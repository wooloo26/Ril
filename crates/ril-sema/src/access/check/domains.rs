use std::collections::{BTreeMap, BTreeSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::{hir::DefinitionId, syntax::Mode};

use super::{
    Analysis, Analyzer, Callable, Context, Datum, DefinitionCheck, Fact, Input, Instance,
    Obligation, Region, SchemaRequirement, extend_rows, member_axes,
};
use crate::access::flow::{Choices, ForwardedMode, ViaConflict, compatible};

pub(super) struct ModeConflict {
    pub owner: Span,
    pub conditions: Vec<(Fact, bool)>,
    pub via: ViaConflict,
    pub span: Span,
    pub message: &'static str,
}

enum Selector {
    Fixed(Input),
    Forwarded(Option<ForwardedMode>),
    Member(Region),
}

struct Offer {
    selector: Selector,
    branches: Choices,
    owner: Option<Span>,
}

pub(super) struct Application {
    owner: Span,
    target: Span,
    site: Span,
    offers: Vec<Vec<Offer>>,
}

type Row = Vec<Input>;

struct Domain {
    axes: Vec<Region>,
    initial: Option<BTreeSet<Row>>,
    allowed: BTreeSet<Row>,
    export: Option<DefinitionId>,
}

impl Domain {
    fn local(axes: Vec<Region>, rows: BTreeSet<Row>, export: Option<DefinitionId>) -> Self {
        Self {
            axes,
            initial: Some(rows.clone()),
            allowed: rows,
            export,
        }
    }

    fn input(&self, row: &Row, axis: &Region) -> Option<Input> {
        self.axes
            .iter()
            .zip(row)
            .find_map(|(known, &input)| known.matches_axis(axis).then_some(input))
    }
}

#[derive(Default)]
pub(super) struct Domains {
    tables: BTreeMap<Span, Domain>,
}

impl Domains {
    pub(super) fn register_function(&mut self, function: &DefinitionCheck, instances: &[Instance]) {
        let axes = axes(&function.declared, &function.formals);
        let rows = instances.iter().map(|row| row.modes.clone()).collect();
        self.tables.insert(
            function.owner,
            Domain::local(
                axes.into_iter().map(|(_, region)| region).collect(),
                rows,
                Some(function.id),
            ),
        );
    }

    fn exclusions(&self, application: &Application, mut reject: impl FnMut(Option<&Row>)) {
        let Some(target) = self.tables.get(&application.target) else {
            return;
        };
        if target
            .initial
            .as_ref()
            .is_some_and(|rows| rows.len() == target.allowed.len())
        {
            return;
        }
        if let Some(owner) = self.tables.get(&application.owner) {
            for row in &owner.allowed {
                if application.excludes(target, |axis| owner.input(row, axis)) {
                    reject(Some(row));
                }
            }
        } else if application.excludes(target, |_| None) {
            reject(None);
        }
    }
}

fn axes(callable: &Callable, formals: &[Option<Span>]) -> Vec<(usize, Region)> {
    callable
        .parameters
        .iter()
        .zip(formals)
        .enumerate()
        .filter_map(|(index, (parameter, formal))| {
            formal
                .filter(|_| parameter.mode == Mode::Via)
                .map(|span| (index, Region::root(span)))
        })
        .chain(member_axes(callable, formals))
        .collect()
}

impl Application {
    fn excludes(&self, target: &Domain, input: impl Fn(&Region) -> Option<Input>) -> bool {
        let mut patterns = vec![(Vec::new(), Choices::new())];
        for offers in &self.offers {
            let mut next = Vec::new();
            for (pattern, branches) in patterns {
                for offer in offers {
                    if !compatible(&branches, &offer.branches) {
                        continue;
                    }
                    let mut pattern = pattern.clone();
                    let mut branches = branches.clone();
                    branches.extend(offer.branches.iter().map(|(&key, &value)| (key, value)));
                    pattern.push(match &offer.selector {
                        Selector::Fixed(input) => Some(*input),
                        Selector::Forwarded(mode) => {
                            mode.as_ref().and_then(|mode| mode.select(&input))
                        }
                        Selector::Member(axis) => input(axis),
                    });
                    next.push((pattern, branches));
                }
            }
            patterns = next;
        }
        patterns.into_iter().any(|(pattern, _)| {
            let matches = |row: &Row| {
                row.len() == pattern.len()
                    && row
                        .iter()
                        .zip(&pattern)
                        .all(|(mode, expect)| expect.is_none_or(|expected| *mode == expected))
            };
            // Existing unary checks report incompatible individual inputs.
            target
                .initial
                .as_ref()
                .is_none_or(|rows| rows.iter().any(matches))
                && !target.allowed.iter().any(matches)
        })
    }
}

impl Analyzer<'_> {
    pub(super) fn record_mode_application(
        &mut self,
        ctx: &Context,
        (target, formals): (Span, &[Option<Span>]),
        signature: &Callable,
        (values, spans): (&[(usize, Mode, Datum)], &[Span]),
        site: Span,
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        let axes = axes(signature, formals);
        if axes.is_empty() {
            return;
        }
        let offers: Option<Vec<Vec<Offer>>> = axes
            .into_iter()
            .map(|(index, axis)| {
                let ((_, actual, value), &span) = values
                    .iter()
                    .zip(spans)
                    .find(|((position, ..), _)| *position == index)?;
                let mode = if axis.selection.is_empty() {
                    *actual
                } else {
                    let mut ty = self.ty(span);
                    let mut mode = Mode::Plain;
                    for coordinate in &axis.selection {
                        let member = self.schema_member(ty, coordinate)?;
                        ty = &member.ty;
                        mode = member.mode.mode;
                    }
                    mode
                };
                if let Some(input) = Input::from_mode(mode) {
                    return Some(vec![Offer {
                        selector: Selector::Fixed(input),
                        branches: Choices::new(),
                        owner: None,
                    }]);
                }
                let matching = value
                    .roots
                    .iter()
                    .map(|root| {
                        let selector = if axis.selection.is_empty() {
                            Selector::Forwarded(root.forwarded_mode())
                        } else {
                            let mut region = root.region.clone();
                            region.selection.extend_from_slice(&axis.selection);
                            Selector::Member(region)
                        };
                        Offer {
                            selector,
                            branches: root.branches.clone(),
                            owner: root.entry_callable(),
                        }
                    })
                    .collect();
                Some(matching)
            })
            .collect::<Option<_>>();
        if let Some(offers) = offers {
            let mut owners = offers.iter().flatten().filter_map(|offer| offer.owner);
            let owner = owners
                .next()
                .filter(|first| owners.all(|owner| owner == *first));
            self.mode_applications.push(Application {
                owner: owner.unwrap_or(ctx.owner),
                target,
                site,
                offers,
            });
        }
    }

    pub(super) fn restrict_mode_domains(
        &mut self,
        facts: &BTreeSet<Fact>,
        domains: &mut Domains,
        analysis: &mut Analysis,
    ) {
        for (&id, export) in &self.program.imported_functions {
            if export.domain.is_empty() {
                continue;
            }
            if let Some(function) = self.function_syntax(id)
                && let Some(signature) = self.program.callables.get(&id)
            {
                let formals: Vec<_> = function
                    .signature
                    .params
                    .iter()
                    .map(|parameter| parameter.name.as_ref().map(|name| name.span))
                    .collect();
                domains.tables.insert(
                    function.name.span,
                    Domain {
                        axes: axes(signature, &formals)
                            .into_iter()
                            .map(|(_, region)| region)
                            .collect(),
                        initial: None,
                        allowed: export.domain.iter().map(|row| row.modes.clone()).collect(),
                        export: None,
                    },
                );
            }
        }
        self.register_closure_domains(facts, domains);
        for conflict in std::mem::take(&mut self.mode_conflicts) {
            if !conflict
                .conditions
                .iter()
                .all(|(fact, expected)| facts.contains(fact) == *expected)
            {
                continue;
            }
            let bad = if let Some(domain) = domains.tables.get_mut(&conflict.owner) {
                let rejected: Vec<_> = domain
                    .allowed
                    .iter()
                    .filter_map(|row| {
                        conflict
                            .via
                            .classify(|axis| domain.input(row, axis))
                            .map(|kind| (row.clone(), kind))
                    })
                    .collect();
                for (row, _) in &rejected {
                    domain.allowed.remove(row);
                }
                domain
                    .allowed
                    .is_empty()
                    .then(|| rejected.first().map(|(_, kind)| *kind))
                    .flatten()
            } else {
                conflict.via.classify(|_| None)
            };
            if let Some(writable) = bad {
                let code = if writable { Code::E0523 } else { Code::E0524 };
                self.error(code, conflict.span, conflict.message);
            }
        }
        let applications = std::mem::take(&mut self.mode_applications);
        // Forwarding may remove rows at earlier call sites or across recursion.
        loop {
            let mut removed = BTreeMap::<_, BTreeMap<Row, Span>>::new();
            for application in &applications {
                domains.exclusions(application, |row| {
                    if let Some(row) = row {
                        removed
                            .entry(application.owner)
                            .or_default()
                            .insert(row.clone(), application.site);
                    } else {
                        self.error(
                            Code::E0520,
                            application.site,
                            "via application requires a compatible combination of access modes",
                        );
                    }
                });
            }
            if removed.is_empty() {
                break;
            }
            for (owner, rows) in removed {
                if let Some(domain) = domains.tables.get_mut(&owner) {
                    for (row, site) in rows {
                        domain.allowed.remove(&row);
                        if domain.allowed.is_empty() {
                            self.error(
                                Code::E0520,
                                site,
                                "via application requires a compatible combination of access modes",
                            );
                        }
                    }
                }
            }
        }
        for domain in domains.tables.values() {
            if let Some(id) = domain.export
                && let Some(instances) = analysis.via.get_mut(&id)
            {
                instances.retain(|row| domain.allowed.contains(&row.modes));
            }
        }
    }

    fn register_closure_domains(&self, facts: &BTreeSet<Fact>, domains: &mut Domains) {
        for (&owner, closure) in &self.closure_modes {
            let mut rows = vec![Vec::new()];
            let mut axes = Vec::new();
            for &formal in closure
                .formals
                .iter()
                .flatten()
                .filter(|formal| closure.via.contains(formal))
            {
                let allowed = root_modes(facts, owner, formal);
                axes.push(Region::root(formal));
                extend_rows(&mut rows, allowed);
            }
            for (_, axis) in &closure.member_axes {
                axes.push(axis.clone());
                let allowed = member_modes(facts, owner, axis);
                extend_rows(&mut rows, &allowed);
            }
            if !axes.is_empty() {
                domains
                    .tables
                    .insert(owner, Domain::local(axes, rows.into_iter().collect(), None));
            }
        }
    }
}

pub(super) fn root_modes(facts: &BTreeSet<Fact>, owner: Span, formal: Span) -> &'static [Input] {
    let exercised = |obligation| facts.contains(&Fact { owner, obligation });
    let needs_sharing = [
        Obligation::Share(formal),
        Obligation::StoreShare(formal),
        Obligation::NeedsSharing(formal),
    ]
    .into_iter()
    .any(exercised);
    if exercised(Obligation::Handoff(formal)) {
        if needs_sharing { &[] } else { &[Input::New] }
    } else if needs_sharing {
        &[Input::Shared]
    } else if exercised(Obligation::Write(formal)) || exercised(Obligation::WriteExisting(formal)) {
        &[Input::Mut, Input::Shared, Input::New]
    } else {
        &[
            Input::Plain,
            Input::Ref,
            Input::Mut,
            Input::Shared,
            Input::New,
        ]
    }
}

pub(super) fn member_modes(facts: &BTreeSet<Fact>, owner: Span, axis: &Region) -> Vec<Input> {
    let required: Vec<_> = [
        SchemaRequirement::Writable,
        SchemaRequirement::Exclusive,
        SchemaRequirement::Shared,
    ]
    .into_iter()
    .filter(|&requirement| {
        facts.contains(&Fact {
            owner,
            obligation: Obligation::Schema(axis.clone(), requirement),
        })
    })
    .collect();
    [Input::Plain, Input::Ref, Input::Mut, Input::Shared]
        .into_iter()
        .filter(|mode| {
            required
                .iter()
                .all(|required| required.accepts(mode.access()))
        })
        .collect()
}
