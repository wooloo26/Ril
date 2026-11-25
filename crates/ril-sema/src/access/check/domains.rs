use std::collections::{BTreeMap, BTreeSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::{hir::DefinitionId, syntax::Mode};

use super::{
    Analysis, Analyzer, Callable, Context, Datum, DefinitionCheck, Fact, Input, Obligation, Region,
    SchemaRequirement, Summary, ViaDomain, collect_axes,
};
use crate::access::{
    ModeAxis, ModeExpression,
    flow::{Choices, ViaConflict, compatible},
};

pub(super) struct ModeConstraint {
    pub owner: Span,
    pub conditions: Vec<(Fact, bool)>,
    pub test: ModeTest,
    pub span: Span,
    pub message: &'static str,
}

pub(super) enum ModeTest {
    Overlap(Box<ViaConflict>),
    Immutable(BTreeSet<Expression>, Code),
}

impl ModeTest {
    fn violation(&self, input: impl Fn(&Region) -> Option<Input>) -> Option<Code> {
        match self {
            Self::Overlap(overlap) => overlap
                .classify(input)
                .map(|writable| if writable { Code::E0523 } else { Code::E0524 }),
            Self::Immutable(expressions, code) => expressions
                .iter()
                .any(|expression| expression.select(&input) != Some(Input::Plain))
                .then_some(*code),
        }
    }
}

pub(super) type Expression = ModeExpression<Region>;

pub(super) struct Offer {
    expression: Expression,
    branches: Choices,
    owner: Option<Span>,
}

impl Offer {
    fn fixed(expression: Expression) -> Self {
        Self {
            expression,
            branches: Choices::new(),
            owner: None,
        }
    }
}

pub(super) type Arguments = BTreeMap<ModeAxis, Expression>;

pub(super) struct Application {
    pub owner: Span,
    pub target: Span,
    pub site: Span,
    pub arguments: Arguments,
}

/// Only combine alternatives that can originate from the same branch.
pub(super) fn mode_patterns<'a, K: Clone + Ord>(
    offers: impl IntoIterator<Item = (K, &'a [Offer])>,
    branches: &Choices,
) -> Vec<BTreeMap<K, Expression>> {
    let mut patterns = vec![(BTreeMap::new(), branches.clone())];
    for (axis, offers) in offers {
        if offers.is_empty() {
            for (pattern, _) in &mut patterns {
                pattern.insert(axis.clone(), ModeExpression::Unknown);
            }
            continue;
        }
        let mut next = Vec::new();
        for (pattern, branches) in patterns {
            for offer in offers {
                if compatible(&branches, &offer.branches) {
                    let mut pattern = pattern.clone();
                    let mut branches = branches.clone();
                    branches.extend(offer.branches.iter().map(|(&key, &value)| (key, value)));
                    pattern.insert(axis.clone(), offer.expression.clone());
                    next.push((pattern, branches));
                }
            }
        }
        patterns = next;
    }
    patterns.into_iter().map(|(pattern, _)| pattern).collect()
}

type Row = Vec<Input>;

struct Domain {
    axes: Vec<(ModeAxis, Region)>,
    modes: ViaDomain,
    local: bool,
    rejected: BTreeSet<Row>,
    export: Option<DefinitionId>,
}

impl Domain {
    fn local(
        axes: Vec<(ModeAxis, Region)>,
        modes: ViaDomain,
        export: Option<DefinitionId>,
    ) -> Self {
        Self {
            axes,
            modes,
            local: true,
            rejected: BTreeSet::new(),
            export,
        }
    }

    fn allowed(&self) -> impl Iterator<Item = Row> + '_ {
        self.modes
            .iter()
            .map(|row| row.modes)
            .filter(|row| !self.rejected.contains(row))
    }

    fn is_empty(&self) -> bool {
        self.modes.len() == self.rejected.len()
    }

    fn input(&self, row: &Row, axis: &Region) -> Option<Input> {
        self.axes
            .iter()
            .zip(row)
            .find_map(|(known, &input)| known.1.matches_axis(axis).then_some(input))
    }
}

#[derive(Default)]
pub(super) struct Domains {
    tables: BTreeMap<Span, Domain>,
}

impl Domains {
    pub(super) fn register_function(&mut self, function: &DefinitionCheck, instances: &ViaDomain) {
        let axes = axes(&function.declared, &function.formals);
        self.tables.insert(
            function.owner,
            Domain::local(axes, instances.clone(), Some(function.id)),
        );
    }

    fn exclusions(&self, application: &Application, mut reject: impl FnMut(Option<&Row>)) {
        let Some(target) = self.tables.get(&application.target) else {
            return;
        };
        if target.local && target.rejected.is_empty() {
            return;
        }
        if let Some(owner) = self.tables.get(&application.owner) {
            for row in owner.allowed() {
                if application.excludes(target, |axis| owner.input(&row, axis)) {
                    reject(Some(&row));
                }
            }
        } else if application.excludes(target, |_| None) {
            reject(None);
        }
    }
}

pub(super) fn mode_axes(callable: &Callable) -> Vec<ModeAxis> {
    let mut axes: Vec<_> = callable
        .parameters
        .iter()
        .enumerate()
        .filter(|(_, param)| param.callable_mode() == Mode::Via)
        .map(|(parameter, _)| ModeAxis {
            parameter,
            path: Vec::new(),
        })
        .collect();
    for (parameter, param) in callable.parameters.iter().enumerate() {
        collect_axes(&param.ty, &mut Vec::new(), &mut |path| {
            axes.push(ModeAxis {
                parameter,
                path: path.to_vec(),
            });
        });
    }
    axes
}

pub(super) fn axis_region(axis: &ModeAxis, formals: &[Option<Span>]) -> Option<Region> {
    let source = formals.get(axis.parameter).copied().flatten()?;
    let mut region = Region::root(source);
    region.selection.clone_from(&axis.path);
    Some(region)
}

pub(super) fn axes(callable: &Callable, formals: &[Option<Span>]) -> Vec<(ModeAxis, Region)> {
    mode_axes(callable)
        .into_iter()
        .filter_map(|axis| {
            let region = axis_region(&axis, formals)?;
            Some((axis, region))
        })
        .collect()
}

impl Application {
    fn excludes(&self, target: &Domain, input: impl Fn(&Region) -> Option<Input>) -> bool {
        let pattern: Vec<_> = target
            .axes
            .iter()
            .map(|(axis, _)| {
                self.arguments
                    .get(axis)
                    .and_then(|mode| mode.select(&input))
            })
            .collect();
        let matches = |row: &Row| {
            row.len() == pattern.len()
                && row
                    .iter()
                    .zip(&pattern)
                    .all(|(mode, expect)| expect.is_none_or(|expected| *mode == expected))
        };
        if target.local {
            // Existing unary checks report incompatible individual inputs.
            target.rejected.iter().any(matches)
        } else {
            // Published rows include the original unary restrictions. If
            // some modes cannot be resolved, check their combinations using
            // the published marginal domains.
            let allowed = target.modes.count_matching(&pattern)
                - target.rejected.iter().filter(|row| matches(row)).count();
            let count = pattern
                .iter()
                .enumerate()
                .fold(1usize, |size, (position, mode)| {
                    let choices = if mode.is_some() {
                        1
                    } else if target.rejected.is_empty() {
                        target.modes.marginal_len(position)
                    } else {
                        target
                            .allowed()
                            .filter_map(|row| row.get(position).copied())
                            .collect::<BTreeSet<_>>()
                            .len()
                    };
                    size.saturating_mul(choices)
                });
            allowed == 0 || allowed < count
        }
    }
}

impl Analyzer<'_> {
    pub(super) fn mode_offers(
        &self,
        axes: impl IntoIterator<Item = ModeAxis>,
        (values, spans): (&[(usize, Mode, Datum)], &[Span]),
    ) -> BTreeMap<ModeAxis, Vec<Offer>> {
        axes.into_iter()
            .map(|axis| {
                let offers = self
                    .offers_for_axis(&axis, values, spans)
                    .unwrap_or_default();
                (axis, offers)
            })
            .collect()
    }

    fn offers_for_axis(
        &self,
        axis: &ModeAxis,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
    ) -> Option<Vec<Offer>> {
        let ((_, actual, value), &span) = values
            .iter()
            .zip(spans)
            .find(|((position, ..), _)| *position == axis.parameter)?;
        let mode = if axis.path.is_empty() {
            *actual
        } else {
            let mut ty = self.ty(span);
            let mut mode = Mode::Plain;
            for coordinate in &axis.path {
                let member = self.schema_member(ty, coordinate)?;
                ty = &member.ty;
                mode = member.mode.mode;
            }
            mode
        };
        if let Some(input) = Input::from_mode(mode) {
            return Some(vec![Offer::fixed(ModeExpression::Input(input))]);
        }
        Some(
            value
                .roots
                .iter()
                .map(|root| {
                    let expression = if axis.path.is_empty() {
                        root.forwarded_mode().unwrap_or(ModeExpression::Unknown)
                    } else {
                        let mut region = root.region.clone();
                        region.selection.extend_from_slice(&axis.path);
                        ModeExpression::Axis(region)
                    };
                    Offer {
                        expression,
                        branches: root.branches.clone(),
                        owner: root.entry_callable(),
                    }
                })
                .collect(),
        )
    }

    pub(super) fn record_mode_application(
        &mut self,
        ctx: &Context,
        (target, formals): (Span, &[Option<Span>]),
        signature: &Callable,
        values: (&[(usize, Mode, Datum)], &[Span]),
        site: Span,
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        let offers = self.mode_offers(
            mode_axes(signature)
                .into_iter()
                .filter(|axis| axis_region(axis, formals).is_some()),
            values,
        );
        if offers.is_empty() {
            return;
        }
        let mut owners = offers.values().flatten().filter_map(|offer| offer.owner);
        let owner = owners
            .next()
            .filter(|first| owners.all(|other| *first == other))
            .unwrap_or(ctx.owner);
        let patterns = mode_patterns(
            offers
                .iter()
                .map(|(axis, offers)| (axis.clone(), offers.as_slice())),
            &Choices::new(),
        );
        self.mode_applications
            .extend(patterns.into_iter().map(|arguments| Application {
                owner,
                target,
                site,
                arguments,
            }));
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
                        axes: axes(signature, &formals),
                        modes: export.domain.clone(),
                        local: false,
                        rejected: BTreeSet::new(),
                        export: None,
                    },
                );
            }
        }
        self.register_closure_domains(facts, domains);
        for constraint in std::mem::take(&mut self.mode_constraints) {
            if !constraint
                .conditions
                .iter()
                .all(|(fact, expected)| facts.contains(fact) == *expected)
            {
                continue;
            }
            let bad = if let Some(domain) = domains.tables.get_mut(&constraint.owner) {
                let rejected: Vec<_> = domain
                    .allowed()
                    .filter_map(|row| {
                        constraint
                            .test
                            .violation(|axis| domain.input(&row, axis))
                            .map(|code| (row, code))
                    })
                    .collect();
                for (row, _) in &rejected {
                    domain.rejected.insert(row.clone());
                }
                domain
                    .is_empty()
                    .then(|| rejected.first().map(|(_, kind)| *kind))
                    .flatten()
            } else {
                constraint.test.violation(|_| None)
            };
            if let Some(code) = bad {
                self.error(code, constraint.span, constraint.message);
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
                        domain.rejected.insert(row);
                        if domain.is_empty() {
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
                && !domain.rejected.is_empty()
            {
                instances.exclude(&domain.rejected);
            }
        }
    }

    fn register_closure_domains(&self, facts: &BTreeSet<Fact>, domains: &mut Domains) {
        for (&owner, closure) in &self.closure_modes {
            let mut permitted = Vec::new();
            let mut axes = Vec::new();
            for (parameter, formal) in closure.formals.iter().enumerate() {
                let Some(formal) = formal.filter(|formal| closure.via.contains(formal)) else {
                    continue;
                };
                let allowed = root_modes(facts, owner, formal);
                axes.push((
                    ModeAxis {
                        parameter,
                        path: Vec::new(),
                    },
                    Region::root(formal),
                ));
                permitted.push(allowed.to_vec());
            }
            for (parameter, axis) in &closure.member_axes {
                axes.push((
                    ModeAxis {
                        parameter: *parameter,
                        path: axis.selection.clone(),
                    },
                    axis.clone(),
                ));
                permitted.push(member_modes(facts, owner, axis));
            }
            if !axes.is_empty() {
                let modes = ViaDomain::uniform(&permitted, &Summary::default());
                domains
                    .tables
                    .insert(owner, Domain::local(axes, modes, None));
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
        &Input::ALL
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
