use std::collections::{BTreeMap, BTreeSet};

use ril_hir::DefinitionId;
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::Mode;

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

    fn support_regions(&self) -> Vec<Region> {
        match self {
            Self::Overlap(overlap) => overlap.support_regions(),
            Self::Immutable(expressions, _) => expressions
                .iter()
                .flat_map(|expr| expr.axes().cloned())
                .collect(),
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

struct Domain {
    axes: Vec<(ModeAxis, Region)>,
    /// Remaining permitted mode tuples stored natively as an MDD DAG.
    current: ViaDomain,
    /// Excluded mode tuples stored natively as an MDD mask DAG.
    excluded: ViaDomain,
    local: bool,
    export: Option<DefinitionId>,
    dirty: bool,
}

impl Domain {
    fn local(
        axes: Vec<(ModeAxis, Region)>,
        modes: ViaDomain,
        export: Option<DefinitionId>,
    ) -> Self {
        Self {
            axes,
            current: modes,
            excluded: ViaDomain::default(),
            local: true,
            export,
            dirty: false,
        }
    }

    fn is_empty(&self) -> bool {
        self.current.is_empty()
    }

    fn support_indices(&self, regions: &[Region]) -> Vec<usize> {
        let mut indices = BTreeSet::new();
        for region in regions {
            for (idx, (_, known)) in self.axes.iter().enumerate() {
                if known.matches_axis(region) {
                    indices.insert(idx);
                }
            }
        }
        indices.into_iter().collect()
    }

    fn lookup_assigned(&self, assigned: &[(usize, Input)], axis: &Region) -> Option<Input> {
        self.axes.iter().enumerate().find_map(|(idx, (_, known))| {
            if !known.matches_axis(axis) {
                return None;
            }
            assigned
                .iter()
                .find_map(|&(pos, input)| (pos == idx).then_some(input))
        })
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
    fn support_regions(&self) -> Vec<Region> {
        self.arguments
            .values()
            .flat_map(|expr| expr.axes().cloned())
            .collect()
    }

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
        if target.local {
            // Existing unary checks report incompatible individual inputs.
            target.excluded.count_matching_u128(&pattern) > 0
        } else {
            // Published rows include the original unary restrictions. If
            // some modes cannot be resolved, check their combinations using
            // the published marginal domains.
            let allowed = target.current.count_matching_u128(&pattern);
            let count = pattern
                .iter()
                .enumerate()
                .fold(1_u128, |size, (position, mode)| {
                    let choices = if mode.is_some() {
                        1_u128
                    } else {
                        target.current.marginal_len(position) as u128
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
                        current: export.domain.clone(),
                        excluded: ViaDomain::default(),
                        local: false,
                        export: None,
                        dirty: false,
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
                let support = domain.support_indices(&constraint.test.support_regions());
                let (kept, removed, first_code) =
                    domain.current.partition_support(&support, |assigned| {
                        constraint
                            .test
                            .violation(|axis| domain.lookup_assigned(assigned, axis))
                    });
                if !removed.is_empty() {
                    domain.current = kept;
                    domain.excluded = domain.excluded.union_mask(&removed);
                    domain.dirty = true;
                }
                domain.is_empty().then_some(first_code).flatten()
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
            let mut changed = false;
            let mut non_via_errors = Vec::new();
            let mut pending: Vec<(Span, ViaDomain, ViaDomain, Span)> = Vec::new();
            for application in &applications {
                let Some(target) = domains.tables.get(&application.target) else {
                    continue;
                };
                if target.local && target.excluded.is_empty() {
                    continue;
                }
                if let Some(owner) = domains.tables.get(&application.owner) {
                    if owner.is_empty() {
                        continue;
                    }
                    let support = owner.support_indices(&application.support_regions());
                    let (kept, removed, rejected_any) =
                        owner.current.partition_support(&support, |assigned| {
                            application
                                .excludes(target, |axis| owner.lookup_assigned(assigned, axis))
                                .then_some(())
                        });
                    if rejected_any.is_some() && !removed.is_empty() {
                        pending.push((application.owner, kept, removed, application.site));
                    }
                } else if application.excludes(target, |_| None) {
                    non_via_errors.push(application.site);
                }
            }
            for site in non_via_errors {
                self.error(
                    Code::E0520,
                    site,
                    "via application requires a compatible combination of access modes",
                );
            }
            if pending.is_empty() {
                break;
            }
            for (owner_span, _kept, removed, site) in pending {
                if let Some(domain) = domains.tables.get_mut(&owner_span) {
                    let was_empty = domain.is_empty();
                    let next_current = domain.current.subtract_mask(&removed);
                    if next_current.len_u128() < domain.current.len_u128() {
                        domain.current = next_current;
                        domain.excluded = domain.excluded.union_mask(&removed);
                        domain.dirty = true;
                        changed = true;
                        if !was_empty && domain.is_empty() {
                            self.error(
                                Code::E0520,
                                site,
                                "via application requires a compatible combination of access modes",
                            );
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for domain in domains.tables.values() {
            if let Some(id) = domain.export
                && domain.dirty
                && let Some(instances) = analysis.via.get_mut(&id)
            {
                *instances = domain.current.clone();
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
