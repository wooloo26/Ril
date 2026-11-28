use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, VecDeque},
};

use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_syntax::syntax::Mode;

use super::{
    Analyzer, Context, Datum, Fact, Input, Ledger, Obligation, Region, Rule,
    domains::{self, Application, Arguments, axis_region, mode_axes, mode_patterns},
};
use crate::{
    access::{
        Access, CallbackModeCall, Coordinate, Invocation as PublishedInvocation, InvocationMode,
        ModeAxis, ModeExpression, Summary,
        flow::{Choices, widen_recursive_projection},
    },
    ty::{Callable, Ty, TypedProgram},
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Offer {
    Input(Input),
    Formal(Span),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Invocation {
    receiver: Span,
    position: usize,
    offer: Offer,
}

struct Argument {
    offers: BTreeSet<Offer>,
    targets: BTreeSet<Span>,
    callback_graph: Option<Datum>,
    dependencies: BTreeSet<Span>,
    existing: BTreeSet<Span>,
    span: Span,
}

impl Argument {
    fn mode_receivers(&self, invocation: &ModeInvocation) -> Vec<(ModeReceiver, Choices)> {
        let Some(graph) = &self.callback_graph else {
            return Vec::new();
        };
        let selected = receiver_path(graph, &invocation.receiver.region.selection);
        let mut receivers = Vec::new();
        match &invocation.receiver.recursive_path {
            Some(path) => nested_mode_receivers(&selected, path, &mut receivers),
            None => collect_mode_receivers(&selected, None, &mut receivers),
        }
        receivers
    }
}

fn receiver_path<'a>(graph: &'a Datum, path: &[Coordinate]) -> Cow<'a, Datum> {
    path.iter().fold(Cow::Borrowed(graph), |base, coordinate| {
        Cow::Owned(base.project(coordinate.clone(), Access::Immutable))
    })
}

fn collect_mode_receivers(
    value: &Datum,
    recursive_path: Option<&[Coordinate]>,
    out: &mut Vec<(ModeReceiver, Choices)>,
) {
    out.extend(value.roots.iter().map(|origin| {
        (
            ModeReceiver {
                region: origin.region.clone(),
                recursive_path: recursive_path.map(<[Coordinate]>::to_vec),
            },
            origin.branches.clone(),
        )
    }));
}

fn nested_mode_receivers(
    value: &Datum,
    path: &[Coordinate],
    out: &mut Vec<(ModeReceiver, Choices)>,
) {
    collect_mode_receivers(value, Some(path), out);
    collect_mode_receivers(&receiver_path(value, path), None, out);
    for member in value.members.values() {
        nested_mode_receivers(member, path, out);
    }
}

struct Call {
    owner: Span,
    arguments: BTreeMap<Span, Argument>,
    modes: BTreeMap<Region, Vec<domains::Offer>>,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct ModeInvocation {
    receiver: ModeReceiver,
    arguments: Arguments,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct ModeReceiver {
    region: Region,
    recursive_path: Option<Vec<Coordinate>>,
}

impl ModeReceiver {
    fn widen_recursive_path(&mut self, previous: &[Coordinate]) {
        widen_recursive_projection(
            &mut self.region.selection,
            previous,
            &mut self.recursive_path,
        );
    }
}

type ReceiverTrail = BTreeMap<Span, Vec<Coordinate>>;

#[derive(Default)]
pub(super) struct Calls {
    calls: BTreeMap<Span, Vec<Call>>,
    interface_formals: BTreeMap<Span, Vec<Option<Span>>>,
    invocations: BTreeSet<(Span, Invocation, Span, Span)>,
    mode_calls: BTreeSet<(Span, ModeInvocation, Span)>,
}

impl Calls {
    pub(super) fn add_interface(
        &mut self,
        owner: Span,
        formals: Vec<Option<Span>>,
        summary: &Summary,
    ) {
        for invocation in &summary.invocations {
            let Some(receiver) = formals.get(invocation.receiver).copied().flatten() else {
                continue;
            };
            let offer = match invocation.mode {
                InvocationMode::Input(input) => Offer::Input(input),
                InvocationMode::Formal(index) => {
                    let Some(source) = formals.get(index).copied().flatten() else {
                        continue;
                    };
                    Offer::Formal(source)
                }
            };
            let at = Invocation {
                receiver,
                position: invocation.parameter,
                offer,
            };
            self.invocations.insert((owner, at, owner, owner));
        }
        for call in summary.offered_mode_calls() {
            if let Some(receiver) = axis_region(&call.receiver, &formals) {
                let arguments = call
                    .arguments
                    .iter()
                    .map(|(axis, expression)| {
                        let expression = expression.substitute(&|axis| {
                            axis_region(axis, &formals)
                                .map_or(ModeExpression::Unknown, ModeExpression::Axis)
                        });
                        (axis.clone(), expression)
                    })
                    .collect();
                self.mode_calls.insert((
                    owner,
                    ModeInvocation {
                        receiver: ModeReceiver {
                            region: receiver,
                            recursive_path: call.recursive_path.clone(),
                        },
                        arguments,
                    },
                    owner,
                ));
            }
        }
        self.interface_formals.insert(owner, formals);
    }
}

impl Offer {
    fn of(mode: Mode, value: &Datum) -> BTreeSet<Self> {
        if mode == Mode::Via {
            return value
                .roots
                .iter()
                .filter(|root| root.inherits_mode)
                .map(|root| Self::Formal(root.region.source))
                .collect();
        }
        BTreeSet::from([Self::Input(Input::from_mode(mode).unwrap_or(Input::Plain))])
    }
}

fn can_supply_mode_callback(program: &TypedProgram, ty: &Ty) -> bool {
    can_supply_callback(
        ty,
        &|signature| !mode_axes(program, signature).is_empty(),
        Some(program),
        &mut BTreeSet::new(),
    )
}

pub(super) fn can_supply_snapshot_callback(program: &TypedProgram, ty: &Ty) -> bool {
    can_supply_callback(
        ty,
        &|signature| {
            signature.parameters.iter().any(|parameter| {
                matches!(
                    program.parameter_callable_mode(parameter),
                    Mode::New | Mode::Via
                ) || can_supply_snapshot_callback(program, &parameter.ty)
            })
        },
        Some(program),
        &mut BTreeSet::new(),
    )
}

pub(super) fn carries_callable(program: &TypedProgram, ty: &Ty) -> bool {
    can_supply_callback(ty, &|_| true, Some(program), &mut BTreeSet::new())
}

fn can_supply_callback(
    ty: &Ty,
    accepts: &dyn Fn(&Callable) -> bool,
    program: Option<&TypedProgram>,
    active: &mut BTreeSet<ril_hir::DefinitionId>,
) -> bool {
    let mut visit = |ty| can_supply_callback(ty, accepts, program, active);
    match ty {
        Ty::Callable(signature) => accepts(signature),
        Ty::Record(fields, open) => *open || fields.values().any(|field| visit(&field.ty)),
        Ty::Tuple(fields) => fields.iter().any(|field| visit(&field.ty)),
        Ty::Array(item) => visit(&item.ty),
        Ty::Map(key, item) => visit(key) || visit(&item.ty),
        Ty::Draft(item) => visit(item),
        Ty::Adt(adt) if let Some(program) = program => {
            if let Some(item) = ty.as_option(&program.hir) {
                return visit(item);
            }
            if let Some((ok, error)) = ty.as_result(&program.hir) {
                return visit(ok) || visit(error);
            }
            if !active.insert(adt.definition) {
                return false;
            }
            let result = program
                .nominal_layout(adt)
                .is_none_or(|layout| can_supply_callback(&layout, accepts, Some(program), active));
            active.remove(&adt.definition);
            result
        }
        Ty::Adt(_) => true,
        Ty::Param(_) | Ty::Infer(_) | Ty::Projection(..) | Ty::Unknown => true,
        _ => false,
    }
}

impl Analyzer<'_> {
    pub(super) fn record_indirect_modes(
        &mut self,
        ctx: &Context,
        target: &Datum,
        signature: &Callable,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
        (site, _ledger): (Span, &mut Ledger),
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        let offers = self.mode_offers(mode_axes(self.program, signature), (values, spans));
        for root in &target.roots {
            let receiver = root.region.source;
            if root.region.selection.is_empty() && self.closure_modes.contains_key(&receiver) {
                continue;
            }
            if !offers.is_empty() {
                for arguments in mode_patterns(
                    offers
                        .iter()
                        .map(|(axis, offers)| (axis.clone(), offers.as_slice())),
                    &root.branches,
                ) {
                    self.higher_order.mode_calls.insert((
                        ctx.owner,
                        ModeInvocation {
                            receiver: ModeReceiver {
                                region: root.region.clone(),
                                recursive_path: None,
                            },
                            arguments,
                        },
                        site,
                    ));
                }
            }
            if !root.region.selection.is_empty() {
                continue;
            }
            for ((position, mode, value), &span) in values.iter().zip(spans) {
                if !signature
                    .parameters
                    .get(*position)
                    .is_some_and(|param| self.program.parameter_callable_mode(param) == Mode::Via)
                {
                    continue;
                }
                for offer in Offer::of(*mode, value) {
                    self.higher_order.invocations.insert((
                        ctx.owner,
                        Invocation {
                            receiver,
                            position: *position,
                            offer,
                        },
                        span,
                        site,
                    ));
                }
            }
        }
    }

    pub(super) fn record_callable_arguments(
        &mut self,
        ctx: &Context,
        (callee, formals): (Span, &[Option<Span>]),
        signature: &Callable,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
        (site, _ledger): (Span, &mut Ledger),
    ) {
        self.record_mode_application(ctx, (callee, formals), signature, (values, spans), site);
        if !ctx.reachable
            || ctx.shadow
            || !signature
                .parameters
                .iter()
                .any(|param| can_supply_mode_callback(self.program, &param.ty))
        {
            return;
        }
        let arguments = values
            .iter()
            .zip(spans)
            .filter_map(|((index, mode, value), &span)| {
                let formal = formals.get(*index).copied().flatten()?;
                let ty = self.ty(span);
                let targets = if matches!(ty, Ty::Callable(_)) {
                    value
                        .roots
                        .iter()
                        .filter(|root| root.region.selection.is_empty())
                        .map(|root| root.region.source)
                        .collect()
                } else {
                    BTreeSet::new()
                };
                let argument = Argument {
                    offers: Offer::of(*mode, value),
                    targets,
                    callback_graph: can_supply_mode_callback(self.program, ty)
                        .then(|| value.clone()),
                    dependencies: value.root_dependencies().collect(),
                    existing: value
                        .roots
                        .iter()
                        .filter(|root| !root.new)
                        .map(|root| root.region.source)
                        .collect(),
                    span,
                };
                Some((formal, argument))
            })
            .collect();
        let modes = self
            .mode_offers(mode_axes(self.program, signature), (values, spans))
            .into_iter()
            .filter_map(|(axis, offers)| Some((axis_region(&axis, formals)?, offers)))
            .collect();
        self.higher_order
            .calls
            .entry(callee)
            .or_default()
            .push(Call {
                owner: ctx.owner,
                arguments,
                modes,
            });
    }

    pub(super) fn link_higher_order_calls(&mut self) {
        let Calls {
            calls,
            interface_formals,
            invocations,
            mode_calls,
        } = std::mem::take(&mut self.higher_order);
        let providers: BTreeMap<_, _> = self
            .functions
            .iter()
            .map(|f| (f.owner, f.formals.clone()))
            .chain(
                self.closure_modes
                    .iter()
                    .map(|(&owner, closure)| (owner, closure.formals.clone())),
            )
            .chain(interface_formals)
            .collect();
        let formal_owners: BTreeMap<_, _> = providers
            .iter()
            .flat_map(|(&owner, formals)| {
                formals.iter().flatten().map(move |&formal| (formal, owner))
            })
            .collect();
        self.link_mode_calls(mode_calls, &providers, &formal_owners, &calls);
        let mut pending = VecDeque::new();
        for (owner, invocation, span, _site) in invocations {
            pending.push_back((owner, invocation, span));
        }
        let mut visited = BTreeSet::new();
        while let Some((owner, invocation, span)) = pending.pop_front() {
            if !visited.insert((owner, invocation, span)) {
                continue;
            }
            if let Some(formals) = providers.get(&owner)
                && let Some(receiver) = formals
                    .iter()
                    .position(|formal| *formal == Some(invocation.receiver))
            {
                let mode = match invocation.offer {
                    Offer::Input(input) => Some(InvocationMode::Input(input)),
                    Offer::Formal(source) => formals
                        .iter()
                        .position(|formal| *formal == Some(source))
                        .map(InvocationMode::Formal),
                };
                if let Some(mode) = mode {
                    self.invocation_summaries.entry(owner).or_default().insert(
                        PublishedInvocation {
                            receiver,
                            parameter: invocation.position,
                            mode,
                            preserves_input: false,
                        },
                    );
                }
            }
            let formal_of = |target| {
                providers
                    .get(&target)
                    .and_then(|params| params.get(invocation.position))
                    .copied()
                    .flatten()
            };
            if let Some(formal) = formal_of(invocation.receiver) {
                self.check_callback_offer(
                    owner,
                    (invocation.receiver, formal),
                    invocation.offer,
                    span,
                    None,
                );
            }
            // Substitute arguments on one edge at a time so a callback at one
            // call site cannot constrain a different instantiation.
            for call in calls.get(&owner).into_iter().flatten() {
                let Some(callback) = call.arguments.get(&invocation.receiver) else {
                    continue;
                };
                let argument = match invocation.offer {
                    Offer::Formal(formal) => call.arguments.get(&formal),
                    Offer::Input(_) => None,
                };
                let offers = argument.map_or_else(
                    || BTreeSet::from([invocation.offer]),
                    |arg| arg.offers.clone(),
                );
                for &target in &callback.targets {
                    for &offer in &offers {
                        let forwarded = Invocation {
                            receiver: target,
                            offer,
                            ..invocation
                        };
                        if let Some(formal) = formal_of(target) {
                            self.check_callback_offer(
                                call.owner,
                                (target, formal),
                                offer,
                                callback.span,
                                argument,
                            );
                        } else if formal_owners.get(&target) == Some(&call.owner) {
                            pending.push_back((call.owner, forwarded, callback.span));
                        }
                    }
                }
            }
        }
    }

    fn link_mode_calls(
        &mut self,
        pending: BTreeSet<(Span, ModeInvocation, Span)>,
        providers: &BTreeMap<Span, Vec<Option<Span>>>,
        formal_owners: &BTreeMap<Span, Span>,
        calls: &BTreeMap<Span, Vec<Call>>,
    ) {
        let published_axes: BTreeMap<_, _> = providers
            .iter()
            .filter_map(|(&owner, formals)| {
                let signature = if let Ty::Callable(signature) = self.ty(owner) {
                    signature
                } else {
                    self.program.callables.get(&self.definition(owner)?)?
                };
                Some((owner, domains::axes(self.program, signature, formals)))
            })
            .collect();
        let mut pending: VecDeque<_> = pending
            .into_iter()
            .map(|(owner, invocation, site)| (owner, invocation, site, ReceiverTrail::default()))
            .collect();
        let mut seen = BTreeSet::new();
        while let Some((call_owner, mut invocation, site, mut trail)) = pending.pop_front() {
            let source = invocation.receiver.region.source;
            let owner = formal_owners.get(&source).copied().unwrap_or(call_owner);
            if let Some(previous) = trail.get(&source) {
                invocation.receiver.widen_recursive_path(previous);
            }
            trail.insert(source, invocation.receiver.region.selection.clone());
            if !seen.insert((owner, invocation.clone(), site)) {
                continue;
            }
            if invocation.receiver.region.selection.is_empty()
                && invocation.receiver.recursive_path.is_none()
                && providers.contains_key(&source)
            {
                self.mode_applications.push(Application {
                    owner,
                    target: source,
                    site,
                    arguments: invocation.arguments,
                });
                continue;
            }
            let Some(receiver) = providers
                .get(&owner)
                .and_then(|formals| formals.iter().position(|formal| *formal == Some(source)))
            else {
                continue;
            };
            let arguments = invocation
                .arguments
                .iter()
                .map(|(axis, mode)| {
                    let mode = mode.substitute(&|source| {
                        published_axes
                            .get(&owner)
                            .into_iter()
                            .flatten()
                            .find(|(_, region)| region.matches_axis(source))
                            .map_or(ModeExpression::Unknown, |(axis, _)| {
                                ModeExpression::Axis(axis.clone())
                            })
                    });
                    (axis.clone(), mode)
                })
                .collect();
            self.mode_call_summaries
                .entry(owner)
                .or_default()
                .insert(CallbackModeCall {
                    receiver: ModeAxis {
                        parameter: receiver,
                        path: invocation.receiver.region.selection.clone(),
                    },
                    recursive_path: invocation.receiver.recursive_path.clone(),
                    arguments,
                });

            let sources: BTreeSet<_> = invocation
                .arguments
                .values()
                .flat_map(ModeExpression::axes)
                .collect();
            for call in calls.get(&owner).into_iter().flatten() {
                let Some(callback) = call.arguments.get(&source) else {
                    continue;
                };
                let offers: Vec<_> = sources
                    .iter()
                    .map(|&source| {
                        let offers = call
                            .modes
                            .iter()
                            .find(|(axis, _)| axis.matches_axis(source))
                            .map_or(&[][..], |(_, offers)| offers.as_slice());
                        (source.clone(), offers)
                    })
                    .collect();
                for (target, branches) in callback.mode_receivers(&invocation) {
                    for bindings in mode_patterns(offers.iter().cloned(), &branches) {
                        let arguments = invocation
                            .arguments
                            .iter()
                            .map(|(axis, mode)| {
                                let translated = mode.substitute(&|source| {
                                    bindings
                                        .get(source)
                                        .cloned()
                                        .unwrap_or(ModeExpression::Unknown)
                                });
                                (axis.clone(), translated)
                            })
                            .collect();
                        pending.push_back((
                            call.owner,
                            ModeInvocation {
                                receiver: target.clone(),
                                arguments,
                            },
                            callback.span,
                            trail.clone(),
                        ));
                    }
                }
            }
        }
    }

    fn check_callback_offer(
        &mut self,
        owner: Span,
        (callee, formal): (Span, Span),
        offer: Offer,
        span: Span,
        argument: Option<&Argument>,
    ) {
        let write = Fact {
            owner: callee,
            obligation: Obligation::Write(formal),
        };
        for (condition, accepts, code, message) in [
            (
                Obligation::Share(formal),
                &[Input::Shared][..],
                Code::E0520,
                "callback requires a shared writable argument",
            ),
            (
                Obligation::StoreShare(formal),
                &[Input::Shared],
                Code::E0520,
                "callback requires a shared writable argument",
            ),
            (
                Obligation::NeedsSharing(formal),
                &[Input::Shared],
                Code::E0520,
                "callback requires a shared writable argument",
            ),
            (
                Obligation::Write(formal),
                &[Input::Mut, Input::Shared, Input::New],
                Code::E0520,
                "callback requires a writable argument",
            ),
        ] {
            let premise = Fact {
                owner: callee,
                obligation: condition.clone(),
            };
            match offer {
                Offer::Input(input) if !accepts.contains(&input) => self
                    .deferred_errors
                    .push((vec![premise], Diagnostic::error(code, span, message))),
                Offer::Formal(source) => {
                    let obligation = match condition {
                        Obligation::Share(_) | Obligation::StoreShare(_) => {
                            Obligation::Share(source)
                        }
                        Obligation::NeedsSharing(_) => Obligation::NeedsSharing(source),
                        _ => Obligation::Write(source),
                    };
                    self.rules.push(Rule {
                        premises: vec![premise],
                        conclusion: Fact { owner, obligation },
                    });
                }
                Offer::Input(_) => {}
            }
        }
        if let Some(argument) = argument
            && !matches!(offer, Offer::Input(Input::Plain | Input::Ref))
        {
            for obligation in argument
                .dependencies
                .iter()
                .copied()
                .map(Obligation::Write)
                .chain(
                    argument
                        .existing
                        .iter()
                        .copied()
                        .map(Obligation::WriteExisting),
                )
            {
                self.rules.push(Rule {
                    premises: vec![write.clone()],
                    conclusion: Fact { owner, obligation },
                });
            }
        }
    }
}
