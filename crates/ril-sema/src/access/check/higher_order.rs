use std::collections::{BTreeMap, BTreeSet, VecDeque};

use ril_base::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_frontend::syntax::Mode;

use super::{Analyzer, Context, Datum, Fact, Input, Ledger, Obligation, Revocation, Rule};
use crate::{
    access::{Invocation as PublishedInvocation, InvocationMode},
    ty::{Callable, Ty},
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

impl Invocation {
    fn consumption(self, owner: Span) -> Fact {
        Fact {
            owner,
            obligation: Obligation::CallbackConsumes(self),
        }
    }
}

struct Argument {
    position: usize,
    offers: BTreeSet<Offer>,
    targets: BTreeSet<Span>,
    dependencies: BTreeSet<Span>,
    existing: BTreeSet<Span>,
    span: Span,
}

struct Call {
    owner: Span,
    site: Span,
    arguments: BTreeMap<Span, Argument>,
}

#[derive(Default)]
pub(super) struct Calls {
    calls: BTreeMap<Span, Vec<Call>>,
    interface_formals: BTreeMap<Span, Vec<Option<Span>>>,
    interface_protected: BTreeSet<(Span, Invocation)>,
    invocations: BTreeSet<(Span, Invocation, Span, Span)>,
    protected: BTreeSet<(Span, usize)>,
}

impl Calls {
    pub(super) fn protect_input(&mut self, site: Span, position: usize) {
        self.protected.insert((site, position));
    }

    pub(super) fn add_interface(
        &mut self,
        owner: Span,
        formals: Vec<Option<Span>>,
        invocations: &[PublishedInvocation],
    ) {
        for invocation in invocations {
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
            if invocation.preserves_input {
                self.interface_protected.insert((owner, at));
            }
        }
        self.interface_formals.insert(owner, formals);
    }
}

fn track_handoff(ledger: &mut Ledger, value: &Datum, (site, position): (Span, usize)) {
    for root in value.roots.iter().filter(|root| root.inherits_mode) {
        for &token in &root.dependencies {
            ledger.revoke(
                token,
                Some(root),
                Some(Revocation::Callback { site, position }),
            );
        }
    }
}

fn callback_handoff(site: Span, position: usize) -> Fact {
    Fact {
        owner: site,
        obligation: Obligation::CallbackHandoff(position),
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

impl Analyzer<'_> {
    pub(super) fn record_indirect_modes(
        &mut self,
        ctx: &Context,
        target: &Datum,
        signature: &Callable,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
        (site, ledger): (Span, &mut Ledger),
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        for root in &target.roots {
            let receiver = root.region.source;
            if !root.region.selection.is_empty() || self.closure_modes.contains_key(&receiver) {
                continue;
            }
            for ((position, mode, value), &span) in values.iter().zip(spans) {
                if !signature
                    .parameters
                    .get(*position)
                    .is_some_and(|param| param.callable_mode() == Mode::Via)
                {
                    continue;
                }
                if *mode == Mode::Via {
                    track_handoff(ledger, value, (site, *position));
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
        (site, ledger): (Span, &mut Ledger),
    ) {
        if !ctx.reachable || ctx.shadow || !signature.parameters.iter().any(|param| {
            matches!(&param.ty, Ty::Callable(call) if call.parameters.iter().any(|input| input.callable_mode() == Mode::Via))
        }) {
            return;
        }
        let arguments = values
            .iter()
            .zip(spans)
            .filter_map(|((index, mode, value), &span)| {
                let formal = formals.get(*index).copied().flatten()?;
                let targets = if matches!(self.ty(span), Ty::Callable(_)) {
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
                    position: *index,
                    offers: Offer::of(*mode, value),
                    targets,
                    dependencies: value.root_dependencies().collect(),
                    existing: value
                        .roots
                        .iter()
                        .filter(|root| !root.new)
                        .map(|root| root.region.source)
                        .collect(),
                    span,
                };
                if *mode == Mode::Via {
                    track_handoff(ledger, value, (site, *index));
                }
                Some((formal, argument))
            })
            .collect();
        self.higher_order
            .calls
            .entry(callee)
            .or_default()
            .push(Call {
                owner: ctx.owner,
                site,
                arguments,
            });
    }

    pub(super) fn link_higher_order_calls(&mut self) {
        let Calls {
            calls,
            interface_formals,
            interface_protected,
            invocations,
            protected,
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
        let mut pending = VecDeque::new();
        for (owner, invocation, span, site) in invocations {
            if matches!(invocation.offer, Offer::Formal(_)) {
                self.rules.push(Rule {
                    premises: vec![invocation.consumption(owner)],
                    conclusion: callback_handoff(site, invocation.position),
                });
            }
            let published_preservation = interface_protected.contains(&(owner, invocation));
            pending.push_back((
                owner,
                invocation,
                span,
                published_preservation || protected.contains(&(site, invocation.position)),
                published_preservation,
            ));
        }
        let mut visited = BTreeSet::new();
        while let Some((owner, invocation, span, preserves_input, published_preservation)) =
            pending.pop_front()
        {
            if !visited.insert((
                owner,
                invocation,
                span,
                preserves_input,
                published_preservation,
            )) {
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
                            preserves_input,
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
                if matches!(
                    invocation.offer,
                    Offer::Formal(_) | Offer::Input(Input::New)
                ) {
                    self.rules.push(Rule {
                        premises: vec![Fact {
                            owner: invocation.receiver,
                            obligation: Obligation::Handoff(formal),
                        }],
                        conclusion: invocation.consumption(owner),
                    });
                }
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
                        let consumption = if let Some(formal) = formal_of(target) {
                            Fact {
                                owner: target,
                                obligation: Obligation::Handoff(formal),
                            }
                        } else {
                            forwarded.consumption(call.owner)
                        };
                        if published_preservation && offer == Offer::Input(Input::New) {
                            self.deferred_errors.push((
                                vec![consumption.clone()],
                                Diagnostic::error(
                                    Code::E0549,
                                    callback.span,
                                    "callback consumes an input the published call still uses",
                                ),
                            ));
                        }
                        if matches!(offer, Offer::Formal(_) | Offer::Input(Input::New)) {
                            self.rules.push(Rule {
                                premises: vec![consumption.clone()],
                                conclusion: invocation.consumption(owner),
                            });
                            if let Some(arg) = argument {
                                self.rules.push(Rule {
                                    premises: vec![consumption],
                                    conclusion: callback_handoff(call.site, arg.position),
                                });
                            }
                        }
                        if let Some(formal) = formal_of(target) {
                            self.check_callback_offer(
                                call.owner,
                                (target, formal),
                                offer,
                                callback.span,
                                argument,
                            );
                        } else if formal_owners.get(&target) == Some(&call.owner) {
                            pending.push_back((
                                call.owner,
                                forwarded,
                                callback.span,
                                preserves_input
                                    || argument.is_some_and(|arg| {
                                        protected.contains(&(call.site, arg.position))
                                    }),
                                published_preservation,
                            ));
                        }
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
                Obligation::Handoff(formal),
                &[Input::New][..],
                Code::E0548,
                "callback requires a new argument",
            ),
            (
                Obligation::Share(formal),
                &[Input::Shared],
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
                        Obligation::Handoff(_) => Obligation::Handoff(source),
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
