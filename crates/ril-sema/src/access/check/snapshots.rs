use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{Analyzer, Code, Context, Coordinate, Datum, Ledger, Mode, Origin, Span};
use crate::access::SnapshotInput;

type Formal = (Span, Span);
type Path = Vec<Coordinate>;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Requirement {
    path: Path,
    replaced: Vec<Path>,
}

struct Argument {
    value: Datum,
    span: Span,
}

struct Call {
    entry: Ledger,
    arguments: BTreeMap<Formal, Argument>,
}

#[derive(Default)]
pub(super) struct Checks {
    requirements: BTreeMap<Formal, BTreeSet<Requirement>>,
    calls: Vec<Call>,
}

impl Requirement {
    fn from_origin(
        ledger: &Ledger,
        origin: &Origin,
        owned: bool,
        replaced: &[Path],
    ) -> Option<(Formal, Self)> {
        let owner = origin.transferred_entry(owned)?;
        let mut replaced = [ledger.overwritten_paths(&origin.region), replaced.to_vec()].concat();
        replaced.sort();
        let mut previous = Vec::<Path>::new();
        for path in replaced {
            if !previous.iter().any(|outer| path.starts_with(outer)) {
                previous.push(path);
            }
        }
        Some((
            (owner, origin.region.source),
            Self {
                path: origin.region.selection.clone(),
                replaced: previous,
            },
        ))
    }

    fn input(&self, formal: usize) -> SnapshotInput {
        SnapshotInput {
            formal,
            path: self.path.clone(),
            replaced: self.replaced.clone(),
        }
    }
}

impl Checks {
    pub(super) fn freeze(&mut self, ledger: &Ledger, value: &Datum) {
        value.snapshot_graph(&[], &mut |origin, owned, replaced| {
            if let Some((formal, requirement)) =
                Requirement::from_origin(ledger, origin, owned, replaced)
            {
                self.requirements
                    .entry(formal)
                    .or_default()
                    .insert(requirement);
            }
            true
        });
    }

    pub(super) fn import(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        inputs: &[SnapshotInput],
    ) {
        for input in inputs {
            if let Some(formal) = formals.get(input.formal).copied().flatten() {
                self.requirements
                    .entry((owner, formal))
                    .or_default()
                    .insert(Requirement {
                        path: input.path.clone(),
                        replaced: input.replaced.clone(),
                    });
            }
        }
    }

    pub(super) fn inputs(&self, owner: Span, formals: &[Option<Span>]) -> Vec<SnapshotInput> {
        formals
            .iter()
            .enumerate()
            .flat_map(|(index, formal)| {
                formal
                    .iter()
                    .filter_map(move |&formal| self.requirements.get(&(owner, formal)))
                    .flatten()
                    .map(move |requirement| requirement.input(index))
            })
            .collect()
    }
}

impl Analyzer<'_> {
    pub(super) fn record_snapshot_call(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        owner: Span,
        formals: &[Option<Span>],
        (values, spans): (&[(usize, Mode, Datum)], &[Span]),
    ) {
        if !ctx.reachable || ctx.shadow || !ctx.runtime {
            return;
        }
        let arguments: BTreeMap<_, _> = values
            .iter()
            .zip(spans)
            .filter_map(|((index, mode, value), &span)| {
                let formal = formals.get(*index).copied().flatten()?;
                if !matches!(mode, Mode::New | Mode::Via) || value.roots.is_empty() {
                    return None;
                }
                let mut value = value.clone();
                if *mode == Mode::Via {
                    // A freeze of a transferred via input is reachable only in a
                    // specialization that hands off ownership at this boundary.
                    value.detach_handed_off_paths();
                }
                Some(((owner, formal), Argument { value, span }))
            })
            .collect();
        if !arguments.is_empty() {
            self.snapshots.calls.push(Call {
                entry: ledger.clone(),
                arguments,
            });
        }
    }

    pub(super) fn check_snapshot_calls(&mut self) {
        let calls = std::mem::take(&mut self.snapshots.calls);
        let mut callers = BTreeMap::<_, Vec<_>>::new();
        for call in &calls {
            for (formal, argument) in &call.arguments {
                callers
                    .entry(*formal)
                    .or_default()
                    .push((&call.entry, argument));
            }
        }
        let mut pending = VecDeque::new();
        for (formal, requirements) in &self.snapshots.requirements {
            for requirement in requirements {
                pending.push_back((*formal, requirement.clone(), BTreeMap::new()));
            }
        }
        while let Some((formal, requirement, mut visited)) = pending.pop_front() {
            visited.insert(formal, requirement.path.clone());
            for &(ledger, argument) in callers.get(&formal).into_iter().flatten() {
                let mut selected = argument.value.clone();
                let mut ty = self.ty(argument.span);
                for coordinate in &requirement.path {
                    let member = self.schema_member(ty, coordinate);
                    selected = ledger.project_schema(
                        &selected,
                        coordinate.clone(),
                        member.map_or(Mode::Mut, |member| member.mode.mode),
                    );
                    ty = member.map_or(&crate::ty::Ty::Unknown, |member| &member.ty);
                }
                let selected = ledger.snapshot(&selected);
                let valid = selected.snapshot_graph(
                    &requirement.replaced,
                    &mut |origin, owned, replaced| {
                        if let Some((caller, mut propagated)) =
                            Requirement::from_origin(ledger, origin, owned, replaced)
                        {
                            if let Some(prior) = visited.get(&caller)
                                && propagated.path.len() > prior.len()
                            {
                                // A recursive projection can add unbounded steps.
                                // Require the shared ancestor to be freezable.
                                let prefix = prior
                                    .iter()
                                    .zip(&propagated.path)
                                    .take_while(|(a, b)| a == b)
                                    .count();
                                propagated.path.truncate(prefix);
                                propagated.replaced.clear();
                            }
                            let requirements =
                                self.snapshots.requirements.entry(caller).or_default();
                            if !requirements
                                .iter()
                                .any(|old| old.input(0).permits(&propagated.input(0)))
                            {
                                pending.push_back((caller, propagated.clone(), visited.clone()));
                                requirements
                                    .retain(|old| !propagated.input(0).permits(&old.input(0)));
                                requirements.insert(propagated);
                            }
                        }
                        origin.can_freeze(owned)
                    },
                );
                if !valid {
                    self.error(
                        Code::E0535,
                        argument.span,
                        "snapshot requires a transferred graph without retained live authority",
                    );
                }
            }
        }
    }
}
