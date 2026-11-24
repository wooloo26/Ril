use std::collections::BTreeMap;

use ril_base::span::Span;
use ril_frontend::syntax::Mode;

use super::{BRANCH_LIMIT, Coordinate, Datum, Region, Replacement};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::access) struct StorageRead {
    pub index: usize,
    pub path: Vec<Coordinate>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::access) enum StorageTarget {
    Entry(Region),
    Observed {
        parent: StorageRead,
        member: Coordinate,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::access) struct DeferredStorageCall {
    pub site: Span,
    pub receiver: Datum,
    pub arguments: Vec<(usize, Mode, Datum)>,
    pub spans: Vec<Span>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::access) enum StorageAction {
    Write(StorageTarget, Replacement),
    Invoke(DeferredStorageCall),
    Read {
        index: usize,
        base: Datum,
        coordinate: Coordinate,
        mode: Mode,
    },
}

/// Ordered transfers to the caller's graph. At a loop backedge or a wide
/// join, use a finite set of actions whose interleavings are replayed weakly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::access) enum StorageFlow {
    Paths(Vec<Vec<StorageAction>>),
    Interleaved(Vec<StorageAction>),
}

impl StorageFlow {
    pub(in crate::access) fn writes(updates: BTreeMap<Region, Replacement>) -> Self {
        Self::Paths(vec![
            updates
                .into_iter()
                .map(|(target, update)| StorageAction::Write(StorageTarget::Entry(target), update))
                .collect(),
        ])
    }

    pub(in crate::access) fn push(&mut self, action: StorageAction) {
        match self {
            Self::Paths(paths) => {
                for path in paths.iter_mut() {
                    path.push(action.clone());
                }
                if paths.iter().any(|path| path.len() > 4 * BRANCH_LIMIT) {
                    self.widen();
                }
            }
            Self::Interleaved(actions) => Self::insert(actions, action),
        }
    }

    pub(in crate::access) fn join(alternatives: impl IntoIterator<Item = Self>) -> Self {
        let mut result = Self::Paths(Vec::new());
        for alternative in alternatives {
            match alternative {
                Self::Paths(paths) => {
                    for path in paths {
                        match &mut result {
                            Self::Paths(merged) if !merged.contains(&path) => merged.push(path),
                            Self::Paths(_) => {}
                            Self::Interleaved(merged) => {
                                for action in path {
                                    Self::insert(merged, action);
                                }
                            }
                        }
                    }
                    if matches!(&result, Self::Paths(paths) if paths.len() > BRANCH_LIMIT) {
                        result.widen();
                    }
                }
                Self::Interleaved(actions) => {
                    result.widen();
                    for action in actions {
                        result.push(action);
                    }
                }
            }
        }
        result
    }

    pub(in crate::access) fn widen(&mut self) {
        if let Self::Paths(paths) = self {
            let mut actions = Vec::new();
            for action in std::mem::take(paths).into_iter().flatten() {
                Self::insert(&mut actions, action);
            }
            *self = Self::Interleaved(actions);
        }
    }

    fn insert(actions: &mut Vec<StorageAction>, mut incoming: StorageAction) {
        match &mut incoming {
            StorageAction::Write(target, update) => {
                update.definite = false;
                if let Some(previous) = actions.iter_mut().find_map(|action| match action {
                    StorageAction::Write(place, previous) if place == target => Some(previous),
                    _ => None,
                }) {
                    previous.value = std::mem::take(&mut previous.value)
                        .joined(std::mem::take(&mut update.value));
                    return;
                }
            }
            StorageAction::Invoke(call) => {
                if let Some(previous) = actions.iter_mut().find_map(|action| match action {
                    StorageAction::Invoke(previous)
                        if previous.site == call.site
                            && previous
                                .arguments
                                .iter()
                                .map(|(index, mode, _)| (index, mode))
                                .eq(call
                                    .arguments
                                    .iter()
                                    .map(|(index, mode, _)| (index, mode))) =>
                    {
                        Some(previous)
                    }
                    _ => None,
                }) {
                    previous.receiver = std::mem::take(&mut previous.receiver)
                        .joined(std::mem::take(&mut call.receiver));
                    for ((_, _, value), (_, _, actual)) in
                        previous.arguments.iter_mut().zip(&mut call.arguments)
                    {
                        *value = std::mem::take(value).joined(std::mem::take(actual));
                    }
                    return;
                }
            }
            StorageAction::Read {
                index,
                base,
                coordinate,
                mode,
            } => {
                if let Some(previous) = actions.iter_mut().find_map(|action| match action {
                    StorageAction::Read {
                        index: other,
                        base,
                        coordinate: selected,
                        mode: access,
                    } if other == index && selected == coordinate && access == mode => Some(base),
                    _ => None,
                }) {
                    *previous = std::mem::take(previous).joined(std::mem::take(base));
                    return;
                }
            }
        }
        actions.push(incoming);
    }

    pub(in crate::access) fn values_mut(&mut self) -> impl Iterator<Item = &mut Datum> {
        let (paths, actions) = match self {
            Self::Paths(paths) => (Some(paths), None),
            Self::Interleaved(actions) => (None, Some(actions)),
        };
        paths
            .into_iter()
            .flatten()
            .flatten()
            .chain(actions.into_iter().flatten())
            .flat_map(|action| {
                let (root, arguments) = match action {
                    StorageAction::Write(_, update) => (&mut update.value, None),
                    StorageAction::Invoke(call) => (&mut call.receiver, Some(&mut call.arguments)),
                    StorageAction::Read { base, .. } => (base, None),
                };
                std::iter::once(root)
                    .chain(arguments.into_iter().flatten().map(|(_, _, value)| value))
            })
    }

    pub(in crate::access) fn values(&self) -> impl Iterator<Item = &Datum> {
        let (paths, actions) = match self {
            Self::Paths(paths) => (Some(paths), None),
            Self::Interleaved(actions) => (None, Some(actions)),
        };
        paths
            .into_iter()
            .flatten()
            .flatten()
            .chain(actions.into_iter().flatten())
            .flat_map(|action| {
                let (root, arguments) = match action {
                    StorageAction::Write(_, update) => (&update.value, None),
                    StorageAction::Invoke(call) => (&call.receiver, Some(&call.arguments)),
                    StorageAction::Read { base, .. } => (base, None),
                };
                std::iter::once(root)
                    .chain(arguments.into_iter().flatten().map(|(_, _, value)| value))
            })
    }
}
