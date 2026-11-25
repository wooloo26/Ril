use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::{Input, Summary, ViaRow};

#[derive(Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct Graph {
    pub(super) summaries: Vec<Summary>,
    // The root is last and every edge points to an earlier node.
    pub(super) nodes: Vec<Node>,
    #[serde(skip)]
    pub(super) counts: Vec<u128>,
    #[serde(skip)]
    pub(super) widths: Vec<usize>,
    #[serde(skip)]
    pub(super) width: usize,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub(super) enum Node {
    Leaf(usize),
    Branch(Vec<(Input, usize)>),
}

impl Graph {
    pub(super) fn validate(&mut self) -> Result<(), &'static str> {
        self.widths.clear();
        self.counts.clear();
        if self.nodes.is_empty() && self.summaries.is_empty() {
            self.width = 0;
            return Ok(());
        }
        for (index, node) in self.nodes.iter().enumerate() {
            let (width, count) = match node {
                Node::Leaf(summary) if *summary < self.summaries.len() => (0, 1_u128),
                Node::Leaf(_) => return Err("invalid via summary reference"),
                Node::Branch(edges) => {
                    if edges.is_empty()
                        || !edges
                            .windows(2)
                            .all(|pair| matches!(pair, [(left, _), (right, _)] if left < right))
                    {
                        return Err("invalid via branch modes");
                    }
                    let mut width = None;
                    let mut count = 0_u128;
                    for &(_, child) in edges {
                        if child >= index {
                            return Err("invalid via branch reference");
                        }
                        let child_width = self
                            .widths
                            .get(child)
                            .copied()
                            .ok_or("invalid via branch width")?;
                        if width.is_some_and(|width| width != child_width) {
                            return Err("inconsistent via mode tuple widths");
                        }
                        width = Some(child_width);
                        count = count
                            .saturating_add(self.counts.get(child).copied().unwrap_or_default());
                    }
                    (width.unwrap_or_default() + 1, count)
                }
            };
            self.widths.push(width);
            self.counts.push(count);
        }
        self.width = self
            .widths
            .last()
            .copied()
            .ok_or("missing via graph root")?;
        Ok(())
    }

    pub(super) fn row(&self, mut position: u128) -> Option<ViaRow<'_>> {
        let mut index = self.nodes.len().checked_sub(1)?;
        let mut modes = Vec::with_capacity(self.width);
        loop {
            match self.nodes.get(index)? {
                Node::Leaf(summary) => {
                    return Some(ViaRow {
                        modes,
                        summary: self.summaries.get(*summary)?,
                    });
                }
                Node::Branch(edges) => {
                    let (input, child) = edges.iter().find_map(|&(input, child)| {
                        let count = self.counts.get(child).copied()?;
                        if position < count {
                            Some((input, child))
                        } else {
                            position -= count;
                            None
                        }
                    })?;
                    modes.push(input);
                    index = child;
                }
            }
        }
    }

    pub(super) fn matching(
        &self,
        width: usize,
        mode: impl Fn(usize) -> Option<Input>,
    ) -> Option<&Summary> {
        if width != self.width {
            return None;
        }
        let mut index = self.nodes.len().checked_sub(1)?;
        let mut depth = 0;
        // Concrete calls walk one path without a worklist.
        while let Some(actual) = (depth < width).then(|| mode(depth)).flatten() {
            let Node::Branch(edges) = self.nodes.get(index)? else {
                return None;
            };
            let edge = edges
                .binary_search_by_key(&actual, |&(input, _)| input)
                .ok()?;
            index = edges.get(edge)?.1;
            depth += 1;
        }
        if let Node::Leaf(summary) = self.nodes.get(index)? {
            return self.summaries.get(*summary);
        }
        let mut pending = vec![(index, depth)];
        let mut visited = BTreeSet::new();
        while let Some((index, depth)) = pending.pop() {
            if !visited.insert(index) {
                continue;
            }
            match self.nodes.get(index)? {
                Node::Leaf(summary) => return self.summaries.get(*summary),
                Node::Branch(edges) => {
                    let chosen = mode(depth);
                    pending.extend(edges.iter().rev().filter_map(|&(input, child)| {
                        chosen
                            .is_none_or(|actual| actual == input)
                            .then_some((child, depth + 1))
                    }));
                }
            }
        }
        None
    }

    pub(super) fn modes_at(&self, axis: usize) -> impl Iterator<Item = Input> + '_ {
        Input::ALL.into_iter().filter(move |&mode| {
            axis < self.width
                && self
                    .matching(self.width, |depth| (depth == axis).then_some(mode))
                    .is_some()
        })
    }

    pub(super) fn count_matching_u128(&self, pattern: &[Option<Input>]) -> u128 {
        if pattern.len() != self.width {
            return 0;
        }
        if pattern.iter().all(Option::is_some) {
            return u128::from(
                self.matching(pattern.len(), |depth| pattern.get(depth).copied().flatten())
                    .is_some(),
            );
        }
        let mut counts = Vec::with_capacity(self.nodes.len());
        for (node, &width) in self.nodes.iter().zip(&self.widths) {
            let count = match node {
                Node::Leaf(_) => 1_u128,
                Node::Branch(edges) if width <= pattern.len() => {
                    let expected = pattern.get(pattern.len() - width).copied().flatten();
                    edges
                        .iter()
                        .filter(|(input, _)| expected.is_none_or(|expected| expected == *input))
                        .filter_map(|(_, child)| counts.get(*child).copied())
                        .fold(0_u128, u128::saturating_add)
                }
                Node::Branch(_) => 0_u128,
            };
            counts.push(count);
        }
        counts.last().copied().unwrap_or_default()
    }

    pub(super) fn subsumes(&self, revision: &Self) -> bool {
        let Some(old_root) = self.nodes.len().checked_sub(1) else {
            return true;
        };
        if self.width != revision.width {
            return false;
        }
        let Some(new_root) = revision.nodes.len().checked_sub(1) else {
            return false;
        };
        let mut pending = vec![(old_root, new_root)];
        let mut visited = BTreeSet::new();
        while let Some((old, new)) = pending.pop() {
            if !visited.insert((old, new)) {
                continue;
            }
            match (self.nodes.get(old), revision.nodes.get(new)) {
                (Some(Node::Leaf(old)), Some(Node::Leaf(new)))
                    if self
                        .summaries
                        .get(*old)
                        .zip(revision.summaries.get(*new))
                        .is_some_and(|(old, new)| old.subsumes(new)) => {}
                (Some(Node::Branch(old)), Some(Node::Branch(new))) => {
                    for &(input, child) in old {
                        let Ok(index) = new.binary_search_by_key(&input, |&(mode, _)| mode) else {
                            return false;
                        };
                        let Some(&(_, revised)) = new.get(index) else {
                            return false;
                        };
                        pending.push((child, revised));
                    }
                }
                _ => return false,
            }
        }
        true
    }
}
