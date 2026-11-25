use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error as _};

use super::{Input, Instance, Summary};

/// An exact set of mode tuples and their summaries. A branch tests one
/// mode axis. Identical subgraphs and summaries are stored once.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ViaDomain(Arc<Encoding>);

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
enum Encoding {
    Graph(Graph),
    // Older .rili files hash the expanded rows in their original order.
    Rows(Vec<Instance>),
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct Graph {
    summaries: Vec<Summary>,
    // The root is last and every edge points to an earlier node.
    nodes: Vec<Node>,
    #[serde(skip)]
    counts: Vec<usize>,
    #[serde(skip)]
    widths: Vec<usize>,
    #[serde(skip)]
    width: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
enum Node {
    Leaf(usize),
    Branch(Vec<(Input, usize)>),
}

pub struct ViaRow<'a> {
    pub modes: Vec<Input>,
    pub summary: &'a Summary,
}

pub struct ViaRows<'a> {
    domain: &'a ViaDomain,
    next: usize,
}

impl Default for ViaDomain {
    fn default() -> Self {
        Self(Arc::new(Encoding::Rows(Vec::new())))
    }
}

impl ViaDomain {
    pub(super) fn from_instances(rows: impl IntoIterator<Item = Instance>) -> Self {
        let mut builder = Builder::default();
        for row in rows {
            builder.push(row.modes, Cow::Owned(row.summary));
        }
        builder.finish()
    }

    pub(super) fn uniform(axes: &[Vec<Input>], summary: &Summary) -> Self {
        if axes.iter().any(Vec::is_empty) {
            return Self::default();
        }
        let mut nodes = vec![Node::Leaf(0)];
        for modes in axes.iter().rev() {
            let suffix = nodes.len() - 1;
            nodes.push(Node::Branch(
                modes.iter().map(|&mode| (mode, suffix)).collect(),
            ));
        }
        Self::from_graph(vec![summary.clone()], nodes)
    }

    fn from_graph(summaries: Vec<Summary>, nodes: Vec<Node>) -> Self {
        let mut graph = Graph {
            summaries,
            nodes,
            counts: Vec::new(),
            widths: Vec::new(),
            width: 0,
        };
        graph
            .validate()
            .unwrap_or_else(|error| ril_base::ice!("invalid generated via graph: {error}"));
        Self(Arc::new(Encoding::Graph(graph)))
    }

    pub fn len(&self) -> usize {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.counts.last().copied().unwrap_or_default(),
            Encoding::Rows(rows) => rows.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> ViaRows<'_> {
        self.into_iter()
    }

    pub(crate) fn uses_graph(&self) -> bool {
        matches!(self.0.as_ref(), Encoding::Graph(_))
    }

    pub(crate) fn compact(&self) -> Self {
        let Encoding::Rows(rows) = self.0.as_ref() else {
            return self.clone();
        };
        let Some(first) = rows.first() else {
            return self.clone();
        };
        if rows.iter().any(|row| row.modes.len() != first.modes.len()) {
            return self.clone();
        }
        let mut builder = Builder::default();
        for row in rows {
            builder.push(row.modes.clone(), Cow::Borrowed(&row.summary));
        }
        builder.finish()
    }

    pub(super) fn exclude(&mut self, rejected: &BTreeSet<Vec<Input>>) {
        let mut builder = Builder::default();
        for row in self.iter().filter(|row| !rejected.contains(&row.modes)) {
            builder.push(row.modes, Cow::Borrowed(row.summary));
        }
        *self = builder.finish();
    }

    pub(crate) fn select(&self, actual: &[Option<Input>]) -> Option<&Summary> {
        self.matching(actual.len(), |index| actual.get(index).copied().flatten())
    }

    pub(super) fn count_matching(&self, pattern: &[Option<Input>]) -> usize {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.count_matching(pattern),
            Encoding::Rows(rows) => rows
                .iter()
                .filter(|row| {
                    row.modes.len() == pattern.len()
                        && row.modes.iter().zip(pattern).all(|(&mode, expected)| {
                            expected.is_none_or(|expected| expected == mode)
                        })
                })
                .map(|row| &row.modes)
                .collect::<BTreeSet<_>>()
                .len(),
        }
    }

    pub(super) fn all_at(&self, axis: usize, permits: impl Fn(Input) -> bool) -> bool {
        match self.0.as_ref() {
            Encoding::Graph(graph) => axis < graph.width && graph.modes_at(axis).all(permits),
            Encoding::Rows(rows) => rows
                .iter()
                .all(|row| row.modes.get(axis).copied().is_some_and(&permits)),
        }
    }

    pub(super) fn marginal_len(&self, axis: usize) -> usize {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.modes_at(axis).count(),
            Encoding::Rows(rows) => rows
                .iter()
                .filter_map(|row| row.modes.get(axis))
                .collect::<BTreeSet<_>>()
                .len(),
        }
    }

    fn matching(&self, width: usize, mode: impl Fn(usize) -> Option<Input>) -> Option<&Summary> {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.matching(width, mode),
            Encoding::Rows(rows) => rows.iter().find_map(|row| {
                (row.modes.len() == width
                    && row
                        .modes
                        .iter()
                        .copied()
                        .enumerate()
                        .all(|(index, input)| mode(index).is_none_or(|actual| actual == input)))
                .then_some(&row.summary)
            }),
        }
    }

    pub fn subsumes(&self, revision: &Self) -> bool {
        match (self.0.as_ref(), revision.0.as_ref()) {
            (Encoding::Graph(old), Encoding::Graph(new)) => old.subsumes(new),
            _ => self.iter().all(|old| {
                revision
                    .matching(old.modes.len(), |index| old.modes.get(index).copied())
                    .is_some_and(|new| old.summary.subsumes(new))
            }),
        }
    }
}

impl<'a> IntoIterator for &'a ViaDomain {
    type Item = ViaRow<'a>;
    type IntoIter = ViaRows<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ViaRows {
            domain: self,
            next: 0,
        }
    }
}

impl<'a> Iterator for ViaRows<'a> {
    type Item = ViaRow<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.next;
        if index >= self.domain.len() {
            return None;
        }
        self.next += 1;
        match self.domain.0.as_ref() {
            Encoding::Graph(graph) => graph.row(index),
            Encoding::Rows(rows) => rows.get(index).map(|row| ViaRow {
                modes: row.modes.clone(),
                summary: &row.summary,
            }),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.domain.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for ViaRows<'_> {}

impl Serialize for ViaDomain {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ViaDomain {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut encoding = Encoding::deserialize(deserializer)?;
        if let Encoding::Graph(graph) = &mut encoding {
            graph.validate().map_err(D::Error::custom)?;
        }
        Ok(Self(Arc::new(encoding)))
    }
}

impl Graph {
    fn validate(&mut self) -> Result<(), &'static str> {
        self.widths.clear();
        self.counts.clear();
        for (index, node) in self.nodes.iter().enumerate() {
            let (width, count) = match node {
                Node::Leaf(summary) if *summary < self.summaries.len() => (0, 1),
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
                    let mut count = 0_usize;
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
                            .checked_add(self.counts.get(child).copied().unwrap_or_default())
                            .ok_or("too many via mode tuples")?;
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

    fn row(&self, mut position: usize) -> Option<ViaRow<'_>> {
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

    fn matching(&self, width: usize, mode: impl Fn(usize) -> Option<Input>) -> Option<&Summary> {
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

    fn modes_at(&self, axis: usize) -> impl Iterator<Item = Input> + '_ {
        Input::ALL.into_iter().filter(move |&mode| {
            axis < self.width
                && self
                    .matching(self.width, |depth| (depth == axis).then_some(mode))
                    .is_some()
        })
    }

    fn count_matching(&self, pattern: &[Option<Input>]) -> usize {
        if pattern.len() != self.width {
            return 0;
        }
        if pattern.iter().all(Option::is_some) {
            return usize::from(
                self.matching(pattern.len(), |depth| pattern.get(depth).copied().flatten())
                    .is_some(),
            );
        }
        let mut counts = Vec::with_capacity(self.nodes.len());
        for (node, &width) in self.nodes.iter().zip(&self.widths) {
            let count = match node {
                Node::Leaf(_) => 1,
                Node::Branch(edges) if width <= pattern.len() => {
                    let expected = pattern.get(pattern.len() - width).copied().flatten();
                    edges
                        .iter()
                        .filter(|(input, _)| expected.is_none_or(|expected| expected == *input))
                        .filter_map(|(_, child)| counts.get(*child).copied())
                        .sum()
                }
                Node::Branch(_) => 0,
            };
            counts.push(count);
        }
        counts.last().copied().unwrap_or_default()
    }

    fn subsumes(&self, revision: &Self) -> bool {
        if self.width != revision.width {
            return false;
        }
        let Some(old_root) = self.nodes.len().checked_sub(1) else {
            return true;
        };
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

#[derive(Default)]
struct Builder {
    rows: BTreeMap<Vec<Input>, usize>,
    summaries: Vec<Summary>,
    summary_ids: BTreeMap<Vec<u8>, usize>,
    previous: Option<usize>,
}

impl Builder {
    fn push(&mut self, modes: Vec<Input>, summary: Cow<'_, Summary>) {
        let std::collections::btree_map::Entry::Vacant(row) = self.rows.entry(modes) else {
            return;
        };
        let id = if let Some(id) = self.previous
            && self.summaries.get(id) == Some(summary.as_ref())
        {
            id
        } else {
            let data = serde_json::to_vec(summary.as_ref())
                .unwrap_or_else(|error| ril_base::ice!("could not encode via summary: {error}"));
            *self.summary_ids.entry(data).or_insert_with(|| {
                self.summaries.push(summary.into_owned());
                self.summaries.len() - 1
            })
        };
        self.previous = Some(id);
        row.insert(id);
    }

    fn finish(self) -> ViaDomain {
        let Some(width) = self.rows.keys().next().map(Vec::len) else {
            return ViaDomain::default();
        };
        let mut nodes = Vec::new();
        let mut interned = BTreeMap::new();
        let mut intern = |node: Node| {
            *interned.entry(node).or_insert_with_key(|node| {
                nodes.push(node.clone());
                nodes.len() - 1
            })
        };
        let mut rows: Vec<_> = self
            .rows
            .into_iter()
            .map(|(modes, summary)| (modes, intern(Node::Leaf(summary))))
            .collect();
        // Fold the sorted rows from the final axis to the first.
        for axis in (0..width).rev() {
            rows = rows
                .chunk_by(|left, right| left.0.get(..axis) == right.0.get(..axis))
                .map(|group| {
                    let prefix = group
                        .first()
                        .and_then(|row| row.0.get(..axis))
                        .unwrap_or_else(|| ril_base::ice!("missing via mode prefix"))
                        .to_vec();
                    let edges = group
                        .iter()
                        .map(|(modes, child)| {
                            let mode = modes
                                .get(axis)
                                .copied()
                                .unwrap_or_else(|| ril_base::ice!("missing via mode axis"));
                            (mode, *child)
                        })
                        .collect();
                    (prefix, intern(Node::Branch(edges)))
                })
                .collect();
        }
        ViaDomain::from_graph(self.summaries, nodes)
    }
}
