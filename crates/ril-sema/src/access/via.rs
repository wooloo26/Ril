use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashMap},
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
    counts: Vec<u128>,
    #[serde(skip)]
    widths: Vec<usize>,
    #[serde(skip)]
    width: usize,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
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

    /// Build a canonical MDD directly by splitting only on axes in `relevant`.
    ///
    /// Axes outside `relevant` share a single child DAG node across all permitted modes,
    /// avoiding `O(5^{k_total})` Cartesian enumeration when `k_relevant < k_total`.
    pub(super) fn build_relevant(
        permitted: &[Vec<Input>],
        relevant: &BTreeSet<usize>,
        specialize: impl FnMut(&[Input]) -> Summary,
    ) -> Self {
        if permitted.is_empty() || permitted.iter().any(Vec::is_empty) {
            return Self::default();
        }
        struct RelevantBuilder<'a, F> {
            permitted: &'a [Vec<Input>],
            relevant: &'a BTreeSet<usize>,
            specialize: F,
            current: Vec<Input>,
            summaries: Vec<Summary>,
            summary_ids: HashMap<Summary, usize>,
            nodes: Vec<Node>,
            interned: HashMap<Node, usize>,
        }

        impl<F: FnMut(&[Input]) -> Summary> RelevantBuilder<'_, F> {
            fn intern(&mut self, node: Node) -> usize {
                if let Some(&id) = self.interned.get(&node) {
                    return id;
                }
                let id = self.nodes.len();
                self.nodes.push(node.clone());
                self.interned.insert(node, id);
                id
            }

            fn build(&mut self, axis: usize) -> usize {
                if axis == self.permitted.len() {
                    let summary = (self.specialize)(&self.current);
                    let sid = if let Some(&id) = self.summary_ids.get(&summary) {
                        id
                    } else {
                        let id = self.summaries.len();
                        self.summaries.push(summary.clone());
                        self.summary_ids.insert(summary, id);
                        id
                    };
                    return self.intern(Node::Leaf(sid));
                }
                let Some(modes) = self.permitted.get(axis) else {
                    ril_base::ice!("invalid via axis index");
                };
                if !self.relevant.contains(&axis) {
                    if let (Some(&first), Some(slot)) = (modes.first(), self.current.get_mut(axis))
                    {
                        *slot = first;
                    }
                    let child = self.build(axis + 1);
                    let edges = modes.iter().map(|&mode| (mode, child)).collect();
                    return self.intern(Node::Branch(edges));
                }
                let mut edges = Vec::with_capacity(modes.len());
                for &mode in modes {
                    if let Some(slot) = self.current.get_mut(axis) {
                        *slot = mode;
                    }
                    let child = self.build(axis + 1);
                    edges.push((mode, child));
                }
                self.intern(Node::Branch(edges))
            }
        }

        let current = permitted
            .iter()
            .map(|modes| modes.first().copied().unwrap_or(Input::Plain))
            .collect();
        let mut builder = RelevantBuilder {
            permitted,
            relevant,
            specialize,
            current,
            summaries: Vec::new(),
            summary_ids: HashMap::new(),
            nodes: Vec::new(),
            interned: HashMap::new(),
        };
        let _root = builder.build(0);
        Self::from_graph(builder.summaries, builder.nodes)
    }

    /// Filter this domain natively on the MDD DAG using a predicate that depends ONLY on
    /// the axes listed in `support_axes` (which must be sorted and unique).
    ///
    /// Returns `(kept_domain, removed_domain, removed_any)` in time proportional to
    /// `O(|DAG| * 5^{|support|})`, never enumerating unaffected axes.
    pub(super) fn partition_support<T>(
        &self,
        support_axes: &[usize],
        classify: impl FnMut(&[(usize, Input)]) -> Option<T>,
    ) -> (Self, Self, Option<T>) {
        let compact = self.compact();
        let Encoding::Graph(graph) = compact.0.as_ref() else {
            return (Self::default(), Self::default(), None);
        };
        let Some(root) = graph.nodes.len().checked_sub(1) else {
            return (Self::default(), Self::default(), None);
        };

        struct Partitioner<'a, F, T> {
            graph: &'a Graph,
            support: &'a [usize],
            classify: F,
            assigned: Vec<(usize, Input)>,
            first_rejected: Option<T>,
            kept_nodes: Vec<Node>,
            kept_intern: HashMap<Node, usize>,
            removed_nodes: Vec<Node>,
            removed_intern: HashMap<Node, usize>,
            // Memoize (orig_node, packed_support_values_up_to_depth) -> (kept_opt, removed_opt)
            memo: HashMap<(usize, u64), (Option<usize>, Option<usize>)>,
        }

        impl<F: FnMut(&[(usize, Input)]) -> Option<T>, T> Partitioner<'_, F, T> {
            fn intern_kept(&mut self, node: Node) -> usize {
                if let Some(&id) = self.kept_intern.get(&node) {
                    return id;
                }
                let id = self.kept_nodes.len();
                self.kept_nodes.push(node.clone());
                self.kept_intern.insert(node, id);
                id
            }

            fn intern_removed(&mut self, node: Node) -> usize {
                if let Some(&id) = self.removed_intern.get(&node) {
                    return id;
                }
                let id = self.removed_nodes.len();
                self.removed_nodes.push(node.clone());
                self.removed_intern.insert(node, id);
                id
            }

            fn visit(
                &mut self,
                node_idx: usize,
                depth: usize,
                sup_pos: usize,
                key_bits: u64,
            ) -> (Option<usize>, Option<usize>) {
                // Only memoize when all support assignments so far fit in 64 bits (up to 21 support axes at 3 bits each).
                let can_memo = self.support.len() <= 21;
                if can_memo && let Some(&cached) = self.memo.get(&(node_idx, key_bits)) {
                    return cached;
                }
                let Some(node) = self.graph.nodes.get(node_idx) else {
                    return (None, None);
                };
                let result = match node {
                    Node::Leaf(summary_idx) => {
                        if let Some(rejection) = (self.classify)(&self.assigned) {
                            if self.first_rejected.is_none() {
                                self.first_rejected = Some(rejection);
                            }
                            (None, Some(self.intern_removed(Node::Leaf(*summary_idx))))
                        } else {
                            (Some(self.intern_kept(Node::Leaf(*summary_idx))), None)
                        }
                    }
                    Node::Branch(edges) => {
                        let is_support = self.support.get(sup_pos) == Some(&depth);
                        let mut kept_edges = Vec::new();
                        let mut removed_edges = Vec::new();
                        for &(mode, child) in edges {
                            let (k, r) = if is_support {
                                self.assigned.push((depth, mode));
                                let bits = (key_bits << 3) | u64::from(mode_bits(mode));
                                let res = self.visit(child, depth + 1, sup_pos + 1, bits);
                                self.assigned.pop();
                                res
                            } else {
                                self.visit(child, depth + 1, sup_pos, key_bits)
                            };
                            if let Some(k) = k {
                                kept_edges.push((mode, k));
                            }
                            if let Some(r) = r {
                                removed_edges.push((mode, r));
                            }
                        }
                        let kept = (!kept_edges.is_empty())
                            .then(|| self.intern_kept(Node::Branch(kept_edges)));
                        let removed = (!removed_edges.is_empty())
                            .then(|| self.intern_removed(Node::Branch(removed_edges)));
                        (kept, removed)
                    }
                };
                if can_memo {
                    self.memo.insert((node_idx, key_bits), result);
                }
                result
            }
        }

        let mut part = Partitioner {
            graph,
            support: support_axes,
            classify,
            assigned: Vec::with_capacity(support_axes.len()),
            first_rejected: None,
            kept_nodes: Vec::new(),
            kept_intern: HashMap::new(),
            removed_nodes: Vec::new(),
            removed_intern: HashMap::new(),
            memo: HashMap::new(),
        };
        let (kept_root, removed_root) = part.visit(root, 0, 0, 0);
        let kept = match kept_root {
            Some(_) => Self::from_graph(graph.summaries.clone(), part.kept_nodes),
            None => Self::default(),
        };
        let removed = match removed_root {
            Some(_) => Self::from_graph(graph.summaries.clone(), part.removed_nodes),
            None => Self::default(),
        };
        (kept, removed, part.first_rejected)
    }

    /// Compute the DAG union of two mask/excluded domains of identical width (summaries are collapsed to a unit placeholder).
    pub(super) fn union_mask(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        let a = self.compact();
        let b = other.compact();
        let (Encoding::Graph(ga), Encoding::Graph(gb)) = (a.0.as_ref(), b.0.as_ref()) else {
            return Self::default();
        };
        if ga.width != gb.width {
            return self.clone();
        }
        let (Some(ra), Some(rb)) = (ga.nodes.len().checked_sub(1), gb.nodes.len().checked_sub(1))
        else {
            return Self::default();
        };
        struct Unioner<'a> {
            ga: &'a Graph,
            gb: &'a Graph,
            nodes: Vec<Node>,
            intern: HashMap<Node, usize>,
            memo: HashMap<(Option<usize>, Option<usize>), usize>,
        }
        impl Unioner<'_> {
            fn intern(&mut self, node: Node) -> usize {
                if let Some(&id) = self.intern.get(&node) {
                    return id;
                }
                let id = self.nodes.len();
                self.nodes.push(node.clone());
                self.intern.insert(node, id);
                id
            }
            fn visit(&mut self, a: Option<usize>, b: Option<usize>) -> usize {
                if let Some(&id) = self.memo.get(&(a, b)) {
                    return id;
                }
                let na = a.and_then(|i| self.ga.nodes.get(i));
                let nb = b.and_then(|i| self.gb.nodes.get(i));
                let id = match (na, nb) {
                    (Some(Node::Leaf(_)), _) | (_, Some(Node::Leaf(_))) => {
                        self.intern(Node::Leaf(0))
                    }
                    (Some(Node::Branch(ea)), Some(Node::Branch(eb))) => {
                        let mut edges = Vec::new();
                        let (mut ia, mut ib) = (0, 0);
                        while ia < ea.len() || ib < eb.len() {
                            match (ea.get(ia), eb.get(ib)) {
                                (Some(&(ma, ca)), Some(&(mb, cb))) if ma == mb => {
                                    let child = self.visit(Some(ca), Some(cb));
                                    edges.push((ma, child));
                                    ia += 1;
                                    ib += 1;
                                }
                                (Some(&(ma, ca)), Some(&(mb, _))) if ma < mb => {
                                    let child = self.visit(Some(ca), None);
                                    edges.push((ma, child));
                                    ia += 1;
                                }
                                (Some(&(ma, ca)), None) => {
                                    let child = self.visit(Some(ca), None);
                                    edges.push((ma, child));
                                    ia += 1;
                                }
                                (_, Some(&(mb, cb))) => {
                                    let child = self.visit(None, Some(cb));
                                    edges.push((mb, child));
                                    ib += 1;
                                }
                                (None, None) => break,
                            }
                        }
                        self.intern(Node::Branch(edges))
                    }
                    (Some(Node::Branch(ea)), None) => {
                        let edges = ea
                            .iter()
                            .map(|&(m, c)| (m, self.visit(Some(c), None)))
                            .collect();
                        self.intern(Node::Branch(edges))
                    }
                    (None, Some(Node::Branch(eb))) => {
                        let edges = eb
                            .iter()
                            .map(|&(m, c)| (m, self.visit(None, Some(c))))
                            .collect();
                        self.intern(Node::Branch(edges))
                    }
                    (None, None) => self.intern(Node::Leaf(0)),
                };
                self.memo.insert((a, b), id);
                id
            }
        }
        let mut unioner = Unioner {
            ga,
            gb,
            nodes: Vec::new(),
            intern: HashMap::new(),
            memo: HashMap::new(),
        };
        let _ = unioner.visit(Some(ra), Some(rb));
        Self::from_graph(vec![Summary::default()], unioner.nodes)
    }

    /// Subtract all mode tuples present in `mask` natively on the MDD DAG in `O(|self| * |mask|)`.
    pub(super) fn subtract_mask(&self, mask: &Self) -> Self {
        if self.is_empty() || mask.is_empty() {
            return self.clone();
        }
        let a = self.compact();
        let b = mask.compact();
        let (Encoding::Graph(ga), Encoding::Graph(gb)) = (a.0.as_ref(), b.0.as_ref()) else {
            return self.clone();
        };
        if ga.width != gb.width {
            return self.clone();
        }
        let (Some(ra), Some(rb)) = (ga.nodes.len().checked_sub(1), gb.nodes.len().checked_sub(1))
        else {
            return self.clone();
        };
        struct Subtractor<'a> {
            ga: &'a Graph,
            gb: &'a Graph,
            nodes: Vec<Node>,
            intern: HashMap<Node, usize>,
            memo: HashMap<(usize, Option<usize>), Option<usize>>,
        }
        impl Subtractor<'_> {
            fn intern(&mut self, node: Node) -> usize {
                if let Some(&id) = self.intern.get(&node) {
                    return id;
                }
                let id = self.nodes.len();
                self.nodes.push(node.clone());
                self.intern.insert(node, id);
                id
            }
            fn visit(&mut self, a: usize, b: Option<usize>) -> Option<usize> {
                if let Some(&cached) = self.memo.get(&(a, b)) {
                    return cached;
                }
                let na = self.ga.nodes.get(a)?;
                let nb = b.and_then(|i| self.gb.nodes.get(i));
                let res = match (na, nb) {
                    (Node::Leaf(_), Some(Node::Leaf(_))) => None,
                    (Node::Leaf(sid), None) => Some(self.intern(Node::Leaf(*sid))),
                    (Node::Branch(ea), Some(Node::Branch(eb))) => {
                        let mut edges = Vec::new();
                        for &(ma, ca) in ea {
                            let cb = eb
                                .binary_search_by_key(&ma, |&(mb, _)| mb)
                                .ok()
                                .and_then(|idx| eb.get(idx).map(|&(_, child)| child));
                            if let Some(child) = self.visit(ca, cb) {
                                edges.push((ma, child));
                            }
                        }
                        (!edges.is_empty()).then(|| self.intern(Node::Branch(edges)))
                    }
                    (Node::Branch(ea), None) => {
                        let mut edges = Vec::with_capacity(ea.len());
                        for &(ma, ca) in ea {
                            if let Some(child) = self.visit(ca, None) {
                                edges.push((ma, child));
                            }
                        }
                        (!edges.is_empty()).then(|| self.intern(Node::Branch(edges)))
                    }
                    _ => None,
                };
                self.memo.insert((a, b), res);
                res
            }
        }
        let mut sub = Subtractor {
            ga,
            gb,
            nodes: Vec::new(),
            intern: HashMap::new(),
            memo: HashMap::new(),
        };
        match sub.visit(ra, Some(rb)) {
            Some(_) => Self::from_graph(ga.summaries.clone(), sub.nodes),
            None => Self::default(),
        }
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

    pub fn len_u128(&self) -> u128 {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.counts.last().copied().unwrap_or_default(),
            Encoding::Rows(rows) => rows.len() as u128,
        }
    }

    pub fn len(&self) -> usize {
        usize::try_from(self.len_u128()).unwrap_or(usize::MAX)
    }

    pub fn is_empty(&self) -> bool {
        self.len_u128() == 0
    }

    pub fn iter(&self) -> ViaRows<'_> {
        self.into_iter()
    }

    pub fn uses_graph(&self) -> bool {
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

    pub(crate) fn select(&self, actual: &[Option<Input>]) -> Option<&Summary> {
        self.matching(actual.len(), |index| actual.get(index).copied().flatten())
    }

    pub(super) fn count_matching_u128(&self, pattern: &[Option<Input>]) -> u128 {
        match self.0.as_ref() {
            Encoding::Graph(graph) => graph.count_matching_u128(pattern),
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
                .len() as u128,
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

const fn mode_bits(mode: Input) -> u8 {
    match mode {
        Input::Plain => 1,
        Input::Ref => 2,
        Input::Mut => 3,
        Input::Shared => 4,
        Input::New => 5,
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
            Encoding::Graph(graph) => graph.row(index as u128),
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

    fn row(&self, mut position: u128) -> Option<ViaRow<'_>> {
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

    fn count_matching_u128(&self, pattern: &[Option<Input>]) -> u128 {
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
    summary_ids: HashMap<Summary, usize>,
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
        } else if let Some(&id) = self.summary_ids.get(summary.as_ref()) {
            id
        } else {
            let owned = summary.into_owned();
            let id = self.summaries.len();
            self.summaries.push(owned.clone());
            self.summary_ids.insert(owned, id);
            id
        };
        self.previous = Some(id);
        row.insert(id);
    }

    fn finish(self) -> ViaDomain {
        let Some(width) = self.rows.keys().next().map(Vec::len) else {
            return ViaDomain::default();
        };
        let mut nodes = Vec::new();
        let mut interned = HashMap::new();
        let mut intern = |node: Node| {
            if let Some(&id) = interned.get(&node) {
                return id;
            }
            let id = nodes.len();
            nodes.push(node.clone());
            interned.insert(node, id);
            id
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
