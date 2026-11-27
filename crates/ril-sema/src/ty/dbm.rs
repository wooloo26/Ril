use std::collections::{HashMap, HashSet};

use ril_hir::DefinitionId;
use serde::{Deserialize, Serialize};

pub(super) const MAX_DBM_ATOMS: usize = 64;

/// A statically tracked variable or nested field/tuple/inner path.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Place {
    pub(super) root: DefinitionId,
    pub(super) path: Vec<String>,
}

impl Place {
    pub(super) fn local(root: DefinitionId) -> Self {
        Self {
            root,
            path: Vec::new(),
        }
    }

    pub(super) fn extends(&self, prefix: &Place) -> bool {
        self.root == prefix.root && self.path.starts_with(&prefix.path)
    }
}

/// Positional parameter path used in lowered Type-Function predicates and `.rili` interfaces.
/// `param_idx == 0` is the piped subject (`x |> Pred(...)` or return value `-> R |> Pred(...)`).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub(crate) struct ProofPlace {
    pub(crate) param_idx: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) path: Vec<String>,
}

/// Symbolic integer atom in a lowered Type-Function predicate.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub(crate) enum ProofAtom {
    Val(ProofPlace),
    Len(ProofPlace),
}

/// Negation-normal-form difference-logic predicate parameterized by atom type `A`.
/// `None` in `lhs`/`rhs` denotes the constant `0` (`Atom::Zero`).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub(crate) enum ProofPred<A> {
    True,
    False,
    /// `lhs - rhs <= bound` (`None` = 0).
    DiffLe {
        lhs: Option<A>,
        rhs: Option<A>,
        bound: i128,
    },
    /// `lhs - rhs != offset` (`None` = 0).
    DiffNe {
        lhs: Option<A>,
        rhs: Option<A>,
        offset: i128,
    },
    And(Vec<ProofPred<A>>),
    Or(Vec<ProofPred<A>>),
}

impl<A: Clone + Eq> ProofPred<A> {
    pub(crate) fn diff_le(lhs: Option<A>, rhs: Option<A>, bound: i128) -> Self {
        if lhs == rhs {
            return if 0 <= bound { Self::True } else { Self::False };
        }
        Self::DiffLe { lhs, rhs, bound }
    }

    pub(crate) fn diff_ne(lhs: Option<A>, rhs: Option<A>, offset: i128) -> Self {
        if lhs == rhs {
            return if 0 != offset { Self::True } else { Self::False };
        }
        Self::DiffNe { lhs, rhs, offset }
    }

    pub(crate) fn diff_eq(lhs: Option<A>, rhs: Option<A>, offset: i128) -> Self {
        let Some(neg) = offset.checked_neg() else {
            return Self::True;
        };
        Self::and(vec![
            Self::diff_le(lhs.clone(), rhs.clone(), offset),
            Self::diff_le(rhs, lhs, neg),
        ])
    }

    pub(crate) fn and(items: Vec<Self>) -> Self {
        let mut flat = Vec::with_capacity(items.len());
        for item in items {
            match item {
                Self::True => {}
                Self::False => return Self::False,
                Self::And(inner) => {
                    for sub in inner {
                        if !flat.contains(&sub) {
                            flat.push(sub);
                        }
                    }
                }
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => Self::True,
            1 => flat.pop().unwrap(),
            _ => Self::And(flat),
        }
    }

    pub(crate) fn or(items: Vec<Self>) -> Self {
        let mut flat = Vec::with_capacity(items.len());
        for item in items {
            match item {
                Self::False => {}
                Self::True => return Self::True,
                Self::Or(inner) => {
                    for sub in inner {
                        if !flat.contains(&sub) {
                            flat.push(sub);
                        }
                    }
                }
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => Self::False,
            1 => flat.pop().unwrap(),
            _ => Self::Or(flat),
        }
    }

    /// Exact logical negation over Z in negation normal form.
    pub(crate) fn negate(&self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::DiffLe { lhs, rhs, bound } => match bound.checked_neg().and_then(|n| n.checked_sub(1)) {
                Some(neg) => Self::diff_le(rhs.clone(), lhs.clone(), neg),
                None => Self::True,
            },
            Self::DiffNe { lhs, rhs, offset } => Self::diff_eq(lhs.clone(), rhs.clone(), *offset),
            Self::And(ps) => Self::or(ps.iter().map(Self::negate).collect()),
            Self::Or(ps) => Self::and(ps.iter().map(Self::negate).collect()),
        }
    }

    pub(crate) fn map_atoms<B: Clone + Eq, F>(&self, f: &mut F) -> Option<ProofPred<B>>
    where
        F: FnMut(&A) -> Option<B>,
    {
        Some(match self {
            Self::True => ProofPred::True,
            Self::False => ProofPred::False,
            Self::DiffLe { lhs, rhs, bound } => ProofPred::diff_le(
                match lhs {
                    Some(a) => Some(f(a)?),
                    None => None,
                },
                match rhs {
                    Some(b) => Some(f(b)?),
                    None => None,
                },
                *bound,
            ),
            Self::DiffNe { lhs, rhs, offset } => ProofPred::diff_ne(
                match lhs {
                    Some(a) => Some(f(a)?),
                    None => None,
                },
                match rhs {
                    Some(b) => Some(f(b)?),
                    None => None,
                },
                *offset,
            ),
            Self::And(ps) => {
                let mut out = Vec::with_capacity(ps.len());
                for p in ps {
                    out.push(p.map_atoms(f)?);
                }
                ProofPred::and(out)
            }
            Self::Or(ps) => {
                let mut out = Vec::with_capacity(ps.len());
                for p in ps {
                    out.push(p.map_atoms(f)?);
                }
                ProofPred::or(out)
            }
        })
    }
}

/// Concrete DBM node in a function's flow-sensitive refinement environment.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Atom {
    Zero,
    Val(Place),
    Len(Place),
    Proof(ProofAtom),
    Temp(u32),
}

/// Closed Difference-Bound Matrix over `{Zero} ∪ active integer/length atoms`,
/// augmented with canonical disequalities `(u, v, k)` (`u - v != k`, `u < v`).
#[derive(Clone, Debug)]
pub(super) struct Dbm {
    atoms: Vec<Atom>,
    index: HashMap<Atom, usize>,
    /// Row-major `n * n` matrix: `mat[u * n + v] == Some(c)` means `atoms[u] - atoms[v] <= c`.
    mat: Vec<Option<i128>>,
    /// Canonical disequalities `(u, v, k)` with `u < v` meaning `atoms[u] - atoms[v] != k`.
    non_equal: HashSet<(usize, usize, i128)>,
    /// Canonical sum upper bounds `(a, b, c, k)` with `a <= b` meaning `atoms[a] + atoms[b] <= atoms[c] + k`.
    sum_le: HashSet<(usize, usize, usize, i128)>,
    pub(super) unsat: bool,
    next_temp: u32,
}

impl Default for Dbm {
    fn default() -> Self {
        Self::new()
    }
}

impl Dbm {
    pub(super) fn new() -> Self {
        let mut index = HashMap::new();
        index.insert(Atom::Zero, 0);
        Self {
            atoms: vec![Atom::Zero],
            index,
            mat: vec![Some(0)],
            non_equal: HashSet::new(),
            sum_le: HashSet::new(),
            unsat: false,
            next_temp: 0,
        }
    }

    #[inline]
    fn n(&self) -> usize {
        self.atoms.len()
    }

    #[inline]
    fn get(&self, u: usize, v: usize) -> Option<i128> {
        self.mat[u * self.atoms.len() + v]
    }

    #[inline]
    fn set(&mut self, u: usize, v: usize, val: Option<i128>) {
        let n = self.atoms.len();
        self.mat[u * n + v] = val;
    }

    pub(super) fn fresh_temp_id(&mut self) -> u32 {
        let id = self.next_temp;
        self.next_temp = self.next_temp.wrapping_add(1);
        id
    }

    pub(super) fn fresh_temp(&mut self) -> Atom {
        Atom::Temp(self.fresh_temp_id())
    }

    pub(super) fn ensure_atom(&mut self, atom: Atom) -> Option<usize> {
        if let Some(&idx) = self.index.get(&atom) {
            return Some(idx);
        }
        let old_n = self.atoms.len();
        if old_n >= MAX_DBM_ATOMS {
            return None;
        }
        let new_n = old_n + 1;
        let is_len = matches!(atom, Atom::Len(_) | Atom::Proof(ProofAtom::Len(_)));
        let inner_len_parent = match &atom {
            Atom::Len(p) if p.path.last().is_some_and(|s| s == "#inner") => {
                let mut parent = p.clone();
                parent.path.pop();
                Some(Atom::Len(parent))
            }
            _ => None,
        };
        let mut new_mat = vec![None; new_n * new_n];
        for i in 0..old_n {
            let src = &self.mat[i * old_n..(i + 1) * old_n];
            let dst = &mut new_mat[i * new_n..i * new_n + old_n];
            dst.copy_from_slice(src);
        }
        new_mat[old_n * new_n + old_n] = Some(0);
        self.atoms.push(atom.clone());
        self.index.insert(atom, old_n);
        self.mat = new_mat;
        if is_len {
            // Axiom: every collection/string/bytes length is >= 0 (`0 - len(p) <= 0`).
            self.add_le_idx(0, old_n, 0);
        }
        if let Some(parent_atom) = inner_len_parent
            && let Some(parent_idx) = self.ensure_atom(parent_atom)
        {
            // Axiom: `len(inner(w)) == len(w)` for nominal/opaque collection wrappers (`Set<T>`, `Derived<T>`).
            self.add_le_idx(old_n, parent_idx, 0);
            self.add_le_idx(parent_idx, old_n, 0);
        }
        Some(old_n)
    }

    fn atom_idx(&self, atom: &Atom) -> Option<usize> {
        self.index.get(atom).copied()
    }

    /// Incremental O(N^2) edge insertion `atoms[u] - atoms[v] <= c` preserving shortest-path closure.
    pub(super) fn add_le_idx(&mut self, u: usize, v: usize, c: i128) {
        if self.unsat {
            return;
        }
        if u == v {
            if c < 0 {
                self.unsat = true;
            }
            return;
        }
        if self.get(u, v).is_some_and(|cur| cur <= c) {
            return;
        }
        // Negative cycle check: `mat[v, u] + c < 0`.
        if let Some(back) = self.get(v, u)
            && back.checked_add(c).is_some_and(|sum| sum < 0)
        {
            self.unsat = true;
            return;
        }
        let n = self.n();
        // Snapshot row `v` and col `u` to keep closure exact while updating `mat`.
        let mut col_u = [None; MAX_DBM_ATOMS];
        let mut row_v = [None; MAX_DBM_ATOMS];
        for i in 0..n {
            col_u[i] = self.mat[i * n + u];
            row_v[i] = self.mat[v * n + i];
        }
        for i in 0..n {
            let Some(iu) = col_u[i] else { continue };
            let Some(iu_c) = iu.checked_add(c) else { continue };
            let row = i * n;
            for j in 0..n {
                let Some(vj) = row_v[j] else { continue };
                let Some(cand) = iu_c.checked_add(vj) else { continue };
                let cell = &mut self.mat[row + j];
                if cell.is_none_or(|cur| cand < cur) {
                    *cell = Some(cand);
                }
            }
        }
        self.propagate_disequalities();
    }

    fn canonical_ne(u: usize, v: usize, k: i128) -> Option<(usize, usize, i128)> {
        if u < v {
            Some((u, v, k))
        } else if v < u {
            k.checked_neg().map(|nk| (v, u, nk))
        } else {
            None
        }
    }

    pub(super) fn add_ne_idx(&mut self, u: usize, v: usize, k: i128) {
        if self.unsat {
            return;
        }
        if u == v {
            if k == 0 {
                self.unsat = true;
            }
            return;
        }
        if let Some(entry) = Self::canonical_ne(u, v, k) {
            self.non_equal.insert(entry);
            self.propagate_disequalities();
        }
    }

    fn propagate_disequalities(&mut self) {
        loop {
            if self.unsat || self.non_equal.is_empty() {
                return;
            }
            let mut tightened: Option<(usize, usize, i128)> = None;
            let mut drop_list = Vec::new();
            for &(a, b, k) in &self.non_equal {
                let ab = self.get(a, b);
                let ba = self.get(b, a);
                let neg_k = k.checked_neg();
                if ab == Some(k) && neg_k.is_some() && ba == neg_k {
                    self.unsat = true;
                    return;
                }
                if k.checked_sub(1).is_some_and(|km1| ab.is_some_and(|x| x <= km1))
                    || neg_k
                        .and_then(|nk| nk.checked_sub(1))
                        .is_some_and(|nkm1| ba.is_some_and(|x| x <= nkm1))
                {
                    drop_list.push((a, b, k));
                } else if ab == Some(k)
                    && let Some(km1) = k.checked_sub(1)
                {
                    drop_list.push((a, b, k));
                    tightened = Some((a, b, km1));
                    break;
                } else if neg_k.is_some()
                    && ba == neg_k
                    && let Some(nkm1) = neg_k.and_then(|nk| nk.checked_sub(1))
                {
                    drop_list.push((a, b, k));
                    tightened = Some((b, a, nkm1));
                    break;
                }
            }
            for item in drop_list {
                self.non_equal.remove(&item);
            }
            if let Some((u, v, c)) = tightened {
                self.add_le_idx(u, v, c);
            } else {
                break;
            }
        }
    }

    pub(super) fn add_le(&mut self, lhs: Atom, rhs: Atom, bound: i128) {
        if self.unsat {
            return;
        }
        let Some(u) = self.ensure_atom(lhs) else {
            return;
        };
        let Some(v) = self.ensure_atom(rhs) else {
            return;
        };
        self.add_le_idx(u, v, bound);
    }

    pub(super) fn add_eq(&mut self, lhs: Atom, rhs: Atom, offset: i128) {
        if self.unsat {
            return;
        }
        let Some(u) = self.ensure_atom(lhs) else {
            return;
        };
        let Some(v) = self.ensure_atom(rhs) else {
            return;
        };
        self.add_le_idx(u, v, offset);
        if let Some(neg) = offset.checked_neg() {
            self.add_le_idx(v, u, neg);
        }
    }

    pub(super) fn add_ne(&mut self, lhs: Atom, rhs: Atom, offset: i128) {
        if self.unsat {
            return;
        }
        let Some(u) = self.ensure_atom(lhs) else {
            return;
        };
        let Some(v) = self.ensure_atom(rhs) else {
            return;
        };
        self.add_ne_idx(u, v, offset);
    }

    pub(super) fn assume(&mut self, pred: &ProofPred<Atom>) {
        if self.unsat {
            return;
        }
        match pred {
            ProofPred::True => {}
            ProofPred::False => self.unsat = true,
            ProofPred::DiffLe { lhs, rhs, bound } => {
                let u = lhs.clone().unwrap_or(Atom::Zero);
                let v = rhs.clone().unwrap_or(Atom::Zero);
                self.add_le(u, v, *bound);
            }
            ProofPred::DiffNe { lhs, rhs, offset } => {
                let u = lhs.clone().unwrap_or(Atom::Zero);
                let v = rhs.clone().unwrap_or(Atom::Zero);
                self.add_ne(u, v, *offset);
            }
            ProofPred::And(ps) => {
                for p in ps {
                    self.assume(p);
                    if self.unsat {
                        break;
                    }
                }
            }
            ProofPred::Or(ps) => {
                let mut acc: Option<Dbm> = None;
                for p in ps {
                    let mut branch = self.clone();
                    branch.assume(p);
                    if !branch.unsat {
                        acc = Some(match acc {
                            None => branch,
                            Some(cur) => Dbm::join(&cur, &branch),
                        });
                    }
                }
                match acc {
                    Some(joined) => *self = joined,
                    None => self.unsat = true,
                }
            }
        }
    }

    pub(super) fn entails(&self, pred: &ProofPred<Atom>) -> bool {
        if self.unsat {
            return true;
        }
        match pred {
            ProofPred::True => true,
            ProofPred::False => false,
            ProofPred::DiffLe { lhs, rhs, bound } => self.entails_le(
                lhs.as_ref().unwrap_or(&Atom::Zero),
                rhs.as_ref().unwrap_or(&Atom::Zero),
                *bound,
            ),
            ProofPred::DiffNe { lhs, rhs, offset } => self.entails_ne(
                lhs.as_ref().unwrap_or(&Atom::Zero),
                rhs.as_ref().unwrap_or(&Atom::Zero),
                *offset,
            ),
            ProofPred::And(ps) => ps.iter().all(|p| self.entails(p)),
            ProofPred::Or(ps) => {
                if ps.iter().any(|p| self.entails(p)) {
                    return true;
                }
                // Bounded refutation for disjunctive goals (e.g., `0 <= x <= 1 |= x == 0 || x == 1`).
                let mut budget = 8usize;
                self.is_refuted(&pred.negate(), &mut budget)
            }
        }
    }

    fn is_refuted(&self, neg_pred: &ProofPred<Atom>, budget: &mut usize) -> bool {
        if self.unsat {
            return true;
        }
        if *budget == 0 {
            return false;
        }
        match neg_pred {
            ProofPred::True => false,
            ProofPred::False => true,
            ProofPred::DiffLe { .. } | ProofPred::DiffNe { .. } => {
                *budget -= 1;
                let mut copy = self.clone();
                copy.assume(neg_pred);
                copy.unsat
            }
            ProofPred::And(ps) => {
                // Split into non-Or parts first, then branch on first Or.
                let mut copy = self.clone();
                let mut ors = Vec::new();
                for p in ps {
                    if matches!(p, ProofPred::Or(_)) {
                        ors.push(p);
                    } else {
                        copy.assume(p);
                        if copy.unsat {
                            return true;
                        }
                    }
                }
                if let Some((first_or, rest)) = ors.split_first() {
                    let ProofPred::Or(alts) = first_or else {
                        unreachable!()
                    };
                    let rest_vec: Vec<ProofPred<Atom>> = rest.iter().copied().cloned().collect();
                    alts.iter().all(|alt| {
                        let mut sub = rest_vec.clone();
                        sub.push(alt.clone());
                        copy.is_refuted(&ProofPred::and(sub), budget)
                    })
                } else {
                    copy.unsat
                }
            }
            ProofPred::Or(ps) => ps.iter().all(|p| self.is_refuted(p, budget)),
        }
    }

    pub(super) fn entails_le(&self, lhs: &Atom, rhs: &Atom, bound: i128) -> bool {
        if self.unsat {
            return true;
        }
        if lhs == rhs {
            return 0 <= bound;
        }
        // Implicit axiom: `0 - Len(_) <= 0` even if atom is not yet registered.
        if matches!(lhs, Atom::Zero) && matches!(rhs, Atom::Len(_)) && bound >= 0 {
            return true;
        }
        let (Some(u), Some(v)) = (self.atom_idx(lhs), self.atom_idx(rhs)) else {
            return false;
        };
        self.get(u, v).is_some_and(|c| c <= bound)
    }

    pub(super) fn entails_ne(&self, lhs: &Atom, rhs: &Atom, offset: i128) -> bool {
        if self.unsat {
            return true;
        }
        if lhs == rhs {
            return 0 != offset;
        }
        if offset
            .checked_sub(1)
            .is_some_and(|km1| self.entails_le(lhs, rhs, km1))
        {
            return true;
        }
        if offset
            .checked_neg()
            .and_then(|nk| nk.checked_sub(1))
            .is_some_and(|nkm1| self.entails_le(rhs, lhs, nkm1))
        {
            return true;
        }
        let (Some(u), Some(v)) = (self.atom_idx(lhs), self.atom_idx(rhs)) else {
            return false;
        };
        Self::canonical_ne(u, v, offset).is_some_and(|entry| self.non_equal.contains(&entry))
    }

    // Convenience queries
    pub(super) fn lb(&self, atom: &Atom) -> Option<i128> {
        if *atom == Atom::Zero {
            return Some(0);
        }
        if let Some(idx) = self.atom_idx(atom) {
            return self.get(0, idx).and_then(|c| c.checked_neg());
        }
        if matches!(atom, Atom::Len(_) | Atom::Proof(ProofAtom::Len(_))) {
            Some(0)
        } else {
            None
        }
    }

    pub(super) fn ub(&self, atom: &Atom) -> Option<i128> {
        if *atom == Atom::Zero {
            return Some(0);
        }
        self.atom_idx(atom).and_then(|idx| self.get(idx, 0))
    }

    pub(super) fn exact(&self, atom: &Atom) -> Option<i128> {
        let lo = self.lb(atom)?;
        let hi = self.ub(atom)?;
        (lo == hi).then_some(lo)
    }

    pub(super) fn diff_ub(&self, lhs: &Atom, rhs: &Atom) -> Option<i128> {
        if lhs == rhs {
            return Some(0);
        }
        if matches!(lhs, Atom::Zero)
            && matches!(rhs, Atom::Len(_) | Atom::Proof(ProofAtom::Len(_)))
        {
            return Some(
                self.atom_idx(rhs)
                    .and_then(|v| self.get(0, v))
                    .map_or(0, |c| c.min(0)),
            );
        }
        let (Some(u), Some(v)) = (self.atom_idx(lhs), self.atom_idx(rhs)) else {
            return None;
        };
        self.get(u, v)
    }

    pub(super) fn is_nonzero(&self, atom: &Atom) -> bool {
        self.entails_ne(atom, &Atom::Zero, 0)
    }

    pub(super) fn is_nonneg(&self, atom: &Atom) -> bool {
        self.entails_le(&Atom::Zero, atom, 0)
    }

    pub(super) fn is_pos(&self, atom: &Atom) -> bool {
        self.entails_le(&Atom::Zero, atom, -1)
    }

    /// Exact branch merge preserving matrix closedness.
    pub(super) fn join(a: &Dbm, b: &Dbm) -> Dbm {
        if a.unsat {
            return b.clone();
        }
        if b.unsat {
            return a.clone();
        }
        let mut out = Dbm::new();
        out.next_temp = a.next_temp.max(b.next_temp);
        let mut common: Vec<(Atom, usize, usize)> = vec![(Atom::Zero, 0, 0)];
        for (ai, atom) in a.atoms.iter().enumerate().skip(1) {
            if let Some(&bi) = b.index.get(atom) {
                common.push((atom.clone(), ai, bi));
            }
        }
        let n = common.len();
        out.atoms = common.iter().map(|(at, _, _)| at.clone()).collect();
        out.index = out
            .atoms
            .iter()
            .enumerate()
            .map(|(i, at)| (at.clone(), i))
            .collect();
        out.mat = vec![None; n * n];
        for (i, &(_, ai, bi)) in common.iter().enumerate() {
            for (j, &(_, aj, bj)) in common.iter().enumerate() {
                if i == j {
                    out.mat[i * n + j] = Some(0);
                } else if let (Some(x), Some(y)) = (a.get(ai, aj), b.get(bi, bj)) {
                    out.mat[i * n + j] = Some(x.max(y));
                }
            }
        }
        // Retain disequalities entailed by BOTH branches.
        let mut candidates: HashSet<(usize, usize, i128)> = HashSet::new();
        for &(au, av, k) in &a.non_equal {
            if let (Some(&ou), Some(&ov)) = (out.index.get(&a.atoms[au]), out.index.get(&a.atoms[av]))
                && let Some(c) = Self::canonical_ne(ou, ov, k)
            {
                candidates.insert(c);
            }
        }
        for &(bu, bv, k) in &b.non_equal {
            if let (Some(&ou), Some(&ov)) = (out.index.get(&b.atoms[bu]), out.index.get(&b.atoms[bv]))
                && let Some(c) = Self::canonical_ne(ou, ov, k)
            {
                candidates.insert(c);
            }
        }
        for i in 1..n {
            candidates.insert((0, i, 0));
        }
        for (ou, ov, k) in candidates {
            let at_u = &out.atoms[ou];
            let at_v = &out.atoms[ov];
            if a.entails_ne(at_u, at_v, k) && b.entails_ne(at_u, at_v, k) && !out.entails_ne(at_u, at_v, k) {
                out.non_equal.insert((ou, ov, k));
            }
        }
        for &(au, av, aw, k) in &a.sum_le {
            if let (Some(&ou), Some(&ov), Some(&ow)) = (
                out.index.get(&a.atoms[au]),
                out.index.get(&a.atoms[av]),
                out.index.get(&a.atoms[aw]),
            ) && b.has_sum_le(&a.atoms[au], &a.atoms[av], &a.atoms[aw], k)
            {
                let (x, y) = if ou <= ov { (ou, ov) } else { (ov, ou) };
                out.sum_le.insert((x, y, ow, k));
            }
        }
        out
    }

    /// Cousot-Cousot unclosed DBM widening: drops any edge whose upper bound grew.
    pub(super) fn widen(prev: &Dbm, next: &Dbm) -> Dbm {
        if prev.unsat {
            return next.clone();
        }
        if next.unsat {
            return prev.clone();
        }
        let mut out = Dbm::new();
        out.next_temp = prev.next_temp.max(next.next_temp);
        let mut common: Vec<(Atom, usize, usize)> = vec![(Atom::Zero, 0, 0)];
        for (pi, atom) in prev.atoms.iter().enumerate().skip(1) {
            if let Some(&ni) = next.index.get(atom) {
                common.push((atom.clone(), pi, ni));
            }
        }
        let n = common.len();
        out.atoms = common.iter().map(|(at, _, _)| at.clone()).collect();
        out.index = out
            .atoms
            .iter()
            .enumerate()
            .map(|(i, at)| (at.clone(), i))
            .collect();
        out.mat = vec![None; n * n];
        for (i, &(_, pi, ni)) in common.iter().enumerate() {
            for (j, &(_, pj, nj)) in common.iter().enumerate() {
                if i == j {
                    out.mat[i * n + j] = Some(0);
                } else if let Some(p_val) = prev.get(pi, pj)
                    && let Some(n_val) = next.get(ni, nj)
                    && n_val <= p_val
                {
                    out.mat[i * n + j] = Some(p_val);
                }
            }
        }
        for &(pu, pv, k) in &prev.non_equal {
            if let (Some(&ou), Some(&ov)) = (
                out.index.get(&prev.atoms[pu]),
                out.index.get(&prev.atoms[pv]),
            ) && let Some(c) = Self::canonical_ne(ou, ov, k)
                && next.entails_ne(&out.atoms[c.0], &out.atoms[c.1], c.2)
            {
                out.non_equal.insert(c);
            }
        }
        for &(pu, pv, pw, k) in &prev.sum_le {
            if let (Some(&ou), Some(&ov), Some(&ow)) = (
                out.index.get(&prev.atoms[pu]),
                out.index.get(&prev.atoms[pv]),
                out.index.get(&prev.atoms[pw]),
            ) && next.has_sum_le(&prev.atoms[pu], &prev.atoms[pv], &prev.atoms[pw], k)
            {
                let (x, y) = if ou <= ov { (ou, ov) } else { (ov, ou) };
                out.sum_le.insert((x, y, ow, k));
            }
        }
        out
    }

    /// Floyd-Warshall closure for an unclosed widened DBM.
    pub(super) fn closed(&self) -> Dbm {
        let mut out = self.clone();
        if out.unsat {
            return out;
        }
        let n = out.n();
        for k in 0..n {
            for i in 0..n {
                let Some(ik) = out.mat[i * n + k] else {
                    continue;
                };
                for j in 0..n {
                    let Some(kj) = out.mat[k * n + j] else {
                        continue;
                    };
                    let Some(cand) = ik.checked_add(kj) else {
                        continue;
                    };
                    let cell = &mut out.mat[i * n + j];
                    if cell.is_none_or(|cur| cand < cur) {
                        *cell = Some(cand);
                    }
                }
            }
            if out.mat[k * n + k].is_some_and(|d| d < 0) {
                out.unsat = true;
                return out;
            }
        }
        // Re-assert Len >= 0 axioms in case widening dropped them.
        for i in 1..n {
            if matches!(out.atoms[i], Atom::Len(_)) {
                out.add_le_idx(0, i, 0);
            }
        }
        out.propagate_disequalities();
        out
    }

    /// Returns true iff every constraint in `other` is entailed by `self` (`self <= other` in lattice).
    pub(super) fn is_subsumed_by(&self, other: &Dbm) -> bool {
        if self.unsat {
            return true;
        }
        if other.unsat {
            return false;
        }
        let n = other.n();
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                if let Some(bound) = other.get(i, j)
                    && !self.entails_le(&other.atoms[i], &other.atoms[j], bound)
                {
                    return false;
                }
            }
        }
        for &(u, v, k) in &other.non_equal {
            if !self.entails_ne(&other.atoms[u], &other.atoms[v], k) {
                return false;
            }
        }
        for &(u, v, w, k) in &other.sum_le {
            if !self.has_sum_le(&other.atoms[u], &other.atoms[v], &other.atoms[w], k) {
                return false;
            }
        }
        true
    }

    /// Records `a + b <= c + k` (sliding-window upper bound).
    pub(super) fn add_sum_le(&mut self, a: Atom, b: Atom, c: Atom, k: i128) {
        if self.unsat {
            return;
        }
        let (Some(ua), Some(ub), Some(uc)) = (
            self.ensure_atom(a),
            self.ensure_atom(b),
            self.ensure_atom(c),
        ) else {
            return;
        };
        let (x, y) = if ua <= ub { (ua, ub) } else { (ub, ua) };
        self.sum_le.insert((x, y, uc, k));
    }

    pub(super) fn has_sum_le(&self, a: &Atom, b: &Atom, c: &Atom, k: i128) -> bool {
        if self.unsat {
            return true;
        }
        let (Some(ua), Some(ub), Some(uc)) = (self.atom_idx(a), self.atom_idx(b), self.atom_idx(c))
        else {
            return false;
        };
        let (x, y) = if ua <= ub { (ua, ub) } else { (ub, ua) };
        self.sum_le
            .iter()
            .any(|&(sx, sy, sc, sk)| sx == x && sy == y && sc == uc && sk <= k)
    }

    pub(super) fn sum_upper_bounds(&self, a: &Atom, b: &Atom) -> Vec<(Atom, i128)> {
        let (Some(ua), Some(ub)) = (self.atom_idx(a), self.atom_idx(b)) else {
            return Vec::new();
        };
        let (x, y) = if ua <= ub { (ua, ub) } else { (ub, ua) };
        self.sum_le
            .iter()
            .filter_map(|&(sx, sy, sc, sk)| {
                (sx == x && sy == y).then(|| (self.atoms[sc].clone(), sk))
            })
            .collect()
    }

    /// Existential projection: forgets all constraints on `atom` while preserving all
    /// transitive relations already materialized among remaining atoms.
    pub(super) fn forget(&mut self, atom: &Atom) {
        if self.unsat || *atom == Atom::Zero {
            return;
        }
        let Some(idx) = self.atom_idx(atom) else {
            return;
        };
        let n = self.n();
        for i in 0..n {
            if i != idx {
                self.set(idx, i, None);
                self.set(i, idx, None);
            }
        }
        self.set(idx, idx, Some(0));
        self.non_equal.retain(|&(u, v, _)| u != idx && v != idx);
        self.sum_le
            .retain(|&(a, b, c, _)| a != idx && b != idx && c != idx);
        if matches!(atom, Atom::Len(_)) {
            self.add_le_idx(0, idx, 0);
        }
    }

    /// Remove atoms matching `pred` completely from the matrix (shrinking N, preventing atom cap exhaustion).
    pub(super) fn project_out<F>(&mut self, mut pred: F)
    where
        F: FnMut(&Atom) -> bool,
    {
        if self.unsat {
            return;
        }
        let keep: Vec<usize> = (0..self.atoms.len())
            .filter(|&i| i == 0 || !pred(&self.atoms[i]))
            .collect();
        if keep.len() == self.atoms.len() {
            return;
        }
        let old_n = self.n();
        let new_n = keep.len();
        let mut remap = vec![None; old_n];
        let mut new_atoms = Vec::with_capacity(new_n);
        let mut new_index = HashMap::with_capacity(new_n);
        for (new_i, &old_i) in keep.iter().enumerate() {
            remap[old_i] = Some(new_i);
            let atom = self.atoms[old_i].clone();
            new_index.insert(atom.clone(), new_i);
            new_atoms.push(atom);
        }
        let mut new_mat = vec![None; new_n * new_n];
        for (ni, &oi) in keep.iter().enumerate() {
            for (nj, &oj) in keep.iter().enumerate() {
                new_mat[ni * new_n + nj] = self.mat[oi * old_n + oj];
            }
        }
        let mut new_ne = HashSet::new();
        for &(ou, ov, k) in &self.non_equal {
            if let (Some(nu), Some(nv)) = (remap[ou], remap[ov])
                && let Some(c) = Self::canonical_ne(nu, nv, k)
            {
                new_ne.insert(c);
            }
        }
        let mut new_sum_le = HashSet::new();
        for &(oa, ob, oc, k) in &self.sum_le {
            if let (Some(na), Some(nb), Some(nc)) = (remap[oa], remap[ob], remap[oc]) {
                let (x, y) = if na <= nb { (na, nb) } else { (nb, na) };
                new_sum_le.insert((x, y, nc, k));
            }
        }
        self.atoms = new_atoms;
        self.index = new_index;
        self.mat = new_mat;
        self.non_equal = new_ne;
        self.sum_le = new_sum_le;
    }

    pub(super) fn forget_temps(&mut self) {
        self.project_out(|a| matches!(a, Atom::Temp(_)));
    }

    pub(super) fn forget_matching<F>(&mut self, mut pred: F)
    where
        F: FnMut(&Atom) -> bool,
    {
        if self.unsat {
            return;
        }
        let targets: Vec<Atom> = self
            .atoms
            .iter()
            .skip(1)
            .filter(|a| pred(a))
            .cloned()
            .collect();
        for atom in targets {
            self.forget(&atom);
        }
    }

    /// Atomic update `target := rhs(pre_state)`:
    /// constrains a fresh `Temp` against the pre-update DBM, forgets `target`, then copies `Temp -> target`.
    pub(super) fn assign_via_temp<F>(&mut self, target: Atom, build: F)
    where
        F: FnOnce(&mut Dbm, &Atom),
    {
        if self.unsat || target == Atom::Zero {
            return;
        }
        let temp = self.fresh_temp();
        if self.ensure_atom(temp.clone()).is_none() {
            self.forget(&target);
            return;
        }
        build(self, &temp);
        self.forget(&target);
        self.add_eq(target, temp.clone(), 0);
        self.project_out(|a| *a == temp);
    }

    /// Copies all constraints on `src` onto `dst` (equivalence `dst == src`), then projects out `src` if temporary.
    pub(super) fn copy_atom_eq(&mut self, dst: Atom, src: Atom) {
        if dst != src {
            self.add_eq(dst, src, 0);
        }
    }
}

/// Checks whether a conjunction of `assumptions` semantically entails `target` over difference logic
/// (including `len(p) >= 0` axioms for all `ProofAtom::Len` atoms).
pub(crate) fn preds_entail(
    assumptions: &[ProofPred<ProofAtom>],
    target: &ProofPred<ProofAtom>,
) -> bool {
    let mapped_assumptions: Vec<ProofPred<Atom>> = assumptions
        .iter()
        .filter_map(|p| p.map_atoms(&mut |a| Some(Atom::Proof(a.clone()))))
        .collect();
    let Some(mapped_target) = target.map_atoms(&mut |a| Some(Atom::Proof(a.clone()))) else {
        return false;
    };
    let mut dbm = Dbm::new();
    let mut queue: Vec<ProofPred<Atom>> = mapped_assumptions;
    preds_entail_rec(&mut dbm, &mut queue, &mapped_target, 8)
}

fn preds_entail_rec(
    dbm: &mut Dbm,
    queue: &mut Vec<ProofPred<Atom>>,
    target: &ProofPred<Atom>,
    or_budget: usize,
) -> bool {
    if dbm.unsat {
        return true;
    }
    while let Some(pred) = queue.pop() {
        match pred {
            ProofPred::True => {}
            ProofPred::False => return true,
            ProofPred::DiffLe { lhs, rhs, bound } => {
                let u = lhs.unwrap_or(Atom::Zero);
                let v = rhs.unwrap_or(Atom::Zero);
                dbm.add_le(u, v, bound);
                if dbm.unsat {
                    return true;
                }
            }
            ProofPred::DiffNe { lhs, rhs, offset } => {
                let u = lhs.unwrap_or(Atom::Zero);
                let v = rhs.unwrap_or(Atom::Zero);
                dbm.add_ne(u, v, offset);
                if dbm.unsat {
                    return true;
                }
            }
            ProofPred::And(items) => {
                queue.extend(items);
            }
            ProofPred::Or(items) => {
                if or_budget == 0 || items.len() > 8 {
                    continue;
                }
                return items.into_iter().all(|branch| {
                    let mut branch_dbm = dbm.clone();
                    let mut branch_q = queue.clone();
                    branch_q.push(branch);
                    preds_entail_rec(&mut branch_dbm, &mut branch_q, target, or_budget - 1)
                });
            }
        }
    }
    dbm.entails(target)
}
