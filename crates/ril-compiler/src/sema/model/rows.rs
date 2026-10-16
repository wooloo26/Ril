//! Finite row constraints, independent of value provenance and authority.
//!
//! Open tails are never empty by default. A successful type-row equation does
//! not establish anything about unknown members' Results, resources, callables,
//! origins or permissions; those obligations belong to the semantic checker.
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RowIdentity {
    Binder(String),
    Fresh { owner: String, ordinal: u64 },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenTail {
    pub identity: RowIdentity,
    /// Required label absences. A rigid tail needs independently registered
    /// declaration facts; an equality cannot assume new absences for it.
    pub lacks: BTreeSet<String>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowTail {
    Closed,
    Open(OpenTail),
}
pub type Field<F> = (bool, F);
pub type Fields<F> = BTreeMap<String, Field<F>>;
pub type FieldPair<F> = (Field<F>, Field<F>);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row<F> {
    pub fields: Fields<F>,
    pub tail: RowTail,
}
impl<F> Row<F> {
    pub fn closed(fields: Fields<F>) -> Self {
        Self {
            fields,
            tail: RowTail::Closed,
        }
    }
    pub fn open(fields: Fields<F>, mut tail: OpenTail) -> Self {
        tail.lacks.extend(fields.keys().cloned());
        Self {
            fields,
            tail: RowTail::Open(tail),
        }
    }
    pub fn is_closed(&self) -> bool {
        matches!(self.tail, RowTail::Closed)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDifference<F> {
    pub left_only: Fields<F>,
    pub right_only: Fields<F>,
    pub common: BTreeMap<String, FieldPair<F>>,
}
pub fn field_difference<F: Clone>(left: &Fields<F>, right: &Fields<F>) -> FieldDifference<F> {
    let mut result = FieldDifference {
        left_only: Fields::new(),
        right_only: Fields::new(),
        common: BTreeMap::new(),
    };
    for (name, field) in left {
        if let Some(other) = right.get(name) {
            result
                .common
                .insert(name.clone(), (field.clone(), other.clone()));
        } else {
            result.left_only.insert(name.clone(), field.clone());
        }
    }
    for (name, field) in right {
        if !left.contains_key(name) {
            result.right_only.insert(name.clone(), field.clone());
        }
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowError {
    Overlap(BTreeSet<String>),
    FieldType(String),
    FieldMutability(String),
    Labels {
        left_only: BTreeSet<String>,
        right_only: BTreeSet<String>,
    },
    Lacks {
        row: RowIdentity,
        label: String,
    },
    Rigid(RowIdentity),
    UnprovedAbsence {
        row: RowIdentity,
        labels: BTreeSet<String>,
    },
    Occurs(RowIdentity),
    RoleConflict(RowIdentity),
    Budget,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Overlap {
    pub definite: BTreeSet<String>,
    pub possible_labels: BTreeSet<String>,
    /// Two unknown tails may share labels beyond every finite lacks set.
    pub symbolic: BTreeSet<(RowIdentity, RowIdentity)>,
}
impl Overlap {
    pub fn proved_disjoint(&self) -> bool {
        self.definite.is_empty() && self.possible_labels.is_empty() && self.symbolic.is_empty()
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RemovalPlan<F> {
    pub known: Fields<F>,
    pub tail: RowTail,
    /// Removing these labels from an unknown tail would change its identity.
    /// Do not materialize `known + tail` as the exact result until resolved.
    pub pending: BTreeSet<String>,
}
impl<F> RemovalPlan<F> {
    pub fn exact(self) -> Option<Row<F>> {
        self.pending.is_empty().then_some(Row {
            fields: self.known,
            tail: self.tail,
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionPlan<F> {
    pub known: Fields<F>,
    pub tails: Vec<OpenTail>,
    pub overlap: Overlap,
    pub pending_removals: BTreeMap<RowIdentity, BTreeSet<String>>,
}
impl<F> UnionPlan<F> {
    pub fn exact(self) -> Option<Row<F>> {
        if !self.overlap.proved_disjoint() || !self.pending_removals.is_empty() {
            return None;
        }
        match self.tails.as_slice() {
            [] => Some(Row::closed(self.known)),
            [tail] => Some(Row::open(self.known, tail.clone())),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Solver<F> {
    owner: String,
    next_residual: u64,
    flexible: BTreeSet<RowIdentity>,
    bindings: BTreeMap<RowIdentity, Row<F>>,
    lacks: BTreeMap<RowIdentity, BTreeSet<String>>,
    budget: usize,
}
struct Budget(usize);
impl Budget {
    fn charge(&mut self, amount: usize) -> Result<(), RowError> {
        self.0 = self.0.checked_sub(amount).ok_or(RowError::Budget)?;
        Ok(())
    }
}
impl<F: Clone + Eq> Solver<F> {
    pub fn new(owner: impl Into<String>, flexible: impl IntoIterator<Item = RowIdentity>) -> Self {
        Self {
            owner: owner.into(),
            next_residual: 0,
            flexible: flexible.into_iter().collect(),
            bindings: BTreeMap::new(),
            lacks: BTreeMap::new(),
            budget: 4096,
        }
    }
    pub fn with_budget(mut self, budget: usize) -> Self {
        self.budget = budget;
        self
    }
    /// These facts come from a checked declaration contract, not a value
    /// spread or the equality currently being attempted.
    pub fn declare_rigid(
        &mut self,
        identity: RowIdentity,
        lacks: impl IntoIterator<Item = String>,
    ) -> Result<(), RowError> {
        if self.flexible.contains(&identity) {
            return Err(RowError::RoleConflict(identity));
        }
        self.lacks.entry(identity).or_default().extend(lacks);
        Ok(())
    }
    pub fn binding(&self, identity: &RowIdentity) -> Option<&Row<F>> {
        self.bindings.get(identity)
    }
    pub fn required_absences(&self, identity: &RowIdentity) -> BTreeSet<String> {
        self.lacks.get(identity).cloned().unwrap_or_default()
    }
    fn fresh(&mut self) -> RowIdentity {
        let identity = RowIdentity::Fresh {
            owner: self.owner.clone(),
            ordinal: self.next_residual,
        };
        self.next_residual += 1;
        self.flexible.insert(identity.clone());
        identity
    }
    fn require_absent(
        &mut self,
        identity: &RowIdentity,
        labels: &BTreeSet<String>,
        budget: &mut Budget,
    ) -> Result<(), RowError> {
        let mut work = vec![(identity.clone(), labels.clone())];
        let mut seen = BTreeSet::new();
        while let Some((identity, labels)) = work.pop() {
            budget.charge(labels.len() + 1)?;
            if !seen.insert(identity.clone()) {
                return Err(RowError::Occurs(identity));
            }
            let previous = self.required_absences(&identity);
            let additional: BTreeSet<_> = labels.difference(&previous).cloned().collect();
            if !additional.is_empty() && !self.flexible.contains(&identity) {
                return Err(RowError::UnprovedAbsence {
                    row: identity,
                    labels: additional,
                });
            }
            self.lacks
                .entry(identity.clone())
                .or_default()
                .extend(labels.iter().cloned());
            if let Some(binding) = self.bindings.get(&identity) {
                if let Some(label) = labels
                    .iter()
                    .find(|label| binding.fields.contains_key(*label))
                {
                    return Err(RowError::Lacks {
                        row: identity,
                        label: label.clone(),
                    });
                }
                if let RowTail::Open(tail) = &binding.tail {
                    work.push((tail.identity.clone(), labels));
                }
            }
        }
        Ok(())
    }
    fn prepare(&mut self, row: &Row<F>, budget: &mut Budget) -> Result<(), RowError> {
        budget.charge(row.fields.len() + 1)?;
        if let RowTail::Open(tail) = &row.tail {
            let mut lacks = tail.lacks.clone();
            lacks.extend(row.fields.keys().cloned());
            self.require_absent(&tail.identity, &lacks, budget)?;
        }
        Ok(())
    }
    fn resolve(&self, row: &Row<F>, budget: &mut Budget) -> Result<Row<F>, RowError> {
        let mut row = row.clone();
        let mut seen = BTreeSet::new();
        loop {
            budget.charge(1)?;
            let RowTail::Open(tail) = &row.tail else {
                return Ok(row);
            };
            let mut tail = tail.clone();
            tail.lacks.extend(self.required_absences(&tail.identity));
            tail.lacks.extend(row.fields.keys().cloned());
            if !seen.insert(tail.identity.clone()) {
                return Err(RowError::Occurs(tail.identity));
            }
            let Some(binding) = self.bindings.get(&tail.identity) else {
                row.tail = RowTail::Open(tail);
                return Ok(row);
            };
            budget.charge(binding.fields.len())?;
            if let Some(label) = binding
                .fields
                .keys()
                .find(|label| tail.lacks.contains(*label))
            {
                return Err(RowError::Lacks {
                    row: tail.identity,
                    label: label.clone(),
                });
            }
            let overlap: BTreeSet<_> = binding
                .fields
                .keys()
                .filter(|label| row.fields.contains_key(*label))
                .cloned()
                .collect();
            if !overlap.is_empty() {
                return Err(RowError::Overlap(overlap));
            }
            row.fields.extend(binding.fields.clone());
            row.tail = binding.tail.clone();
            if let RowTail::Open(next) = &mut row.tail {
                next.lacks.extend(tail.lacks);
            }
        }
    }
    pub fn normalize(&self, row: &Row<F>) -> Result<Row<F>, RowError> {
        let mut trial = self.clone();
        let mut budget = Budget(self.budget);
        trial.prepare(row, &mut budget)?;
        trial.resolve(row, &mut budget)
    }
    fn normalized_pair(&self, left: &Row<F>, right: &Row<F>) -> Result<(Row<F>, Row<F>), RowError> {
        let mut trial = self.clone();
        let mut budget = Budget(self.budget);
        trial.prepare(left, &mut budget)?;
        trial.prepare(right, &mut budget)?;
        Ok((
            trial.resolve(left, &mut budget)?,
            trial.resolve(right, &mut budget)?,
        ))
    }
    fn bind(
        &mut self,
        identity: &RowIdentity,
        row: Row<F>,
        budget: &mut Budget,
    ) -> Result<(), RowError> {
        if !self.flexible.contains(identity) {
            return Err(RowError::Rigid(identity.clone()));
        }
        self.prepare(&row, budget)?;
        let mut row = self.resolve(&row, budget)?;
        if let RowTail::Open(tail) = &row.tail
            && &tail.identity == identity
        {
            if row.fields.is_empty() {
                return self.require_absent(identity, &tail.lacks, budget);
            }
            return Err(RowError::Occurs(identity.clone()));
        }
        let lacks = self.required_absences(identity);
        if let Some(label) = lacks.iter().find(|label| row.fields.contains_key(*label)) {
            return Err(RowError::Lacks {
                row: identity.clone(),
                label: label.clone(),
            });
        }
        if let RowTail::Open(tail) = &mut row.tail {
            self.require_absent(&tail.identity, &lacks, budget)?;
            tail.lacks.extend(lacks);
        }
        self.bindings.insert(identity.clone(), row);
        Ok(())
    }
    /// Exact field equality is invariant, including the slot-replacement bit.
    /// B's type unifier must solve ordinary field-type equations beforehand.
    pub fn unify(&mut self, left: &Row<F>, right: &Row<F>) -> Result<Row<F>, RowError> {
        let mut trial = self.clone();
        let mut budget = Budget(self.budget);
        trial.prepare(left, &mut budget)?;
        trial.prepare(right, &mut budget)?;
        let left = trial.resolve(left, &mut budget)?;
        let right = trial.resolve(right, &mut budget)?;
        let difference = field_difference(&left.fields, &right.fields);
        budget.charge(left.fields.len() + right.fields.len() + 1)?;
        for (name, (a, b)) in &difference.common {
            if a.0 != b.0 {
                return Err(RowError::FieldMutability(name.clone()));
            }
            if a.1 != b.1 {
                return Err(RowError::FieldType(name.clone()));
            }
        }
        let mismatch = || RowError::Labels {
            left_only: difference.left_only.keys().cloned().collect(),
            right_only: difference.right_only.keys().cloned().collect(),
        };
        match (&left.tail, &right.tail) {
            (RowTail::Closed, RowTail::Closed) => {
                if !difference.left_only.is_empty() || !difference.right_only.is_empty() {
                    return Err(mismatch());
                }
            }
            (RowTail::Open(tail), RowTail::Closed) => {
                if !difference.left_only.is_empty() {
                    return Err(mismatch());
                }
                trial.bind(
                    &tail.identity,
                    Row::closed(difference.right_only.clone()),
                    &mut budget,
                )?;
            }
            (RowTail::Closed, RowTail::Open(tail)) => {
                if !difference.right_only.is_empty() {
                    return Err(mismatch());
                }
                trial.bind(
                    &tail.identity,
                    Row::closed(difference.left_only.clone()),
                    &mut budget,
                )?;
            }
            (RowTail::Open(a), RowTail::Open(b)) if a.identity == b.identity => {
                if !difference.left_only.is_empty() || !difference.right_only.is_empty() {
                    return Err(mismatch());
                }
            }
            (RowTail::Open(a), RowTail::Open(b)) => {
                let af = trial.flexible.contains(&a.identity);
                let bf = trial.flexible.contains(&b.identity);
                match (af, bf) {
                    (true, true) => {
                        let residual = trial.fresh();
                        let mut lacks = trial.required_absences(&a.identity);
                        lacks.extend(trial.required_absences(&b.identity));
                        lacks.extend(left.fields.keys().cloned());
                        lacks.extend(right.fields.keys().cloned());
                        let tail = OpenTail {
                            identity: residual,
                            lacks,
                        };
                        trial.bind(
                            &a.identity,
                            Row::open(difference.right_only.clone(), tail.clone()),
                            &mut budget,
                        )?;
                        trial.bind(
                            &b.identity,
                            Row::open(difference.left_only.clone(), tail),
                            &mut budget,
                        )?;
                    }
                    (true, false) if difference.left_only.is_empty() => {
                        trial.bind(
                            &a.identity,
                            Row::open(difference.right_only.clone(), b.clone()),
                            &mut budget,
                        )?;
                    }
                    (false, true) if difference.right_only.is_empty() => {
                        trial.bind(
                            &b.identity,
                            Row::open(difference.left_only.clone(), a.clone()),
                            &mut budget,
                        )?;
                    }
                    _ => {
                        return Err(RowError::Rigid(if af {
                            b.identity.clone()
                        } else {
                            a.identity.clone()
                        }));
                    }
                }
            }
        }
        let result = trial.resolve(&left, &mut budget)?;
        if result != trial.resolve(&right, &mut budget)? {
            return Err(mismatch());
        }
        *self = trial;
        Ok(result)
    }
    pub fn overlap(&self, left: &Row<F>, right: &Row<F>) -> Result<Overlap, RowError> {
        let (left, right) = self.normalized_pair(left, right)?;
        let mut result = Overlap::default();
        for label in left.fields.keys() {
            if right.fields.contains_key(label) {
                result.definite.insert(label.clone());
            } else if let RowTail::Open(tail) = &right.tail
                && !tail.lacks.contains(label)
            {
                result.possible_labels.insert(label.clone());
            }
        }
        if let RowTail::Open(tail) = &left.tail {
            for label in right.fields.keys() {
                if !left.fields.contains_key(label) && !tail.lacks.contains(label) {
                    result.possible_labels.insert(label.clone());
                }
            }
        }
        if let (RowTail::Open(a), RowTail::Open(b)) = (&left.tail, &right.tail) {
            let pair = if a.identity <= b.identity {
                (a.identity.clone(), b.identity.clone())
            } else {
                (b.identity.clone(), a.identity.clone())
            };
            result.symbolic.insert(pair);
        }
        Ok(result)
    }
    pub fn remove(
        &self,
        row: &Row<F>,
        labels: &BTreeSet<String>,
    ) -> Result<RemovalPlan<F>, RowError> {
        let mut row = self.normalize(row)?;
        for label in labels {
            row.fields.remove(label);
        }
        let pending = if let RowTail::Open(tail) = &row.tail {
            labels.difference(&tail.lacks).cloned().collect()
        } else {
            BTreeSet::new()
        };
        Ok(RemovalPlan {
            known: row.fields,
            tail: row.tail,
            pending,
        })
    }
    pub fn union(
        &self,
        left: &Row<F>,
        right: &Row<F>,
        overrides: &Fields<F>,
    ) -> Result<UnionPlan<F>, RowError> {
        let (left, right) = self.normalized_pair(left, right)?;
        let mut overlap = self.overlap(&left, &right)?;
        overlap
            .definite
            .retain(|label| !overrides.contains_key(label));
        overlap
            .possible_labels
            .retain(|label| !overrides.contains_key(label));
        if !overlap.definite.is_empty() {
            return Err(RowError::Overlap(overlap.definite));
        }
        let mut known = left.fields;
        known.extend(right.fields);
        known.extend(overrides.clone());
        let tails: Vec<_> = [left.tail, right.tail]
            .into_iter()
            .filter_map(|tail| {
                if let RowTail::Open(tail) = tail {
                    Some(tail)
                } else {
                    None
                }
            })
            .collect();
        let mut pending_removals = BTreeMap::new();
        for tail in &tails {
            let removed: BTreeSet<_> = overrides
                .keys()
                .filter(|label| !tail.lacks.contains(*label))
                .cloned()
                .collect();
            if !removed.is_empty() {
                pending_removals.insert(tail.identity.clone(), removed);
            }
        }
        Ok(UnionPlan {
            known,
            tails,
            overlap,
            pending_removals,
        })
    }
}

#[cfg(test)]
mod tests;
