//! Finite, canonical Boolean relations used by polymorphic provenance summaries.
//!
//! A relation is a sufficient condition, not a guessed run-time identity.  For
//! example a permutation's two results are disjoint precisely when its two
//! inputs are known disjoint. Keeping that condition avoids losing correlations
//! when each result has the same may-origin set.
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pivot(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Atom {
    Equal(Pivot, Pivot),
    Disjoint(Pivot, Pivot),
}

impl Atom {
    pub fn equal(a: Pivot, b: Pivot) -> Self {
        Self::Equal(a.min(b), a.max(b))
    }
    pub fn disjoint(a: Pivot, b: Pivot) -> Self {
        Self::Disjoint(a.min(b), a.max(b))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Condition(pub u32);
impl Condition {
    pub const FALSE: Self = Self(0);
    pub const TRUE: Self = Self(1);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Decision {
    atom: Atom,
    low: Condition,
    high: Condition,
}

/// Reduced ordered BDD. Its variables are the finite summary interface pivots.
/// Local paths and recursive calls never become new Boolean variables.
#[derive(Debug, Clone, Default)]
pub struct Conditions {
    nodes: Vec<Decision>,
    interned: HashMap<Decision, Condition>,
    and_cache: HashMap<(Condition, Condition), Condition>,
    or_cache: HashMap<(Condition, Condition), Condition>,
}

impl Conditions {
    pub fn decisions(&self) -> impl Iterator<Item = (Condition, Atom, Condition, Condition)> + '_ {
        self.nodes
            .iter()
            .enumerate()
            .map(|(index, node)| (Condition(index as u32 + 2), node.atom, node.low, node.high))
    }
    fn decision(&self, condition: Condition) -> Option<Decision> {
        condition.0.checked_sub(2).map(|i| self.nodes[i as usize])
    }
    fn node(&mut self, atom: Atom, low: Condition, high: Condition) -> Condition {
        if low == high {
            return low;
        }
        let decision = Decision { atom, low, high };
        if let Some(id) = self.interned.get(&decision) {
            return *id;
        }
        let id = Condition(self.nodes.len() as u32 + 2);
        self.nodes.push(decision);
        self.interned.insert(decision, id);
        id
    }
    pub fn atom(&mut self, atom: Atom) -> Condition {
        match atom {
            Atom::Equal(a, b) if a == b => Condition::TRUE,
            Atom::Disjoint(a, b) if a == b => Condition::FALSE,
            _ => self.node(atom, Condition::FALSE, Condition::TRUE),
        }
    }
    pub fn and(&mut self, a: Condition, b: Condition) -> Condition {
        if a == Condition::FALSE || b == Condition::FALSE {
            return Condition::FALSE;
        }
        if a == Condition::TRUE || a == b {
            return b;
        }
        if b == Condition::TRUE {
            return a;
        }
        let key = if a.0 < b.0 { (a, b) } else { (b, a) };
        if let Some(result) = self.and_cache.get(&key) {
            return *result;
        }
        let left = self.decision(a).expect("nonterminal condition");
        let right = self.decision(b).expect("nonterminal condition");
        let atom = left.atom.min(right.atom);
        let (al, ah) = if left.atom == atom {
            (left.low, left.high)
        } else {
            (a, a)
        };
        let (bl, bh) = if right.atom == atom {
            (right.low, right.high)
        } else {
            (b, b)
        };
        let low = self.and(al, bl);
        let high = self.and(ah, bh);
        let result = self.node(atom, low, high);
        self.and_cache.insert(key, result);
        result
    }
    pub fn or(&mut self, a: Condition, b: Condition) -> Condition {
        if a == Condition::TRUE || b == Condition::TRUE {
            return Condition::TRUE;
        }
        if a == Condition::FALSE || a == b {
            return b;
        }
        if b == Condition::FALSE {
            return a;
        }
        let key = if a.0 < b.0 { (a, b) } else { (b, a) };
        if let Some(result) = self.or_cache.get(&key) {
            return *result;
        }
        let left = self.decision(a).expect("nonterminal condition");
        let right = self.decision(b).expect("nonterminal condition");
        let atom = left.atom.min(right.atom);
        let (al, ah) = if left.atom == atom {
            (left.low, left.high)
        } else {
            (a, a)
        };
        let (bl, bh) = if right.atom == atom {
            (right.low, right.high)
        } else {
            (b, b)
        };
        let low = self.or(al, bl);
        let high = self.or(ah, bh);
        let result = self.node(atom, low, high);
        self.or_cache.insert(key, result);
        result
    }
    pub fn evaluate(&self, condition: Condition, known: &impl Fn(Atom) -> bool) -> bool {
        match self.decision(condition) {
            None => condition == Condition::TRUE,
            Some(node) => self.evaluate(
                if known(node.atom) {
                    node.high
                } else {
                    node.low
                },
                known,
            ),
        }
    }
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Relation {
    pub equal: Condition,
    pub disjoint: Condition,
}
impl Relation {
    pub const UNKNOWN: Self = Self {
        equal: Condition::FALSE,
        disjoint: Condition::FALSE,
    };
    pub const EQUAL: Self = Self {
        equal: Condition::TRUE,
        disjoint: Condition::FALSE,
    };
    pub const DISJOINT: Self = Self {
        equal: Condition::FALSE,
        disjoint: Condition::TRUE,
    };
    pub fn symbolic(conditions: &mut Conditions, a: Pivot, b: Pivot) -> Self {
        Self {
            equal: conditions.atom(Atom::equal(a, b)),
            disjoint: conditions.atom(Atom::disjoint(a, b)),
        }
    }
    /// Join aligned predecessor pairs, never the Cartesian product of their
    /// independently flattened may-origin sets.
    pub fn join(self, other: Self, conditions: &mut Conditions) -> Self {
        Self {
            equal: conditions.and(self.equal, other.equal),
            disjoint: conditions.and(self.disjoint, other.disjoint),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn permutation_retains_conditional_disjointness() {
        let mut bdd = Conditions::default();
        let ab = Relation::symbolic(&mut bdd, Pivot(0), Pivot(1));
        let ba = Relation::symbolic(&mut bdd, Pivot(1), Pivot(0));
        let joined = ab.join(ba, &mut bdd);
        assert_eq!(joined, ab);
        assert!(bdd.evaluate(joined.disjoint, &|a| matches!(a, Atom::Disjoint(_, _))));
        assert!(!bdd.evaluate(joined.disjoint, &|_| false));
        assert_eq!(
            joined.join(Relation::EQUAL, &mut bdd).disjoint,
            Condition::FALSE
        );
    }
    #[test]
    fn canonical_boolean_operations_are_order_independent() {
        let mut bdd = Conditions::default();
        let a = bdd.atom(Atom::equal(Pivot(0), Pivot(1)));
        let b = bdd.atom(Atom::disjoint(Pivot(1), Pivot(2)));
        let c = bdd.atom(Atom::equal(Pivot(2), Pivot(3)));
        let ab = bdd.and(a, b);
        let ba = bdd.and(b, a);
        assert_eq!(ab, ba);
        let abc = bdd.and(ab, c);
        let bc = bdd.and(b, c);
        assert_eq!(abc, bdd.and(a, bc));
        assert_eq!(bdd.and(a, a), a);
        assert_eq!(bdd.or(a, a), a);
        let a_or_b = bdd.or(a, b);
        assert_eq!(bdd.and(a, a_or_b), a);
    }
}
