use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Rule<A> {
    pub premises: Vec<A>,
    pub conclusion: A,
}

pub fn solve<A: Clone + Ord>(rules: &[Rule<A>]) -> BTreeSet<A> {
    let mut waiting = BTreeMap::<&A, Vec<usize>>::new();
    let mut unmet = Vec::with_capacity(rules.len());
    let mut ready = VecDeque::new();
    for (index, rule) in rules.iter().enumerate() {
        let distinct: BTreeSet<_> = rule.premises.iter().collect();
        unmet.push(distinct.len());
        if distinct.is_empty() {
            ready.push_back(&rule.conclusion);
        }
        for premise in distinct {
            waiting.entry(premise).or_default().push(index);
        }
    }
    let mut facts = BTreeSet::new();
    while let Some(fact) = ready.pop_front() {
        if facts.insert(fact.clone())
            && let Some(dependent) = waiting.remove(fact)
        {
            for index in dependent {
                let count = unmet
                    .get_mut(index)
                    .unwrap_or_else(|| ril_base::ice!("invalid Horn rule index"));
                *count -= 1;
                if *count == 0 {
                    let rule = rules
                        .get(index)
                        .unwrap_or_else(|| ril_base::ice!("missing Horn rule"));
                    ready.push_back(&rule.conclusion);
                }
            }
        }
    }
    facts
}

pub fn oracle_input<A: Ord>(rules: &[Rule<A>]) -> Vec<Rule<usize>> {
    let domain: BTreeSet<_> = rules
        .iter()
        .flat_map(|rule| {
            rule.premises
                .iter()
                .chain(std::iter::once(&rule.conclusion))
        })
        .collect();
    let index: BTreeMap<_, _> = domain
        .into_iter()
        .enumerate()
        .map(|(i, fact)| (fact, i))
        .collect();
    let number = |atom| {
        *index
            .get(atom)
            .unwrap_or_else(|| ril_base::ice!("Horn atom missing from exported domain"))
    };
    rules
        .iter()
        .map(|rule| Rule {
            conclusion: number(&rule.conclusion),
            premises: rule.premises.iter().map(number).collect(),
        })
        .collect()
}
