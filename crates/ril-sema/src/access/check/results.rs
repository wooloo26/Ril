use std::collections::BTreeSet;

use ril_frontend::syntax::{Pattern, PatternId};

use super::{Access, Analyzer, Context, Coordinate, Datum, Ledger};
use crate::access::flow::ResultOccurrence;

type Inspections = BTreeSet<ResultOccurrence>;

pub(super) struct PatternTests {
    pub matched: Option<Inspections>,
    pub missed: Option<Inspections>,
}

impl PatternTests {
    fn test(outcome: Option<bool>, inspected: Inspections) -> Self {
        Self {
            matched: (outcome != Some(false)).then(|| inspected.clone()),
            missed: (outcome != Some(true)).then_some(inspected),
        }
    }

    pub(super) fn inspect(&self, ledger: &mut Ledger, matched: bool) -> bool {
        let selected = if matched { &self.matched } else { &self.missed };
        if let Some(inspected) = selected {
            ledger.inspected.extend(inspected.iter().cloned());
            true
        } else {
            false
        }
    }

    // A failing prefix prevents subsequent tests from executing. Intersect
    // their inspections when several paths reach the same outcome.
    fn and(self, other: impl FnOnce() -> Self) -> Self {
        let Some(prefix) = self.matched else {
            return self;
        };
        let next = other().after(&prefix);
        Self {
            matched: next.matched,
            missed: alternatives(self.missed, next.missed),
        }
    }

    fn or(self, other: impl FnOnce() -> Self) -> Self {
        let Some(prefix) = self.missed else {
            return self;
        };
        let next = other().after(&prefix);
        Self {
            matched: alternatives(self.matched, next.matched),
            missed: next.missed,
        }
    }

    pub(super) fn after(mut self, prior: &Inspections) -> Self {
        for inspected in self.matched.iter_mut().chain(&mut self.missed) {
            inspected.extend(prior.iter().cloned());
        }
        self
    }
}

pub(super) fn alternatives(
    left: Option<Inspections>,
    right: Option<Inspections>,
) -> Option<Inspections> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.intersection(&right).cloned().collect()),
        (left, right) => left.or(right),
    }
}

impl Analyzer<'_> {
    pub(super) fn pattern_paths(
        &self,
        ctx: &Context,
        ledger: &Ledger,
        id: PatternId,
        value: &Datum,
        matched: bool,
    ) -> Vec<(Ledger, Datum)> {
        let mut paths = ledger.variant_paths(value);
        if paths.is_empty() {
            paths.push((ledger.clone(), value.clone()));
        }
        paths.retain_mut(|(inside, selected)| {
            self.pattern_tests(ctx, inside, id, selected)
                .inspect(inside, matched)
        });
        paths
    }

    pub(super) fn pattern_tests(
        &self,
        ctx: &Context,
        ledger: &Ledger,
        id: PatternId,
        value: &Datum,
    ) -> PatternTests {
        let ast = self.ast(ctx.file);
        let node = ast.pattern(id);
        let certain = || PatternTests::test(Some(true), Inspections::new());
        let uncertain = || PatternTests::test(None, Inspections::new());
        let child = |id, coordinate, mode| {
            let projected = ledger.project_schema(value, coordinate, mode);
            self.pattern_tests(ctx, ledger, id, &projected)
        };
        match &node.value {
            Pattern::Binding(..) | Pattern::Wildcard | Pattern::Rest(_) | Pattern::Unit => {
                certain()
            }
            Pattern::Constructor(path, payload) => {
                let name = path
                    .segments
                    .last()
                    .map_or("", |seg| seg.name.value.as_str());
                let input = self.ty(node.span);
                let tag = value.known_variant().map(|variant| variant == name);
                let tests = if input.is_result() {
                    PatternTests::test(tag, value.root_results())
                } else {
                    PatternTests::test(tag, Inspections::new())
                };
                payload
                    .iter()
                    .flatten()
                    .enumerate()
                    .fold(tests, |tests, (index, &id)| {
                        tests.and(|| {
                            child(
                                id,
                                Coordinate::Index(index.to_string()),
                                Access::Immutable.as_mode(),
                            )
                        })
                    })
            }
            Pattern::Tuple(items) => {
                items
                    .iter()
                    .enumerate()
                    .fold(certain(), |tests, (index, &id)| {
                        tests.and(|| {
                            let coordinate = Coordinate::Index(index.to_string());
                            let (mode, _) = self.schema_mode(self.ty(node.span), &coordinate);
                            child(id, coordinate, mode)
                        })
                    })
            }
            Pattern::Record { fields, .. } => fields.iter().fold(certain(), |tests, field| {
                tests.and(|| {
                    field.pattern.map_or_else(certain, |id| {
                        let coordinate = Coordinate::Field(field.name.value.clone());
                        let (mode, _) = self.schema_mode(self.ty(node.span), &coordinate);
                        child(id, coordinate, mode)
                    })
                })
            }),
            Pattern::Slice { elements, .. } => {
                let (before, _, after) = ast.slice_parts(elements);
                let (mode, _) = self.schema_mode(self.ty(node.span), &Coordinate::Dynamic);
                let tests = before
                    .iter()
                    .enumerate()
                    .fold(uncertain(), |tests, (index, &id)| {
                        tests.and(|| child(id, Coordinate::Index(index.to_string()), mode))
                    });
                after.iter().fold(tests, |tests, &id| {
                    tests.and(|| child(id, Coordinate::Dynamic, mode))
                })
            }
            Pattern::Or(items) => items.iter().fold(
                PatternTests::test(Some(false), Inspections::new()),
                |tests, &id| tests.or(|| self.pattern_tests(ctx, ledger, id, value)),
            ),
            Pattern::Subset {
                binding: Some(id), ..
            } => uncertain().and(|| self.pattern_tests(ctx, ledger, *id, value)),
            _ => uncertain(),
        }
    }
}
