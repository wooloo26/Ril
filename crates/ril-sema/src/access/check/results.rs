use std::collections::{BTreeMap, BTreeSet};

use ril_base::span::Span;
use ril_frontend::{
    hir::DefinitionId,
    syntax::{Mode, Pattern, PatternId},
};

use super::{Access, Analyzer, Context, Coordinate, Datum, Ledger, Ty};
use crate::access::flow::{Choices, Occurrence, Region, ResultOccurrence};
use crate::ty::TypedProgram;

type Inspections = BTreeSet<ResultOccurrence>;

pub(super) fn receive_results(
    program: &TypedProgram,
    ledger: &mut Ledger,
    ty: &Ty,
    mut value: Datum,
    span: Span,
) -> Datum {
    if carries_result(program, ty) {
        value.forget_results();
        let choices = ledger.choices.clone();
        value = BoundaryResults {
            program,
            span,
            next_part: 0,
            objects: BTreeMap::new(),
            active: Vec::new(),
        }
        .receive(ledger, ty, value, &choices);
    }
    value
}

pub(super) fn carries_result(program: &TypedProgram, ty: &Ty) -> bool {
    fn visit(program: &TypedProgram, ty: &Ty, active: &mut BTreeSet<DefinitionId>) -> bool {
        match ty {
            Ty::Result(..) => true,
            Ty::Option(inner) => visit(program, inner, active),
            Ty::Tuple(members) => members
                .iter()
                .any(|member| visit(program, &member.ty, active)),
            Ty::Record(fields, _) => fields
                .values()
                .any(|member| visit(program, &member.ty, active)),
            Ty::Adt(adt) if active.insert(adt.definition) => {
                let result = program
                    .nominal_layout(adt)
                    .is_some_and(|layout| visit(program, &layout, active));
                active.remove(&adt.definition);
                result
            }
            _ => false,
        }
    }
    visit(program, ty, &mut BTreeSet::new())
}

struct BoundaryResults<'a> {
    program: &'a TypedProgram,
    span: Span,
    next_part: usize,
    objects: BTreeMap<(Region, Choices), usize>,
    active: Vec<(DefinitionId, BTreeSet<Region>)>,
}

impl BoundaryResults<'_> {
    fn part(&mut self) -> usize {
        let part = self.next_part;
        self.next_part += 1;
        part
    }

    fn receive(
        &mut self,
        ledger: &mut Ledger,
        ty: &Ty,
        mut value: Datum,
        choices: &Choices,
    ) -> Datum {
        match ty {
            Ty::Result(ok, error) => {
                let next = self.part();
                let part = value.result_object().map_or(next, |object| {
                    *self
                        .objects
                        .entry((object.clone(), choices.clone()))
                        .or_insert(next)
                });
                ledger.record_result_part(&mut value, self.span, part, choices);
                if carries_result(self.program, ok) || carries_result(self.program, error) {
                    return self.sum(
                        ledger,
                        value,
                        [("Ok", Some(ok)), ("Err", Some(error))],
                        choices,
                    );
                }
            }
            Ty::Option(inner) if carries_result(self.program, inner) => {
                return self.sum(
                    ledger,
                    value,
                    [("Some", Some(inner)), ("None", None)],
                    choices,
                );
            }
            Ty::Tuple(items) => {
                for (index, member) in items.iter().enumerate() {
                    self.member(
                        ledger,
                        &mut value,
                        Coordinate::Index(index.to_string()),
                        &member.ty,
                        member.mode.mode,
                        choices,
                    );
                }
            }
            Ty::Record(fields, _) => {
                for (field, member) in fields {
                    self.member(
                        ledger,
                        &mut value,
                        Coordinate::Field(field.clone()),
                        &member.ty,
                        member.mode.mode,
                        choices,
                    );
                }
            }
            Ty::Adt(adt) => {
                let Some(layout) = self.program.nominal_layout(adt) else {
                    return value;
                };
                let roots = value.roots.iter().map(|root| root.region.clone()).collect();
                // Follow materialized recursive edges without unfolding an
                // unknown tail or walking the same object through a cycle.
                if self.active.iter().any(|(definition, prior)| {
                    *definition == adt.definition && (value.members.is_empty() || prior == &roots)
                }) {
                    return value;
                }
                self.active.push((adt.definition, roots));
                if matches!(layout, Ty::Record(..) | Ty::Tuple(_)) {
                    value = self.receive(ledger, &layout, value, choices);
                } else {
                    self.member(
                        ledger,
                        &mut value,
                        Coordinate::Index("0".into()),
                        &layout,
                        Mode::Plain,
                        choices,
                    );
                }
                self.active.pop();
            }
            _ => {}
        }
        value
    }

    fn sum(
        &mut self,
        ledger: &mut Ledger,
        value: Datum,
        variants: [(&str, Option<&Ty>); 2],
        choices: &Choices,
    ) -> Datum {
        let key = Occurrence::discriminant(self.span, self.part());
        variants
            .into_iter()
            .enumerate()
            .map(|(arm, (tag, ty))| {
                let mut selected = value.clone();
                selected.choose_variant(tag, key, arm);
                if let Some(ty) = ty {
                    let mut choices = choices.clone();
                    choices.insert(key, arm);
                    self.member(
                        ledger,
                        &mut selected,
                        Coordinate::Index("0".into()),
                        ty,
                        Mode::Plain,
                        &choices,
                    );
                }
                selected
            })
            .reduce(Datum::joined)
            .unwrap_or(value)
    }

    fn member(
        &mut self,
        ledger: &mut Ledger,
        value: &mut Datum,
        coordinate: Coordinate,
        ty: &Ty,
        mode: Mode,
        choices: &Choices,
    ) {
        if carries_result(self.program, ty) {
            let member = value
                .members
                .remove(&coordinate)
                .unwrap_or_else(|| ledger.project_schema(value, coordinate.clone(), mode));
            let member = self.receive(ledger, ty, member, choices);
            value.members.insert(coordinate, member);
        }
    }
}

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
    pub(super) fn propagated(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        value: Datum,
        site: Span,
    ) -> Datum {
        let Some(ty) = self.program.propagation_inputs.get(&site) else {
            return Datum::default();
        };
        let success = if ty.is_result() { "Ok" } else { "Some" };
        let member = Coordinate::Index("0".into());
        if !ctx.reachable {
            return ledger.project(&value, member, Access::Immutable);
        }
        let mut paths = ledger.variant_paths(&value);
        if paths.is_empty() {
            paths.push((ledger.clone(), value));
        }
        let mut continuing = Vec::new();
        let mut output = None;
        for (mut path, value) in paths {
            path.inspect_root(&value);
            let tag = value.known_variant();
            if tag != Some(success) {
                if tag.is_some() {
                    path.inspect(&value);
                    self.check_results(&path, &Inspections::new());
                    self.storage_exit(ctx, &path);
                    if ctx.runtime && !ctx.shadow {
                        ctx.return_values.push(path.snapshot(&value));
                    }
                    continue;
                }
                // An unknown Result can stop here. A payload known to occur
                // only in Err leaves with the returned error.
                let transfer = match ty {
                    Ty::Result(ok, _) if ok.is_value() => path.snapshot(&value).results(),
                    _ => Inspections::new(),
                };
                self.check_results(&path, &transfer);
                self.storage_exit(ctx, &path);
            }
            let payload = path.project(&value, member.clone(), Access::Immutable);
            output = Some(match output {
                Some(prior) => payload.joined(prior),
                None => payload,
            });
            continuing.push(path);
        }
        if !ledger.continue_at_pattern(continuing) {
            ledger.no_continuation = true;
        }
        output.unwrap_or_default()
    }

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
