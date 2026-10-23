//! The Result domain projects existing producers through one sequence plan.
use super::*;

impl Engine<'_> {
    pub(super) fn sequence_pattern(
        &mut self,
        root: &Pattern,
        patterns: &[Pattern],
        value: &Value,
        state: State,
        array: bool,
    ) -> std::result::Result<Vec<(State, bool)>, Problem> {
        let empty = Vec::new();
        let items = match (&value.shape, array, &value.ty) {
            (Shape::Array(items), true, _) | (Shape::Tuple(items), false, _) => items,
            (Shape::Plain, false, Ty::Unit) => &empty,
            _ => {
                return Err(incomplete(
                    root.span,
                    "static sequence pattern lacks its declared member graph",
                ));
            }
        };
        let mut rest = None;
        for (index, pattern) in patterns.iter().enumerate() {
            self.step(pattern.span)?;
            if matches!(pattern.kind, PatternKind::Rest(_)) && rest.replace(index).is_some() {
                return Err(Problem {
                    failure: Box::new(Failure::Diagnostic(
                        "E0347",
                        "one sequence permits at most one rest".into(),
                    )),
                    span: pattern.span,
                    producer: None,
                });
            }
        }
        let minimum = patterns.len() - usize::from(rest.is_some());
        if items.len() < minimum || (rest.is_none() && items.len() != minimum) {
            return Ok(vec![(state, false)]);
        }
        let mut members = Vec::new();
        for (index, pattern) in patterns.iter().enumerate() {
            if matches!(pattern.kind, PatternKind::Rest(_)) {
                continue;
            }
            let selected = if rest.is_some_and(|rest| index > rest) {
                items.len() - (patterns.len() - index)
            } else {
                index
            };
            members.push((pattern, &items[selected]));
        }
        let mut paths = self.pattern_members(members, state)?;
        if let Some(index) = rest
            && let PatternKind::Rest(Some(name)) = &patterns[index].kind
            && name != "_"
        {
            if !array {
                return Err(incomplete(root.span, "a tuple rest cannot bind a value"));
            }
            let suffix = patterns.len() - index - 1;
            for _ in &items[index..items.len() - suffix] {
                self.step(root.span)?;
            }
            let selected = items[index..items.len() - suffix].to_vec();
            let source_type = if let Some(source) = &value.source_type {
                at(
                    self.evaluator.project_source_schema(
                        source,
                        &[
                            ril_compiler_core::projection::TypeProjection::ArrayRemainder {
                                prefix: u32::try_from(index).map_err(|_| {
                                    incomplete(root.span, "array rest coordinate limit")
                                })?,
                                suffix: u32::try_from(suffix).map_err(|_| {
                                    incomplete(root.span, "array rest coordinate limit")
                                })?,
                            },
                        ],
                        root.span,
                    ),
                    root.span,
                )?
            } else {
                None
            };
            let Ty::Array(element, _) = &value.ty else {
                return Err(incomplete(
                    root.span,
                    "array rest has no original array type",
                ));
            };
            let fixed = source_type.as_ref().is_some_and(|source| {
                matches!(
                    source.syntax.kind,
                    TypeKind::Array {
                        length: Some(_),
                        ..
                    }
                )
            });
            let rest_value = Value {
                source_type,
                ty: Ty::Array(element.clone(), fixed.then_some(selected.len())),
                shape: Shape::Array(selected),
            };
            for (state, matched) in &mut paths {
                if *matched {
                    self.mask_const_bindings(state, &BTreeSet::from([name.clone()]), root.span)?;
                    state.env.insert(name.clone(), rest_value.clone());
                }
            }
        }
        Ok(paths)
    }
}
