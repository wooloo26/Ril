//! Lexical publication visibility is independent of immutable object identity.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct PublicationBindingId(u64);
pub(super) struct Visibility(BTreeMap<String, PublicationBindingId>);
struct Published {
    binding: PublicationBindingId,
    name: String,
}
#[derive(Default)]
pub(super) struct Bindings {
    next: u64,
    visible: BTreeMap<String, PublicationBindingId>,
    collections: BTreeMap<u64, Vec<Published>>,
}
impl Bindings {
    pub(super) fn snapshot(&self, budget: &budget::Budget) -> Result<Visibility> {
        for name in self.visible.keys() {
            budget.work(1 + name.len() as u64)?;
        }
        Ok(Visibility(self.visible.clone()))
    }
    pub(super) fn restore(&mut self, visibility: Visibility) {
        // Never rewind next or erase collection identity when leaving a scope.
        self.visible = visibility.0;
    }
    pub(super) fn bind_name(
        &mut self,
        name: &str,
        budget: &budget::Budget,
    ) -> Result<PublicationBindingId> {
        budget.work(1 + name.len() as u64)?;
        let binding = PublicationBindingId(self.next);
        self.next = self.next.checked_add(1).ok_or_else(|| {
            Failure::Unsupported("static publication binding identity allowance".into())
        })?;
        self.visible.insert(name.into(), binding);
        Ok(binding)
    }
    pub(super) fn publish(
        &mut self,
        collection: u64,
        name: &str,
        budget: &budget::Budget,
    ) -> Result<()> {
        let binding = self.visible.get(name).copied().ok_or_else(|| {
            Failure::Unsupported("static publication has no lexical binding token".into())
        })?;
        budget.work(1 + name.len() as u64)?;
        self.collections
            .entry(collection)
            .or_default()
            .push(Published {
                binding,
                name: name.into(),
            });
        Ok(())
    }
    pub(super) fn visible_name(&self, collection: u64) -> Option<&str> {
        self.collections
            .get(&collection)?
            .iter()
            .rev()
            .find_map(|published| {
                (self.visible.get(&published.name) == Some(&published.binding))
                    .then_some(published.name.as_str())
            })
    }
}

fn step(budget: &budget::Budget, depth: usize) -> Result<()> {
    if depth > 128 {
        return Err(Failure::Unsupported(
            "static publication binder nesting allowance".into(),
        ));
    }
    budget.work(1)
}
pub(super) fn pattern_names<'a>(
    pattern: &'a Pattern,
    budget: &budget::Budget,
) -> Result<BTreeSet<&'a str>> {
    fn visit<'a>(
        pattern: &'a Pattern,
        names: &mut BTreeSet<&'a str>,
        budget: &budget::Budget,
        depth: usize,
    ) -> Result<()> {
        step(budget, depth)?;
        match &pattern.kind {
            PatternKind::Name(name) => {
                names.insert(name);
            }
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    visit(item, names, budget, depth + 1)?;
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    visit(&field.pattern, names, budget, depth + 1)?;
                }
                if let Some(name) = rest_binding {
                    names.insert(name);
                }
            }
            PatternKind::Mode { pattern, .. } => visit(pattern, names, budget, depth + 1)?,
            PatternKind::Type { ty, binder } => {
                if let Some(name) = binder {
                    names.insert(name);
                }
                type_names(ty, names, budget, depth + 1)?;
            }
            _ => {}
        }
        Ok(())
    }
    let mut names = BTreeSet::new();
    visit(pattern, &mut names, budget, 0)?;
    Ok(names)
}
fn type_names<'a>(
    ty: &'a TypeExpr,
    names: &mut BTreeSet<&'a str>,
    budget: &budget::Budget,
    depth: usize,
) -> Result<()> {
    step(budget, depth)?;
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            if let Some(name) = path.first().and_then(|name| name.strip_prefix("let ")) {
                names.insert(name);
            }
            for ty in arguments {
                type_names(ty, names, budget, depth + 1)?;
            }
        }
        TypeKind::Tuple(items) => {
            for ty in items {
                type_names(ty, names, budget, depth + 1)?;
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                type_names(&field.ty, names, budget, depth + 1)?;
            }
            if let Some(ty) = row {
                type_names(ty, names, budget, depth + 1)?;
            }
        }
        TypeKind::Array { element, .. }
        | TypeKind::Optional(element)
        | TypeKind::Rest(element)
        | TypeKind::KeyOf(element) => type_names(element, names, budget, depth + 1)?,
        TypeKind::Map { key, value }
        | TypeKind::KindArrow {
            parameter: key,
            result: value,
        } => {
            type_names(key, names, budget, depth + 1)?;
            type_names(value, names, budget, depth + 1)?;
        }
        _ => {}
    }
    Ok(())
}

/// Names definitely introduced on this outcome, respecting short circuit.
pub(super) fn condition_names<'a>(
    expression: &'a Expr,
    truth: bool,
    budget: &budget::Budget,
) -> Result<BTreeSet<&'a str>> {
    fn visit<'a>(
        expression: &'a Expr,
        budget: &budget::Budget,
        depth: usize,
    ) -> Result<[BTreeSet<&'a str>; 2]> {
        step(budget, depth)?;
        Ok(match &expression.kind {
            ExprKind::Is { pattern, .. } => [BTreeSet::new(), pattern_names(pattern, budget)?],
            ExprKind::Unary { operator, operand } if operator == "!" => {
                let [when_false, when_true] = visit(operand, budget, depth + 1)?;
                [when_true, when_false]
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "&&" || operator == "||" => {
                // Compute both outcomes once per syntax node; deeply nested
                // boolean conditions must not recursively re-expand paths.
                let [left_false, left_true] = visit(left, budget, depth + 1)?;
                let [right_false, right_true] = visit(right, budget, depth + 1)?;
                if operator == "&&" {
                    let mut right_exit = left_true.clone();
                    right_exit.extend(right_false);
                    let when_false = left_false.intersection(&right_exit).copied().collect();
                    let mut when_true = left_true;
                    when_true.extend(right_true);
                    [when_false, when_true]
                } else {
                    let mut right_exit = left_false.clone();
                    right_exit.extend(right_true);
                    let when_true = left_true.intersection(&right_exit).copied().collect();
                    let mut when_false = left_false;
                    when_false.extend(right_false);
                    [when_false, when_true]
                }
            }
            _ => Default::default(),
        })
    }
    let [when_false, when_true] = visit(expression, budget, 0)?;
    Ok(if truth { when_true } else { when_false })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn condition_visibility_agrees_with_every_concrete_short_circuit_path() {
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        };
        let test = |name: &str| Expr {
            kind: ExprKind::Is {
                value: Box::new(Expr {
                    kind: ExprKind::Name("input".into()),
                    span,
                }),
                pattern: Pattern {
                    kind: PatternKind::Name(name.into()),
                    span,
                },
            },
            span,
        };
        let binary = |operator: &str, left: Expr, right: Expr| Expr {
            kind: ExprKind::Binary {
                operator: operator.into(),
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        };
        let negate = |value: Expr| Expr {
            kind: ExprKind::Unary {
                operator: "!".into(),
                operand: Box::new(value),
            },
            span,
        };
        // Independent concrete executions record a bit for each binder actually
        // introduced. No abstract outcome/intersection helper is reused here.
        fn paths(expression: &Expr) -> Vec<(bool, u8)> {
            match &expression.kind {
                ExprKind::Is { pattern, .. } => {
                    let PatternKind::Name(name) = &pattern.kind else {
                        unreachable!()
                    };
                    let bit = match name.as_str() {
                        "a" => 1,
                        "b" => 2,
                        "c" => 4,
                        _ => unreachable!(),
                    };
                    vec![(false, 0), (true, bit)]
                }
                ExprKind::Unary { operand, .. } => paths(operand)
                    .into_iter()
                    .map(|(truth, bits)| (!truth, bits))
                    .collect(),
                ExprKind::Binary {
                    operator,
                    left,
                    right,
                } => {
                    let mut output = vec![];
                    for (left_truth, left_bits) in paths(left) {
                        if left_truth == (operator == "&&") {
                            for (right_truth, right_bits) in paths(right) {
                                output.push((right_truth, left_bits | right_bits));
                            }
                        } else {
                            output.push((left_truth, left_bits));
                        }
                    }
                    output
                }
                _ => unreachable!(),
            }
        }
        let budget = budget::Budget::default();
        for expression in [
            binary("&&", test("a"), test("b")),
            binary("||", test("a"), test("b")),
            negate(binary("&&", test("a"), test("b"))),
            binary("&&", binary("||", test("a"), test("b")), test("c")),
            binary("&&", test("a"), binary("||", test("b"), test("c"))),
            binary("||", binary("&&", test("a"), test("b")), test("c")),
            binary("&&", binary("||", test("a"), test("b")), negate(test("c"))),
            binary(
                "||",
                binary("||", test("a"), test("b")),
                binary("&&", test("c"), test("a")),
            ),
        ] {
            for truth in [false, true] {
                let actual = paths(&expression)
                    .into_iter()
                    .filter(|(outcome, _)| *outcome == truth)
                    .map(|(_, bits)| bits)
                    .reduce(|left, right| left & right)
                    .unwrap();
                let proved = condition_names(&expression, truth, &budget)
                    .unwrap_or_else(|_| panic!())
                    .into_iter()
                    .fold(0, |bits, name| {
                        bits | match name {
                            "a" => 1,
                            "b" => 2,
                            "c" => 4,
                            _ => unreachable!(),
                        }
                    });
                assert_eq!(proved, actual, "{truth}: {expression:?}");
            }
        }
    }
    #[test]
    fn restored_visibility_does_not_reuse_a_shadowing_binding_token() {
        let budget = budget::Budget::default();
        let mut bindings = Bindings::default();
        let outer = bindings
            .bind_name("VALUES", &budget)
            .unwrap_or_else(|_| panic!());
        bindings
            .publish(7, "VALUES", &budget)
            .unwrap_or_else(|_| panic!());
        let saved = bindings.snapshot(&budget).unwrap_or_else(|_| panic!());
        let inner = bindings
            .bind_name("VALUES", &budget)
            .unwrap_or_else(|_| panic!());
        bindings
            .publish(9, "VALUES", &budget)
            .unwrap_or_else(|_| panic!());
        assert_ne!(outer, inner);
        assert_eq!(bindings.visible_name(7), None);
        assert_eq!(bindings.visible_name(9), Some("VALUES"));
        bindings.restore(saved);
        assert_eq!(bindings.visible_name(7), Some("VALUES"));
        assert_eq!(bindings.visible_name(9), None);
        assert_ne!(
            bindings
                .bind_name("VALUES", &budget)
                .unwrap_or_else(|_| panic!()),
            inner
        );
    }
    #[test]
    fn another_alias_remains_visible_without_merging_distinct_objects() {
        let budget = budget::Budget::default();
        let mut bindings = Bindings::default();
        for name in ["A", "B"] {
            bindings
                .bind_name(name, &budget)
                .unwrap_or_else(|_| panic!());
            bindings
                .publish(7, name, &budget)
                .unwrap_or_else(|_| panic!());
        }
        bindings
            .bind_name("B", &budget)
            .unwrap_or_else(|_| panic!());
        bindings
            .publish(9, "B", &budget)
            .unwrap_or_else(|_| panic!());
        assert_eq!(bindings.visible_name(7), Some("A"));
        assert_eq!(bindings.visible_name(9), Some("B"));
        // A runtime/scalar binder has no collection publication of its own.
        bindings
            .bind_name("A", &budget)
            .unwrap_or_else(|_| panic!());
        assert_eq!(bindings.visible_name(7), None);
    }
}
