use ril_syntax::syntax::{Pattern, PatternId, Type};

use super::{
    AdtKind, Ty,
    check::{Checker, Env},
};

#[derive(Clone)]
pub(super) enum Shape {
    Any,
    Constructor(String, Vec<Shape>),
    Or(Vec<Shape>),
}

impl Checker<'_> {
    pub(super) fn pattern_shape(&mut self, env: &Env, id: PatternId, input: &Ty) -> Shape {
        use Shape::{Any, Constructor, Or};
        let input = match input {
            Ty::Draft(inner) => inner,
            ty => ty,
        };
        match &self.ast(env.file).pattern(id).value {
            Pattern::Binding(..) | Pattern::Wildcard | Pattern::Rest(_) => Any,
            Pattern::Unit => Constructor("()".into(), Vec::new()),
            Pattern::Literal(literal) => {
                let name = super::literal(literal)
                    .map_or_else(|_| literal.text.clone(), |value| super::render(&value));
                Constructor(name, Vec::new())
            }
            Pattern::Tuple(items) => {
                let parts = items
                    .iter()
                    .enumerate()
                    .map(|(i, &part)| {
                        let ty = if let Ty::Tuple(items) = input {
                            items.get(i).map_or(&Ty::Unknown, |item| &item.ty)
                        } else {
                            &Ty::Unknown
                        };
                        self.pattern_shape(env, part, ty)
                    })
                    .collect();
                Constructor("tuple".into(), parts)
            }
            Pattern::Constructor(path, parts) => {
                let name = path.segments.last().map_or("", |s| s.name.value.as_str());
                let payload = self.constructor_payload(env, input, name);
                let typed = parts
                    .iter()
                    .flatten()
                    .enumerate()
                    .map(|(i, &id)| {
                        self.pattern_shape(env, id, payload.get(i).unwrap_or(&Ty::Unknown))
                    })
                    .collect();
                Constructor(name.into(), typed)
            }
            Pattern::Or(items) => Or(items
                .iter()
                .map(|&id| self.pattern_shape(env, id, input))
                .collect()),
            Pattern::Subset { ty, .. } => {
                if let Ty::Adt(subset) = self.type_expr(&mut env.clone(), *ty) {
                    Or(self
                        .sum_variants(&subset)
                        .into_iter()
                        .map(|(tag, payload)| Constructor(tag, vec![Any; payload.len()]))
                        .collect())
                } else {
                    Or(Vec::new())
                }
            }
            Pattern::Record { fields, .. } => {
                let unwrapped = match input {
                    Ty::Adt(adt)
                        if adt.kind == AdtKind::Nominal
                            || (adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope) =>
                    {
                        self.representation(env, adt)
                    }
                    _ => None,
                };
                let target = unwrapped.as_ref().unwrap_or(input);
                if let Ty::Record(known, _) = target {
                    let fields = known
                        .iter()
                        .map(|(key, ty)| {
                            fields
                                .iter()
                                .find(|f| f.name.value == *key)
                                .and_then(|f| f.pattern)
                                .map_or(Any, |id| self.pattern_shape(env, id, &ty.ty))
                        })
                        .collect();
                    Constructor("record".into(), fields)
                } else if fields.iter().all(|f| f.pattern.is_none()) {
                    Any
                } else {
                    Constructor(
                        format!("sealed-pattern:{}", id_span(self, env, id)),
                        Vec::new(),
                    )
                }
            }
            Pattern::Slice { elements, .. } if matches!(elements.as_slice(), [id] if matches!(self.ast(env.file).pattern(*id).value, Pattern::Rest(_))) => {
                Any
            }
            Pattern::Type(ty) => match &self.ast(env.file).ty(*ty).value {
                Type::PatternWildcard | Type::PatternBinding(_) => Any,
                _ => {
                    let typed = self.type_expr(&mut env.clone(), *ty);
                    Constructor(format!("<{}>", typed.display(self.hir)), Vec::new())
                }
            },
            _ => Constructor(
                format!("partial-pattern:{}", id_span(self, env, id)),
                Vec::new(),
            ),
        }
    }

    pub(super) fn useful(&mut self, env: &Env, prior: &[Shape], arm: Shape, ty: &Ty) -> bool {
        let matrix = prior.iter().cloned().map(|p| vec![p]).collect::<Vec<_>>();
        self.useful_row(env, &matrix, &[arm], std::slice::from_ref(ty), 0)
    }

    fn useful_row(
        &mut self,
        env: &Env,
        matrix: &[Vec<Shape>],
        row: &[Shape],
        types: &[Ty],
        depth: usize,
    ) -> bool {
        let Some((head, rest)) = row.split_first() else {
            return matrix.is_empty();
        };
        if matrix.is_empty() {
            return true;
        }
        if matrix
            .iter()
            .any(|row| row.iter().all(|item| matches!(item, Shape::Any)))
        {
            return false;
        }
        if depth == 128 {
            // Unfolding recursive sum domains is bounded. Lacking a coverage proof
            // leaves the arm useful and forces an explicit default where necessary.
            return true;
        }
        let (ty, tail) = types.split_first().unwrap_or((&Ty::Unknown, &[]));
        match head {
            Shape::Or(choices) => choices.iter().any(|choice| {
                let row = std::iter::once(choice.clone())
                    .chain(rest.iter().cloned())
                    .collect::<Vec<_>>();
                self.useful_row(env, matrix, &row, types, depth + 1)
            }),
            Shape::Constructor(name, parts) => {
                let children = self.constructor_payload(env, ty, name);
                let arity = children.len().max(parts.len());
                let selected = specialize(matrix, Some(name), arity);
                let mut row = parts.clone();
                row.resize(arity, Shape::Any);
                row.extend_from_slice(rest);
                let tys = children
                    .into_iter()
                    .chain(tail.iter().cloned())
                    .collect::<Vec<_>>();
                self.useful_row(env, &selected, &row, &tys, depth + 1)
            }
            Shape::Any => {
                if let Some(domain) = self.constructors(env, ty) {
                    domain.into_iter().any(|(name, children)| {
                        let selected = specialize(matrix, Some(&name), children.len());
                        let row = std::iter::repeat_n(Shape::Any, children.len())
                            .chain(rest.iter().cloned())
                            .collect::<Vec<_>>();
                        let types = children
                            .into_iter()
                            .chain(tail.iter().cloned())
                            .collect::<Vec<_>>();
                        self.useful_row(env, &selected, &row, &types, depth + 1)
                    })
                } else {
                    let selected = specialize(matrix, None, 0);
                    self.useful_row(env, &selected, rest, tail, depth + 1)
                }
            }
        }
    }

    fn constructor_payload(&mut self, env: &Env, ty: &Ty, name: &str) -> Vec<Ty> {
        self.constructors(env, ty)
            .unwrap_or_default()
            .into_iter()
            .find_map(|(key, members)| (key == name).then_some(members))
            .unwrap_or_default()
    }

    fn constructors(&mut self, env: &Env, ty: &Ty) -> Option<Vec<(String, Vec<Ty>)>> {
        Some(match ty {
            Ty::Draft(inner) => return self.constructors(env, inner),
            Ty::Never => Vec::new(),
            Ty::Bool => vec![("true".into(), vec![]), ("false".into(), vec![])],
            Ty::Unit => vec![("()".into(), vec![])],
            Ty::Mode => vec![
                ("Let".into(), vec![]),
                ("Var".into(), vec![]),
                ("Mut".into(), vec![]),
                ("SharedMut".into(), vec![]),
                ("Ref".into(), vec![]),
                ("VarMut".into(), vec![]),
                ("VarSharedMut".into(), vec![]),
                ("VarRef".into(), vec![]),
            ],
            Ty::Tuple(items) => vec![(
                "tuple".into(),
                items.iter().map(|item| item.ty.clone()).collect(),
            )],
            Ty::Record(items, false) => vec![(
                "record".into(),
                items.values().map(|item| item.ty.clone()).collect(),
            )],
            Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
                self.match_domain(env, ty)?;
                self.sum_variants(adt).into_iter().collect()
            }
            Ty::Adt(adt)
                if adt.kind == AdtKind::Nominal
                    || (adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope) =>
            {
                let name = self.hir.definition(adt.definition).name.value.clone();
                match self.representation(env, adt) {
                    Some(Ty::Record(items, false)) => vec![(
                        "record".into(),
                        items.values().map(|item| item.ty.clone()).collect(),
                    )],
                    Some(Ty::Tuple(items)) => {
                        vec![(name, items.into_iter().map(|m| m.ty).collect())]
                    }
                    Some(Ty::Unit) | None => vec![(name, Vec::new())],
                    Some(inner) => vec![(name, vec![inner])],
                }
            }
            Ty::TypeValue(Some(inner)) => {
                if let Ty::Param(id) = **inner {
                    let domain = env.domains.get(&id)?;
                    if domain.iter().any(|ty| {
                        matches!(ty, Ty::Unknown | Ty::Record(_, true) | Ty::TypeValue(None))
                    }) {
                        return None;
                    }
                    domain
                        .iter()
                        .map(|ty| (format!("<{}>", ty.display(self.hir)), Vec::new()))
                        .collect()
                } else {
                    // A type function may define polymorphic patterns independently of
                    // the currently selected static instantiation.
                    return None;
                }
            }
            _ => return None,
        })
    }
}

fn id_span(compiler: &Checker<'_>, env: &Env, id: PatternId) -> usize {
    compiler.ast(env.file).pattern(id).span.start
}

fn specialize(rows: &[Vec<Shape>], name: Option<&str>, arity: usize) -> Vec<Vec<Shape>> {
    let mut result = Vec::new();
    for row in rows {
        if let Some((head, tail)) = row.split_first() {
            expand(head, tail, name, arity, &mut result);
        }
    }
    result
}

fn expand(
    head: &Shape,
    tail: &[Shape],
    name: Option<&str>,
    arity: usize,
    output: &mut Vec<Vec<Shape>>,
) {
    let mut selected = match head {
        Shape::Any => vec![Shape::Any; arity],
        Shape::Constructor(label, parts) if name == Some(label) => parts.clone(),
        Shape::Or(alternatives) => {
            for head in alternatives {
                expand(head, tail, name, arity, output);
            }
            return;
        }
        _ => return,
    };
    selected.resize(arity, Shape::Any);
    selected.extend_from_slice(tail);
    output.push(selected);
}
