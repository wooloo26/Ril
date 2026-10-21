//! Temporary type syntax is a projection of the frozen graph, never a new
//! source declaration or runtime evaluation. All projected IDs remain absent.
use super::queries::SourceTypeQueries;
use super::{SourceContainer, SourceNode, SourceTypeId, SourceTypes, SourceTypesError, WorkLimit};
use ril_compiler_core::source::Span;
use ril_syntax::ast::{
    Annotation, AnnotationKind, Expr, ExprKind, Literal, Parameter, Pattern, PatternKind, TypeExpr,
    TypeField, TypeKind,
};
use std::collections::BTreeSet;

pub(super) fn project(
    types: &SourceTypes,
    root: SourceTypeId,
    span: Span,
    work: &mut WorkLimit,
    binder: &mut impl FnMut(&str, bool, &mut WorkLimit) -> Result<TypeExpr, SourceTypesError>,
) -> Result<TypeExpr, SourceTypesError> {
    struct Projection<'a, F> {
        types: &'a SourceTypes,
        span: Span,
        active: BTreeSet<SourceTypeId>,
        binder: F,
    }
    impl<F> Projection<'_, F>
    where
        F: FnMut(&str, bool, &mut WorkLimit) -> Result<TypeExpr, SourceTypesError>,
    {
        fn ty(
            &mut self,
            root: SourceTypeId,
            row: bool,
            work: &mut WorkLimit,
            depth: usize,
        ) -> Result<TypeExpr, SourceTypesError> {
            work.charge(1)?;
            if depth >= 64 {
                return Err(SourceTypesError::BudgetExceeded);
            }
            let root = self.types.unalias(root, work)?;
            if !self.active.insert(root) {
                return Err(SourceTypesError::RecursiveLegacyKey);
            }
            let types = self.types;
            let node = types.get(root)?;
            node.charge(work)?;
            let kind = match node {
                SourceNode::Binder(identity) => {
                    let result = (self.binder)(identity, row, work)?;
                    self.active.remove(&root);
                    return Ok(result);
                }
                SourceNode::Scalar(super::SourceScalar::Unit) => TypeKind::Tuple(vec![]),
                SourceNode::Scalar(kind) => {
                    let name = super::scalar_name(*kind);
                    let mut path = Vec::new();
                    if !name.contains("::") {
                        path.push("Prelude".into());
                    }
                    path.extend(name.split("::").map(str::to_owned));
                    TypeKind::Name {
                        path,
                        arguments: vec![],
                    }
                }
                SourceNode::Nominal(identity) => TypeKind::Name {
                    path: identity.name().split("::").map(str::to_owned).collect(),
                    arguments: vec![],
                },
                SourceNode::OpaqueName { name, arguments } => {
                    work.charge(arguments.len())?;
                    TypeKind::Name {
                        path: name.split("::").map(str::to_owned).collect(),
                        arguments: arguments
                            .iter()
                            .map(|argument| self.ty(*argument, false, work, depth + 1))
                            .collect::<Result<_, _>>()?,
                    }
                }
                SourceNode::Array { length, element } => {
                    let length = match length {
                        super::SourceLength::Dynamic => None,
                        super::SourceLength::Fixed(length) => {
                            // This literal is only a type-coordinate adapter;
                            // it is never installed in an evaluation arena.
                            work.charge(2)?;
                            Some(Box::new(Expr {
                                hir_id: None,
                                span: self.span,
                                kind: ExprKind::Literal(Literal::Integer(length.to_string())),
                            }))
                        }
                    };
                    TypeKind::Array {
                        length,
                        element: Box::new(self.ty(*element, false, work, depth + 1)?),
                    }
                }
                SourceNode::Map { key, value } => TypeKind::Map {
                    key: Box::new(self.ty(*key, false, work, depth + 1)?),
                    value: Box::new(self.ty(*value, false, work, depth + 1)?),
                },
                SourceNode::Tuple(items) => {
                    work.charge(items.len())?;
                    TypeKind::Tuple(
                        items
                            .iter()
                            .map(|item| self.ty(*item, false, work, depth + 1))
                            .collect::<Result<_, _>>()?,
                    )
                }
                SourceNode::Record { fields, row } => {
                    work.charge(fields.len() + usize::from(row.is_some()))?;
                    TypeKind::Record {
                        fields: fields
                            .iter()
                            .map(|field| {
                                Ok(TypeField {
                                    name: field.label.clone(),
                                    mutable: field.mutable,
                                    ty: self.ty(field.value, false, work, depth + 1)?,
                                    span: self.span,
                                })
                            })
                            .collect::<Result<_, SourceTypesError>>()?,
                        row: row
                            .map(|row| self.ty(row, true, work, depth + 1).map(Box::new))
                            .transpose()?,
                    }
                }
                SourceNode::Callable {
                    parameters,
                    result,
                    annotations,
                } => {
                    work.charge(parameters.len() + annotations.len() + 1)?;
                    let parameters = parameters
                        .iter()
                        .map(|(mode, ty)| {
                            Ok(Parameter {
                                pattern: Pattern {
                                    hir_id: None,
                                    kind: PatternKind::Wildcard,
                                    span: self.span,
                                },
                                mode: *mode,
                                ty: Some(self.ty(*ty, false, work, depth + 1)?),
                                default: None,
                                span: self.span,
                            })
                        })
                        .collect::<Result<_, SourceTypesError>>()?;
                    let annotations = annotations
                        .iter()
                        .map(|text| {
                            Ok(Annotation {
                                kind: match text.as_bytes().first() {
                                    Some(b'@') => AnnotationKind::Effect,
                                    Some(b'&') => AnnotationKind::Capability,
                                    _ => return Err(SourceTypesError::Unresolved),
                                },
                                text: text.clone(),
                                span: self.span,
                            })
                        })
                        .collect::<Result<_, SourceTypesError>>()?;
                    TypeKind::Callable {
                        parameters,
                        result: Some(Box::new(self.ty(*result, false, work, depth + 1)?)),
                        annotations,
                    }
                }
                SourceNode::Container { kind, arguments } => {
                    work.charge(arguments.len())?;
                    let name = match kind {
                        SourceContainer::Immutable => "Prelude::Immut",
                        SourceContainer::Option => "Prelude::Option",
                        SourceContainer::Result => "Prelude::Result",
                        SourceContainer::Set => "Prelude::Set",
                        SourceContainer::Range => "Prelude::Range",
                        SourceContainer::Heap => "Heap::Heap",
                        SourceContainer::Deque => "Deque::Deque",
                    };
                    TypeKind::Name {
                        path: name.split("::").map(str::to_owned).collect(),
                        arguments: arguments
                            .iter()
                            .map(|argument| self.ty(*argument, false, work, depth + 1))
                            .collect::<Result<_, _>>()?,
                    }
                }
                SourceNode::GenericBuiltin(_)
                | SourceNode::OpaqueComputation(_)
                | SourceNode::Unresolved { .. } => return Err(SourceTypesError::Unresolved),
                SourceNode::Alias { .. } => unreachable!("unalias returned an alias"),
            };
            self.active.remove(&root);
            Ok(TypeExpr {
                hir_id: None,
                text: String::new(),
                span: self.span,
                kind,
            })
        }
    }
    Projection {
        types,
        span,
        active: BTreeSet::new(),
        binder,
    }
    .ty(root, false, work, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        effect_identity::{ArgumentKey, StaticBinderSort},
        source_types::{SourceBuilder, SourceField, SourceSchema},
    };
    use ril_compiler_core::{ids::TypeExprId, source::FileId};
    use ril_syntax::ast::ParameterMode;
    use std::collections::BTreeMap;

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 0,
            end: 0,
        }
    }
    fn binder(identity: &str) -> ArgumentKey {
        ArgumentKey::Binder {
            identity: identity.into(),
            sort: StaticBinderSort::Type,
        }
    }

    #[test]
    fn projected_effect_types_keep_fixed_dimensions_modes_rows_and_genuine_uid_roles() {
        let fixed = ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some("const(int:2)".into()),
                element: Box::new(binder("actual:U")),
            }),
        };
        let key = ArgumentKey::Record {
            fields: vec![
                (
                    "action".into(),
                    false,
                    ArgumentKey::Callable {
                        parameters: vec![(ParameterMode::Mut, fixed.clone())],
                        result: Box::new(fixed),
                        annotations: vec!["&mut".into(), "@Clock".into()],
                    },
                ),
                (
                    "input".into(),
                    false,
                    ArgumentKey::Name {
                        name: "Process::Input".into(),
                        arguments: vec![],
                    },
                ),
            ],
            row: Some(Box::new(binder("actual:row"))),
        };
        let source =
            SourceSchema::import(&key, Some(TypeExprId(9)), &mut WorkLimit::new(4096)).unwrap();
        let mut names = BTreeMap::new();
        let mut roles = Vec::new();
        let projected = source
            .syntax_projection(
                span(),
                &mut WorkLimit::new(4096),
                &mut |identity, row, work| {
                    work.charge(1 + identity.len().div_ceil(32))?;
                    let token = format!("\0projected:{identity}");
                    names.insert(token.clone(), identity.to_owned());
                    roles.push((identity.to_owned(), row));
                    Ok(TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span: span(),
                        kind: TypeKind::Name {
                            path: vec![token],
                            arguments: vec![],
                        },
                    })
                },
            )
            .unwrap();
        assert_eq!(source.original(), Some(TypeExprId(9)));
        assert!(projected.hir_id.is_none());
        assert!(roles.contains(&("actual:row".into(), true)));
        assert!(
            roles
                .iter()
                .all(|(identity, row)| identity != "actual:U" || !row)
        );
        let actual = crate::static_eval::effects::bounded_argument_key(&projected, &names).unwrap();
        assert!(
            source
                .equivalent_key(&actual, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let TypeKind::Record { fields, .. } = &projected.kind else {
            panic!("record")
        };
        let TypeKind::Callable { parameters, .. } = &fields[0].ty.kind else {
            panic!("callable")
        };
        assert!(parameters[0].pattern.hir_id.is_none() && parameters[0].default.is_none());
        let TypeKind::Array {
            length: Some(length),
            ..
        } = &parameters[0].ty.as_ref().unwrap().kind
        else {
            panic!("fixed dimension")
        };
        assert!(length.hir_id.is_none());
        assert!(matches!(&length.kind, ExprKind::Literal(Literal::Integer(value)) if value=="0"));
        let mut called = false;
        assert!(matches!(
            source.syntax_projection(span(), &mut WorkLimit::new(0), &mut |_, _, _| {
                called = true;
                Err(SourceTypesError::Unresolved)
            }),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(!called);
    }

    #[test]
    fn unknown_and_recursive_graphs_do_not_receive_syntax_fallbacks() {
        let unknown = SourceSchema::import(
            &ArgumentKey::Closed("unresolved computation".into()),
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert!(matches!(
            unknown.syntax_projection(span(), &mut WorkLimit::new(4096), &mut |_, _, _| Err(
                SourceTypesError::Unresolved
            )),
            Err(SourceTypesError::Unresolved)
        ));
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![SourceField {
                        label: "following".into(),
                        mutable: false,
                        value: root,
                    }],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let recursive = SourceSchema::copy_from(&types, root, None, &mut work).unwrap();
        assert!(matches!(
            recursive.syntax_projection(span(), &mut work, &mut |_, _, _| Err(
                SourceTypesError::Unresolved
            )),
            Err(SourceTypesError::RecursiveLegacyKey)
        ));
    }
}
