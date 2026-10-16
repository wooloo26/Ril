//! Keep written generic arguments and parameter labels as source schemas. The
//! intrinsic name is unchanged; lowering reorders already evaluated operands.
use super::*;

pub(super) fn labels(name: &str) -> Option<&'static [&'static str]> {
    Some(match name {
        "Parallel::map" => &["items", "transform"],
        "Parallel::map_bounded" => &["items", "max_concurrency", "transform"],
        "Parallel::find" | "Parallel::first" | "Parallel::any" => &["items", "predicate"],
        "Parallel::fold" => &["items", "init_acc", "fold_local", "merge_acc"],
        "Parallel::join" => &["left", "right"],
        "Parallel::join3" => &["first", "second", "third"],
        "Parallel::for_each" => &["items", "action"],
        _ => return None,
    })
}
pub(super) fn parameters(name: &str, span: Span) -> Option<Vec<Parameter>> {
    Some(
        labels(name)?
            .iter()
            .enumerate()
            .map(|(index, label)| Parameter {
                pattern: Pattern {
                    hir_id: None,
                    kind: PatternKind::Name((*label).into()),
                    span,
                },
                mode: if name == "Parallel::for_each" && index == 0 {
                    ParameterMode::Mut
                } else {
                    ParameterMode::Read
                },
                ty: None,
                default: None,
                span,
            })
            .collect(),
    )
}
fn named(name: &str, span: Span) -> TypeExpr {
    TypeExpr {
        hir_id: None,
        text: name.into(),
        kind: TypeKind::Name {
            path: vec![name.into()],
            arguments: vec![],
        },
        span,
    }
}
fn array(element: TypeExpr, span: Span) -> TypeExpr {
    TypeExpr {
        hir_id: None,
        text: String::new(),
        kind: TypeKind::Array {
            element: Box::new(element),
            length: None,
        },
        span,
    }
}
fn callable(inputs: Vec<(ParameterMode, TypeExpr)>, output: TypeExpr, span: Span) -> TypeExpr {
    let mutable = inputs.iter().any(|(mode, _)| *mode != ParameterMode::Read);
    TypeExpr {
        hir_id: None,
        text: String::new(),
        kind: TypeKind::Callable {
            parameters: inputs
                .into_iter()
                .enumerate()
                .map(|(index, (mode, ty))| Parameter {
                    pattern: Pattern {
                        hir_id: None,
                        kind: PatternKind::Name(format!("ril__parallel_{index}")),
                        span,
                    },
                    mode,
                    ty: Some(ty),
                    default: None,
                    span,
                })
                .collect(),
            result: Some(Box::new(output)),
            annotations: if mutable {
                vec![Annotation {
                    kind: AnnotationKind::Capability,
                    text: "&mut".into(),
                    span,
                }]
            } else {
                vec![]
            },
        },
        span,
    }
}
fn callback_result(parameter: &Parameter) -> Option<TypeExpr> {
    if let TypeKind::Callable {
        result: Some(result),
        ..
    } = &parameter.ty.as_ref()?.kind
    {
        Some(*result.clone())
    } else {
        None
    }
}

impl Checker {
    pub(super) fn parallel_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) -> bool {
        let Some(name) = value.callables.iter().find_map(|target| match target {
            Callable::Builtin(name) if parallel::is_builtin(name) => Some(name.clone()),
            _ => None,
        }) else {
            return false;
        };
        let arity = match name.as_str() {
            "Parallel::map" | "Parallel::map_bounded" | "Parallel::fold" | "Parallel::join" => 2,
            "Parallel::join3" => 3,
            _ => 1,
        };
        if arguments.len() != arity {
            self.error(
                "E0340",
                span,
                format!("{name} requires {arity} type arguments"),
                [value.cause],
            );
            return true;
        }
        for syntax in arguments {
            self.require_type_argument_identity(syntax);
        }
        let read = |ty: TypeExpr| (ParameterMode::Read, ty);
        let first = arguments[0].clone();
        let unit = TypeExpr {
            hir_id: None,
            text: "()".into(),
            kind: TypeKind::Tuple(vec![]),
            span,
        };
        let inputs = match name.as_str() {
            "Parallel::map" | "Parallel::map_bounded" => {
                let mut inputs = vec![array(first.clone(), span)];
                if name == "Parallel::map_bounded" {
                    inputs.push(named("int", span));
                }
                inputs.push(callable(vec![read(first)], arguments[1].clone(), span));
                inputs
            }
            "Parallel::find" | "Parallel::first" | "Parallel::any" => vec![
                array(first.clone(), span),
                callable(vec![read(first)], named("bool", span), span),
            ],
            "Parallel::fold" => {
                let accumulator = arguments[1].clone();
                vec![
                    array(first.clone(), span),
                    callable(vec![], accumulator.clone(), span),
                    callable(
                        vec![read(accumulator.clone()), read(first)],
                        accumulator.clone(),
                        span,
                    ),
                    callable(
                        vec![read(accumulator.clone()), read(accumulator.clone())],
                        accumulator,
                        span,
                    ),
                ]
            }
            "Parallel::join" | "Parallel::join3" => arguments
                .iter()
                .map(|ty| callable(vec![], ty.clone(), span))
                .collect(),
            "Parallel::for_each" => vec![
                array(first.clone(), span),
                callable(vec![(ParameterMode::Mut, first)], unit.clone(), span),
            ],
            _ => unreachable!(),
        };
        let mut signature = parameters(&name, span).unwrap();
        let types = inputs.iter().map(|syntax| self.ty(syntax)).collect();
        for (parameter, ty) in signature.iter_mut().zip(inputs) {
            parameter.ty = Some(ty);
        }
        let output = parallel_output(&name, &signature, span).unwrap();
        value.ty = Ty::Callable(types, Box::new(self.ty(&output)));
        value.signature = Some(signature);
        true
    }

    pub(super) fn parallel_typed_builtin(
        &mut self,
        callee: &Value,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        if let Some(signature) = &callee.signature {
            for ((_, argument, argument_span), parameter) in args.iter().zip(signature) {
                if let Some(syntax) = &parameter.ty {
                    self.check_storage_shape(argument, syntax, frame);
                    let ty = self.ty(syntax);
                    self.require_type(argument, &ty, *argument_span);
                }
            }
        }
        let output = self
            .parallel_builtin(name, args, span, frame)
            .expect("parallel signature has a contract");
        if let Some(syntax) = callee
            .signature
            .as_ref()
            .and_then(|signature| parallel_output(name, signature, span))
        {
            let ty = self.ty(&syntax);
            self.require_type(&output, &ty, span);
            self.check_storage_shape(&output, &syntax, frame);
        }
        output
    }
}
fn parallel_output(name: &str, parameters: &[Parameter], span: Span) -> Option<TypeExpr> {
    if parameters.iter().any(|parameter| parameter.ty.is_none()) {
        return None;
    }
    Some(match name {
        "Parallel::map" | "Parallel::map_bounded" => {
            array(callback_result(parameters.last()?)?, span)
        }
        "Parallel::find" | "Parallel::first" => {
            let TypeKind::Array { element, .. } = &parameters[0].ty.as_ref()?.kind else {
                return None;
            };
            TypeExpr {
                hir_id: None,
                text: String::new(),
                kind: TypeKind::Optional(element.clone()),
                span,
            }
        }
        "Parallel::any" => named("bool", span),
        "Parallel::fold" => callback_result(&parameters[1])?,
        "Parallel::join" | "Parallel::join3" => TypeExpr {
            hir_id: None,
            text: String::new(),
            kind: TypeKind::Tuple(
                parameters
                    .iter()
                    .map(callback_result)
                    .collect::<Option<_>>()?,
            ),
            span,
        },
        "Parallel::for_each" => TypeExpr {
            hir_id: None,
            text: "()".into(),
            kind: TypeKind::Tuple(vec![]),
            span,
        },
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn parallel_written_types_and_argument_labels_select_the_same_contract() {
        for source in [
            "halt fn example()->int{Parallel::fold(items:[1,2],merge_acc: \\left,right->left+right,init_acc: \\->10,fold_local: \\acc,n->acc+n)}",
            "fn example(){let values=Parallel::map<int,int>([],\\n->n+1);assert(values==[])}",
            "fn example(){let _=Parallel::map<int,int>([1,2],\\n->n+1);let _=Parallel::join<int,str>(right: \\->\"x\",left: \\->1)}",
            "fn example(){let result=Parallel::fold([1,2],merge_acc: \\left,right->left+right,init_acc: \\->10,fold_local: \\acc,n->acc+n);assert(result==13)}",
            "fn example(){let _=Parallel::map_bounded<int,int>(transform: \\n->n+1,max_concurrency:1,items:[1,2]);let _=Parallel::find<int>(predicate: \\n->n>0,items:[1,2])}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for (source, code) in [
            (
                "fn example(){let _=Parallel::map<int,int>([1],\\n->true)}",
                "E0301",
            ),
            (
                "fn example(){let _=Parallel::map<int>([1],\\n->n)}",
                "E0340",
            ),
            (
                "fn example(){let _=Parallel::map(values:[1],transform: \\n->n)}",
                "E0339",
            ),
            (
                "fn example(){let _=Parallel::join<int,int>(\\->true,\\->1)}",
                "E0301",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "expected {code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
}
