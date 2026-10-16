//! Empty handler selection is certified for exact generated builtin adapters.
//! It says nothing about whether their receiver environment may escape or copy.
use super::*;
use ril_ir::provenance::NonRetainingBuiltin;

pub(super) type Adapters = HashMap<(CallableOwner, (u32, u32, u32)), NonRetainingBuiltin>;

pub(super) fn certificates(input: &native::Module) -> Result<Adapters, BackendError> {
    let mut adapters = HashMap::new();
    for proof in &input.nonretaining_adapters {
        if proof.causes.is_empty() {
            return Err(BackendError::InvalidIr(
                "non-retaining adapter has no builtin selection evidence".into(),
            ));
        }
        let key = (
            proof.owner,
            (proof.span.file.0, proof.span.start, proof.span.end),
        );
        if let Some(previous) = adapters.insert(key, proof.builtin)
            && previous != proof.builtin
        {
            return Err(BackendError::InvalidIr(
                "conflicting non-retaining adapter identities".into(),
            ));
        }
    }
    Ok(adapters)
}

pub(super) fn validate(
    builtin: NonRetainingBuiltin,
    source_callable: Option<CallableOwner>,
    parameters: &[core::Parameter],
    body: &Expr,
    captures: &[String],
    prepared: &Prepared,
) -> Result<(), BackendError> {
    let (expected, arity) = match builtin {
        NonRetainingBuiltin::ConcurrentFork => ("Concurrent::fork", 1),
        NonRetainingBuiltin::ConcurrentJoin => ("Concurrent::join", 0),
    };
    let invalid = || {
        BackendError::InvalidIr(
            "non-retaining adapter certificate does not match its generated builtin body".into(),
        )
    };
    if source_callable.is_some()
        || parameters.len() != arity
        || prepared.callable_owners.contains_key(expected)
        || prepared.globals.contains(expected)
    {
        return Err(invalid());
    }
    let ExprKind::Call {
        callback_entry: false,
        callee,
        arguments,
    } = &body.kind
    else {
        return Err(invalid());
    };
    let [receiver] = captures else {
        return Err(invalid());
    };
    if !matches!(&callee.kind, ExprKind::Name(name) if name == expected)
        || receiver == expected
        || arguments.len() != arity + 1
        || arguments.iter().any(|argument| argument.label.is_some())
        || !matches!(&arguments[0].value.kind, ExprKind::Name(name) if name == receiver)
    {
        return Err(invalid());
    }
    for (parameter, argument) in parameters.iter().zip(&arguments[1..]) {
        if parameter.default.is_some()
            || !matches!((&parameter.pattern, &argument.value.kind), (Pattern::Name(parameter), ExprKind::Name(argument)) if parameter == argument && parameter != expected)
        {
            return Err(invalid());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::{
        diagnostic::CauseId,
        ids::{ClosureSiteId, DefinitionId},
        source::{FileId, Span},
    };
    use ril_ir::provenance::{ClosureSite, NonRetainingAdapter};

    fn module(builtin: NonRetainingBuiltin) -> native::Module {
        let span = Span {
            file: FileId(0),
            start: 10,
            end: 20,
        };
        let expression = |kind| Expr { span, kind };
        let name = |text: &str| expression(ExprKind::Name(text.into()));
        let (operation, parameters, mut arguments) = match builtin {
            NonRetainingBuiltin::ConcurrentFork => (
                "Concurrent::fork",
                vec![core::Parameter {
                    pattern: Pattern::Name("action".into()),
                    default: None,
                }],
                vec![
                    core::Argument {
                        label: None,
                        value: name("receiver"),
                    },
                    core::Argument {
                        label: None,
                        value: name("action"),
                    },
                ],
            ),
            NonRetainingBuiltin::ConcurrentJoin => (
                "Concurrent::join",
                vec![],
                vec![core::Argument {
                    label: None,
                    value: name("receiver"),
                }],
            ),
        };
        let program = core::Program {
            functions: vec![core::Function {
                role: core::FunctionRole::Ordinary,
                definition: DefinitionId(0),
                name: "main".into(),
                parameters: vec![],
                generic_parameters: vec![],
                span,
                body: core::Block {
                    statements: vec![
                        Statement::Bind {
                            pattern: Pattern::Name("receiver".into()),
                            value: expression(ExprKind::Literal(Literal::Unit)),
                            scoped: false,
                        },
                        Statement::Handle {
                            definition: 1,
                            arms: vec![],
                        },
                        Statement::Expr {
                            terminated: false,
                            expression: expression(ExprKind::Lambda {
                                parameters,
                                body: Box::new(expression(ExprKind::Call {
                                    callback_entry: false,
                                    callee: Box::new(name(operation)),
                                    arguments: std::mem::take(&mut arguments),
                                })),
                            }),
                        },
                    ],
                },
            }],
            provenance: ril_ir::provenance::Graph {
                nonretaining_adapters: vec![NonRetainingAdapter {
                    owner: CallableOwner::Function(DefinitionId(0)),
                    span,
                    builtin,
                    causes: vec![CauseId(0)],
                }],
                ..Default::default()
            },
            ..Default::default()
        };
        ril_codegen::lower::lower_native(&program).unwrap()
    }

    #[test]
    fn exact_adapter_proofs_preserve_receiver_captures_without_retained_wrappers() {
        for builtin in [
            NonRetainingBuiltin::ConcurrentFork,
            NonRetainingBuiltin::ConcurrentJoin,
        ] {
            let input = module(builtin);
            let prepared = super::super::prepare(&input).unwrap();
            let name = prepared.lambdas.values().next().unwrap();
            assert_eq!(
                prepared.captures[name].len(),
                1,
                "the certificate cannot erase the captured receiver"
            );
            assert!(!prepared.retained_handlers.contains_key(name));
        }
    }

    #[test]
    fn missing_wrong_or_source_callable_certificates_cannot_skip_retention_checks() {
        for change in 0..5 {
            let mut input = module(NonRetainingBuiltin::ConcurrentFork);
            let site = input.nonretaining_adapters[0].span;
            match change {
                0 => input.nonretaining_adapters.clear(),
                1 => {
                    input.nonretaining_adapters[0].owner = CallableOwner::Function(DefinitionId(99))
                }
                2 => input.nonretaining_adapters[0].builtin = NonRetainingBuiltin::ConcurrentJoin,
                3 => input.closure_sites.push(ClosureSite {
                    id: ClosureSiteId(0),
                    owner: CallableOwner::Function(DefinitionId(0)),
                    span: site,
                }),
                _ => input.nonretaining_adapters[0].causes.clear(),
            }
            assert!(
                super::super::prepare(&input).is_err(),
                "invalid certificate case {change}"
            );
        }
    }
}
