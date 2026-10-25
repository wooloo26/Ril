//! Abstract events are distinct from native continuation bookkeeping.
use super::*;
impl Builder {
    pub(super) fn charge(
        &mut self,
        event: Option<core::ChargeEvent>,
        span: Span,
        next: BlockId,
    ) -> BlockId {
        if self.metered
            && let Some(event) = event
        {
            self.block(
                Input::Continue(None),
                vec![],
                Terminator::Charge { event, span, next },
            )
        } else {
            next
        }
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn budget(
        &mut self,
        limit: &Expr,
        action: &Expr,
        exhaustion_operation: u64,
        coverage: ril_compiler_core::diagnostic::CauseId,
        destination: &str,
        next: BlockId,
        span: Span,
    ) -> Result<BlockId, NotImplemented> {
        let first = self.temporary();
        let second = self.temporary();
        let next = self.continuation(destination, next);
        let enter = self.block(
            Input::Continue(None),
            vec![],
            Terminator::Budget {
                limit: name(&first, limit.span),
                action: name(&second, action.span),
                exhaustion_operation,
                coverage,
                span,
                next,
            },
        );
        let entry = self.values(&[limit.clone(), action.clone()], &[first, second], enter)?;
        // Only this structural action position guarantees immediate invocation
        // while the selected handler chain is live. Names/aliases and every
        // other callable creation retain the existing escape/context gate.
        if matches!(action.kind, ExprKind::Lambda { .. }) {
            self.retained_lambdas
                .remove(&(action.span.file.0, action.span.start, action.span.end));
        }
        Ok(entry)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::{ids::DefinitionId, source::FileId};
    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 0,
            end: 1,
        }
    }
    fn expr(kind: ExprKind) -> Expr {
        expression(kind, span())
    }
    fn statement(expression: Expr) -> Statement {
        Statement::Expr {
            expression,
            terminated: true,
        }
    }
    fn function(role: core::FunctionRole, statements: Vec<Statement>) -> core::Function {
        core::Function {
            role,
            definition: DefinitionId(0),
            name: "main".into(),
            generic_parameters: vec![],
            parameters: vec![],
            body: core::Block { statements },
            span: span(),
        }
    }
    fn count(graph: &cps::Function, event: core::ChargeEvent) -> usize {
        graph.blocks.iter().filter(|block|matches!(block.terminator,Terminator::Charge {event:found,..}if found==event)).count()
    }
    #[test]
    fn source_loop_headers_and_function_entry_are_explicit_metered_events() {
        let source = function(
            core::FunctionRole::Ordinary,
            vec![
                statement(expr(ExprKind::While {
                    condition: Box::new(expr(ExprKind::Literal(core::Literal::Bool(false)))),
                    body: core::Block::default(),
                    charge: Some(core::ChargeEvent::LoopIteration),
                })),
                statement(expr(ExprKind::For {
                    iterable: Box::new(expr(ExprKind::Array(vec![]))),
                    pattern: Pattern::Wildcard,
                    body: core::Block::default(),
                    charge: Some(core::ChargeEvent::LoopIteration),
                })),
                statement(expr(ExprKind::Loop {
                    body: core::Block {
                        statements: vec![statement(expr(ExprKind::Control {
                            operation: core::ControlOperation::Last,
                            value: None,
                        }))],
                    },
                    charge: None,
                })),
            ],
        );
        let ordinary = lower(&source).unwrap();
        assert_eq!(count(&ordinary, core::ChargeEvent::FunctionEntry), 0);
        assert_eq!(count(&ordinary, core::ChargeEvent::LoopIteration), 0);
        let metered = lower_metered(&source).unwrap();
        assert_eq!(count(&metered, core::ChargeEvent::FunctionEntry), 1);
        assert_eq!(count(&metered, core::ChargeEvent::LoopIteration), 2);
        let Terminator::Jump(next) = metered.blocks[metered.entry.0 as usize].terminator else {
            panic!("function input must precede the entry charge")
        };
        assert!(matches!(
            metered.blocks[next.0 as usize].terminator,
            Terminator::Charge {
                event: core::ChargeEvent::FunctionEntry,
                ..
            }
        ));
    }
    #[test]
    fn handler_and_resume_events_do_not_turn_synthetic_blocks_into_function_entries() {
        let source = function(
            core::FunctionRole::Synthetic,
            vec![
                Statement::Handle {
                    definition: 0,
                    arms: vec![core::HandlerArm {
                        operation: 7,
                        parameters: vec![],
                        body: expr(ExprKind::Control {
                            operation: core::ControlOperation::Resume,
                            value: None,
                        }),
                    }],
                },
                statement(expr(ExprKind::Perform {
                    operation: 7,
                    arguments: vec![],
                })),
            ],
        );
        let graph = lower_metered(&source).unwrap();
        assert_eq!(count(&graph, core::ChargeEvent::FunctionEntry), 0);
        assert_eq!(count(&graph, core::ChargeEvent::HandlerEntry), 1);
        assert_eq!(count(&graph, core::ChargeEvent::Resume), 1);
    }

    #[test]
    fn sequential_callback_entries_survive_cps_without_marking_internal_primitives() {
        let invocation = |callee: &str, callback_entry| {
            statement(expr(ExprKind::Call {
                callback_entry,
                callee: Box::new(expr(ExprKind::Name(callee.into()))),
                arguments: vec![],
            }))
        };
        let source = function(
            core::FunctionRole::Ordinary,
            vec![
                invocation("len", false),
                invocation("action", true),
                invocation("storage_push", false),
            ],
        );
        for graph in [lower(&source).unwrap(), lower_metered(&source).unwrap()] {
            let callbacks = graph
                .blocks
                .iter()
                .filter(|block| {
                    matches!(
                        block.terminator,
                        Terminator::Call {
                            callback_entry: true,
                            ..
                        }
                    )
                })
                .count();
            let primitives = graph
                .blocks
                .iter()
                .filter(|block| {
                    matches!(
                        block.terminator,
                        Terminator::Call {
                            callback_entry: false,
                            ..
                        }
                    )
                })
                .count();
            assert_eq!(callbacks, 1, "one actual callback entry");
            assert!(primitives >= 2, "length and push remain primitive calls");
        }
    }

    #[test]
    fn only_a_structural_immediate_budget_lambda_avoids_the_retained_context_gate() {
        let lambda = |start| Expr {
            span: Span {
                start,
                end: start + 1,
                ..span()
            },
            kind: ExprKind::Lambda {
                parameters: vec![],
                body: Box::new(expr(ExprKind::Perform {
                    operation: 43,
                    arguments: vec![],
                })),
            },
        };
        let source = function(
            core::FunctionRole::Ordinary,
            vec![
                Statement::Handle {
                    definition: 0,
                    arms: vec![core::HandlerArm {
                        operation: 43,
                        parameters: vec![],
                        body: expr(ExprKind::Control {
                            operation: core::ControlOperation::Resume,
                            value: None,
                        }),
                    }],
                },
                Statement::Bind {
                    pattern: Pattern::Name("stored".into()),
                    value: lambda(2),
                    scoped: false,
                },
                statement(expr(ExprKind::Budget {
                    limit: Box::new(expr(ExprKind::Literal(core::Literal::Integer {
                        value: 1,
                        bits: 64,
                        signed: true,
                    }))),
                    action: Box::new(lambda(4)),
                    exhaustion_operation: 44,
                    coverage: ril_compiler_core::diagnostic::CauseId(0),
                })),
            ],
        );
        let graph = lower(&source).unwrap();
        assert!(graph.retained_lambdas.contains(&(0, 2, 3)));
        assert!(!graph.retained_lambdas.contains(&(0, 4, 5)));
    }
}
