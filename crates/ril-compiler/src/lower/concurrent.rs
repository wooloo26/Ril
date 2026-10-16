//! Bind only receiver methods whose builtin identity the checker certified.
use super::*;

impl Lower<'_> {
    pub(super) fn concurrent_receiver(
        &mut self,
        expression: &ast::Expr,
    ) -> Result<Option<ir::Expr>, NotImplemented> {
        let ast::ExprKind::Field {
            base,
            field,
            safe: false,
        } = &expression.kind
        else {
            return Ok(None);
        };
        let span = expression.span;
        let Some(operation) = self
            .specialized_builtins
            .get(&(span.file.0, span.start, span.end))
            .filter(|name| {
                matches!(
                    (name.as_str(), field.as_str()),
                    ("Concurrent::fork", "fork") | ("Concurrent::join", "join")
                )
            })
            .cloned()
        else {
            return Ok(None);
        };
        let owner = self.callable_owner.ok_or_else(|| {
            unsupported("bound concurrent adapter requires a verified lexical owner")
        })?;
        let causes: Vec<_> = self
            .facts
            .expressions
            .iter()
            .filter(|fact| fact.span == span)
            .map(|fact| fact.value.cause)
            .collect();
        if causes.is_empty() {
            return Err(unsupported(
                "bound concurrent adapter requires its builtin selection certificate",
            ));
        }
        self.nonretaining_adapters
            .push(ril_ir::provenance::NonRetainingAdapter {
                owner,
                span,
                builtin: if operation == "Concurrent::fork" {
                    ril_ir::provenance::NonRetainingBuiltin::ConcurrentFork
                } else {
                    ril_ir::provenance::NonRetainingBuiltin::ConcurrentJoin
                },
                causes,
            });
        let receiver = format!("\0ril.concurrent.receiver.{}", self.next_temporary);
        self.next_temporary += 1;
        let argument = format!("\0ril.concurrent.argument.{}", self.next_temporary);
        self.next_temporary += 1;
        let local = |name: &str| ir::Expr {
            kind: ir::ExprKind::Name(name.into()),
            span,
        };
        let mut parameters = vec![];
        let mut arguments = vec![ir::Argument {
            label: None,
            value: local(&receiver),
        }];
        if operation == "Concurrent::fork" {
            parameters.push(ir::Parameter {
                pattern: ir::Pattern::Name(argument.clone()),
                default: None,
            });
            arguments.push(ir::Argument {
                label: None,
                value: local(&argument),
            });
        }
        Ok(Some(ir::Expr {
            kind: ir::ExprKind::Block(ir::Block {
                statements: vec![
                    ir::Statement::Bind {
                        pattern: ir::Pattern::Name(receiver),
                        value: self.expression(base)?,
                        scoped: false,
                    },
                    ir::Statement::Expr {
                        expression: ir::Expr {
                            kind: ir::ExprKind::Lambda {
                                parameters,
                                body: Box::new(ir::Expr {
                                    kind: ir::ExprKind::Call {
                                        callback_entry: false,
                                        callee: Box::new(local(&operation)),
                                        arguments,
                                    },
                                    span,
                                }),
                            },
                            span,
                        },
                        terminated: false,
                    },
                ],
            }),
            span,
        }))
    }
}
