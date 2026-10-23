//! Guarded binding lowering preserves one subject evaluation and installs
//! binders only after the shared Core pattern succeeds.
use super::*;

impl Lower<'_> {
    pub(super) fn binding_statements(
        &mut self,
        binding: &ast::Binding,
        span: Span,
    ) -> Result<Option<Vec<ir::Statement>>, NotImplemented> {
        let Some(fallback) = &binding.fallback else {
            return Ok(None);
        };
        if binding.is_meta {
            return Err(unsupported("static binding projection materialization"));
        }
        let pattern = self.pattern(&binding.pattern)?;
        let value = self.expression(&binding.value)?;
        let temporary = format!("\0ril.binding.{}", self.next_temporary);
        self.next_temporary = self
            .next_temporary
            .checked_add(1)
            .ok_or_else(|| unsupported("binding temporary identity exhausted"))?;
        let reference = ir::Expr {
            kind: ir::ExprKind::Name(temporary.clone()),
            span: binding.value.span,
        };
        Ok(Some(vec![
            ir::Statement::Bind {
                pattern: ir::Pattern::Name(temporary),
                value,
                scoped: false,
            },
            ir::Statement::Expr {
                expression: ir::Expr {
                    kind: ir::ExprKind::If {
                        condition: Box::new(ir::Expr {
                            kind: ir::ExprKind::Is {
                                value: Box::new(reference.clone()),
                                pattern: binding_test(&pattern),
                            },
                            span: binding.pattern.span,
                        }),
                        then_branch: Box::new(ir::Expr {
                            kind: ir::ExprKind::Literal(ir::Literal::Unit),
                            span,
                        }),
                        else_branch: Some(Box::new(self.expression(fallback)?)),
                    },
                    span,
                },
                terminated: true,
            },
            ir::Statement::Bind {
                pattern,
                value: reference,
                scoped: matches!(
                    binding.mode,
                    ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
                ),
            },
        ]))
    }
}
