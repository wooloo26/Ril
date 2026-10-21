//! Lower original binding projections without inventing semantic AST nodes.
use super::*;
use crate::sema::source_types::WorkLimit;
use ril_compiler_core::{ids::PatternId, projection::TypeProjection};
use std::collections::{BTreeMap, BTreeSet};

pub(super) struct BindingPatterns {
    bindings: BTreeMap<PatternId, Vec<usize>>,
}

fn charge(work: &mut WorkLimit, units: usize) -> Result<(), NotImplemented> {
    work.charge(units)
        .map_err(|error| unsupported(format!("binding projection lowering: {error}")))
}

impl BindingPatterns {
    pub(super) fn new(facts: &crate::sema::SemanticFacts) -> Result<Self, NotImplemented> {
        let mut work = WorkLimit::new(4_000_000);
        charge(&mut work, facts.bindings.len())?;
        let mut bindings = BTreeMap::<_, Vec<_>>::new();
        for (index, binding) in facts.bindings.iter().enumerate() {
            charge(&mut work, 1)?;
            if let Some(pattern) = binding.pattern {
                bindings.entry(pattern).or_default().push(index);
            }
        }
        Ok(Self { bindings })
    }
}

struct Remainder {
    name: String,
    receiver: Vec<TypeProjection>,
    fields: BTreeSet<String>,
    scoped: bool,
}

impl Lower<'_> {
    fn binding_remainders(
        &self,
        pattern: &ast::Pattern,
        work: &mut WorkLimit,
    ) -> Result<Vec<Remainder>, NotImplemented> {
        let root = pattern
            .hir_id
            .ok_or_else(|| unsupported("binding lowering lost its original PatternId"))?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or_else(|| unsupported("binding lowering has no original HIR"))?;
        let mut remaining = work.remaining();
        let entries = hir
            .pattern_bindings(root, &mut remaining)
            .map_err(|error| unsupported(error.to_string()))?;
        let consumed = work.remaining() - remaining;
        charge(work, consumed)?;
        let mut remainders = Vec::new();
        for entry in entries {
            charge(work, 1)?;
            let Some(crate::hir::nodes::Pattern {
                kind:
                    crate::hir::nodes::PatternKind::Record {
                        rest_binding: Some(name),
                        ..
                    },
                ..
            }) = hir.pattern(entry.pattern)
            else {
                continue;
            };
            if name != &entry.name {
                return Err(unsupported("record remainder changed its original binding"));
            }
            let mut receiver = entry
                .projection
                .ok_or_else(|| unsupported("record remainder has an unresolved HIR projection"))?;
            let Some(TypeProjection::RecordRemainder(excluded)) = receiver.pop() else {
                return Err(unsupported("record remainder lost its original projection"));
            };
            if receiver
                .iter()
                .any(|step| !matches!(step, TypeProjection::Field(_) | TypeProjection::Tuple(_)))
            {
                return Err(unsupported(
                    "record remainder receiver needs a resolved Core projection",
                ));
            }
            let mut fields = None;
            let mut scoped = None;
            for &binding in self
                .binding_patterns
                .bindings
                .get(&entry.pattern)
                .into_iter()
                .flatten()
            {
                charge(work, 1)?;
                let info = self.facts.bindings.get(binding).ok_or_else(|| {
                    unsupported("record remainder binding is outside its original snapshot")
                })?;
                if info.name != entry.name || info.context.owner != self.callable_owner {
                    continue;
                }
                let current_scoped = matches!(
                    info.mode,
                    ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
                );
                if scoped.is_some_and(|previous| previous != current_scoped) {
                    return Err(unsupported("record remainder changed its binding mode"));
                }
                scoped = Some(current_scoped);
                let (schema, _) = self
                    .facts
                    .source_types
                    .binding_schema(binding, None, work)
                    .map_err(|error| {
                        unsupported(format!("record remainder Source view: {error}"))
                    })?;
                let current = schema.closed_record_labels(work).map_err(|error| {
                    unsupported(format!("record remainder field domain: {error}"))
                })?;
                if !current.is_disjoint(&excluded) {
                    return Err(unsupported("record remainder retained an excluded field"));
                }
                if fields.as_ref().is_some_and(|previous| previous != &current) {
                    return Err(unsupported(
                        "record remainder requires distinct native field shapes",
                    ));
                }
                fields = Some(current);
            }
            let fields = fields
                .ok_or_else(|| unsupported("record remainder has no original binding Source"))?;
            let scoped = scoped
                .ok_or_else(|| unsupported("record remainder has no original binding mode"))?;
            charge(work, 1)?;
            remainders.push(Remainder {
                name: entry.name,
                receiver,
                fields,
                scoped,
            });
        }
        Ok(remainders)
    }

    pub(super) fn binding_statements(
        &mut self,
        binding: &ast::Binding,
        span: Span,
    ) -> Result<Option<Vec<ir::Statement>>, NotImplemented> {
        let mut work = WorkLimit::new(1_000_000);
        let remainders = self.binding_remainders(&binding.pattern, &mut work)?;
        if remainders.is_empty() && binding.fallback.is_none() {
            return Ok(None);
        }
        if binding.is_meta {
            return Err(unsupported("static binding projection materialization"));
        }
        let pattern = self.lower_pattern(&binding.pattern, !remainders.is_empty())?;
        let value = self.expression(&binding.value)?;
        let temporary = format!("\0ril.binding.{}", self.next_temporary);
        self.next_temporary = self
            .next_temporary
            .checked_add(1)
            .ok_or_else(|| unsupported("binding temporary identity exhausted"))?;
        charge(&mut work, 3 + remainders.len())?;
        let mut statements = Vec::with_capacity(3 + remainders.len());
        statements.push(ir::Statement::Bind {
            pattern: ir::Pattern::Name(temporary.clone()),
            value,
            scoped: false,
        });
        let reference = ir::Expr {
            kind: ir::ExprKind::Name(temporary),
            span: binding.value.span,
        };
        if let Some(fallback) = &binding.fallback {
            statements.push(ir::Statement::Expr {
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
            });
        }
        let scoped = matches!(
            binding.mode,
            ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
        );
        statements.push(ir::Statement::Bind {
            pattern,
            value: reference.clone(),
            scoped,
        });
        for remainder in remainders {
            let cost = remainder
                .fields
                .len()
                .checked_mul(remainder.receiver.len() + 3)
                .ok_or_else(|| unsupported("binding projection work overflow"))?;
            charge(&mut work, cost)?;
            let mut fields = Vec::with_capacity(remainder.fields.len());
            for field in remainder.fields {
                charge(&mut work, 2 * field.len().div_ceil(32))?;
                let mut receiver = reference.clone();
                for step in &remainder.receiver {
                    let label = match step {
                        TypeProjection::Field(name) => {
                            charge(&mut work, name.len().div_ceil(32))?;
                            name.clone()
                        }
                        TypeProjection::Tuple(index) => index.to_string(),
                        _ => return Err(unsupported("unresolved record remainder receiver")),
                    };
                    receiver = ir::Expr {
                        kind: ir::ExprKind::Field {
                            base: Box::new(receiver),
                            field: label,
                            safe: false,
                        },
                        span: binding.pattern.span,
                    };
                }
                fields.push((
                    field.clone(),
                    ir::Expr {
                        kind: ir::ExprKind::Field {
                            base: Box::new(receiver),
                            field,
                            safe: false,
                        },
                        span: binding.pattern.span,
                    },
                ));
            }
            statements.push(ir::Statement::Bind {
                pattern: ir::Pattern::Name(remainder.name),
                value: ir::Expr {
                    kind: ir::ExprKind::Record {
                        members: fields
                            .iter()
                            .map(|(name, value)| {
                                ir::RecordMember::Field(name.clone(), value.clone())
                            })
                            .collect(),
                        fields,
                        spread: None,
                    },
                    span: binding.pattern.span,
                },
                scoped: remainder.scoped,
            });
        }
        Ok(Some(statements))
    }
}
