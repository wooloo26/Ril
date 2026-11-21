use ril_base::span::Span;
use ril_sema::{
    syntax::{Condition, Expr, ExprId, MatchArm, Name, Pattern, PatternId, Transfer},
    ty::{self, Value},
};

use super::{BlockId, Builder, IntLowering, Loop, ManagedInt, Register, Result, Terminator};

impl Builder<'_, '_> {
    pub(super) fn binary(
        &mut self,
        operator: &Name,
        left: ExprId,
        right: ExprId,
    ) -> Result<Register> {
        let token = operator.value.as_str();
        if matches!(token, "&&" | "||" | "??") {
            return self.short_circuit(left, right, token);
        }
        let assignment = matches!(
            token,
            "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | ">>=" | "<<="
        );
        if assignment {
            let node = self.ast().expr(left);
            let target = match &node.value {
                Expr::Path(path) => {
                    let slot = self.global.resolve(path.span).ok_or_else(|| {
                        self.unsupported(node.span, "unresolved local assignment")
                    })?;
                    Destination::Local(slot)
                }
                Expr::Member {
                    base,
                    member,
                    safe: false,
                } => Destination::Object(self.expr(*base)?, self.member_key(member)?),
                Expr::Index {
                    base,
                    index,
                    safe: false,
                } => Destination::Object(self.expr(*base)?, self.expr(*index)?),
                _ => return Err(self.unsupported(node.span, "non-addressable assignment")),
            };
            let current = if token == "=" {
                None
            } else {
                Some(match target {
                    Destination::Local(slot) => self.read(slot, node.span)?,
                    Destination::Object(base, key) => self.runtime("ril_rt_load", vec![base, key]),
                })
            };
            let mut right = self.expr(right)?;
            if let Some(current) = current {
                let token = token.strip_suffix('=').unwrap_or_default();
                let op = ManagedInt
                    .binary(token)
                    .ok_or_else(|| self.unsupported(operator.span, "compound operator"))?;
                right = self.runtime(op, vec![current, right]);
            }
            match target {
                Destination::Local(slot) => {
                    self.locals.insert(slot, right);
                }
                Destination::Object(base, key) => {
                    self.runtime("ril_rt_store", vec![base, key, right]);
                }
            }
            return Ok(self.unit());
        }
        let left = self.expr(left)?;
        let right = self.expr(right)?;
        let name = ManagedInt
            .binary(token)
            .ok_or_else(|| self.unsupported(operator.span, "binary operator"))?;
        Ok(self.runtime(name, vec![left, right]))
    }

    fn short_circuit(&mut self, left: ExprId, right: ExprId, op: &str) -> Result<Register> {
        let value = self.expr(left)?;
        let test = if op == "??" {
            let none = self.string("None");
            let err = self.string("Err");
            let is_none = self.runtime("ril_rt_is_tag", vec![value, none]);
            let is_err = self.runtime("ril_rt_is_tag", vec![value, err]);
            let fallback = self.block(0);
            let payload = self.block(0);
            let check_error = self.block(0);
            let join = self.block(1);
            self.terminate(Terminator::Branch {
                condition: is_none,
                yes: fallback,
                no: check_error,
            });
            self.current = Some(check_error);
            if matches!(
                self.ast().expr(right).value,
                Expr::Closure { .. } | Expr::Accessor(_)
            ) {
                let err_block = self.block(0);
                self.terminate(Terminator::Branch {
                    condition: is_err,
                    yes: err_block,
                    no: payload,
                });
                self.current = Some(err_block);
                let zero = self.integer("0");
                let err = self.runtime("ril_rt_load", vec![value, zero]);
                let result = self.inline_closure(right, &[err], self.ast().expr(right).span)?;
                self.terminate(Terminator::Jump(join, vec![result]));
            } else {
                self.terminate(Terminator::Jump(payload, Vec::new()));
            }
            self.current = Some(fallback);
            let result = if matches!(
                self.ast().expr(right).value,
                Expr::Closure { .. } | Expr::Accessor(_)
            ) {
                self.unit()
            } else {
                self.expr(right)?
            };
            self.terminate(Terminator::Jump(join, vec![result]));
            self.current = Some(payload);
            let zero = self.integer("0");
            let result = self.runtime("ril_rt_load", vec![value, zero]);
            self.terminate(Terminator::Jump(join, vec![result]));
            self.current = Some(join);
            return Ok(self.result_param(join));
        } else {
            value
        };
        let rhs = self.block(0);
        let early = self.block(0);
        let join = self.block(1);
        let (yes, no) = if op == "&&" {
            (rhs, early)
        } else {
            (early, rhs)
        };
        self.terminate(Terminator::Branch {
            condition: test,
            yes,
            no,
        });
        self.current = Some(early);
        self.terminate(Terminator::Jump(join, vec![value]));
        self.current = Some(rhs);
        let rhs = self.expr(right)?;
        self.terminate(Terminator::Jump(join, vec![rhs]));
        self.current = Some(join);
        Ok(self.result_param(join))
    }

    pub(super) fn result_param(&self, block: BlockId) -> Register {
        self.params(block)
            .first()
            .copied()
            .unwrap_or_else(|| ril_base::ice!("expected MIR block result parameter"))
    }

    pub(super) fn conditional(
        &mut self,
        condition: &Condition,
        yes: ExprId,
        no: Option<ExprId>,
    ) -> Result<Register> {
        if let Condition::Expr(test) = condition
            && let Some(Value::Bool(value)) = self.static_expr(*test)
        {
            return if value {
                self.expr(yes)
            } else if let Some(no) = no {
                self.expr(no)
            } else {
                Ok(self.unit())
            };
        }
        let yes_block = self.block(0);
        let no_block = self.block(0);
        let bindings = self.condition(condition, yes_block, no_block)?;
        let saved = self.locals.clone();
        let names: Vec<_> = saved.keys().copied().collect();
        let join = self.block(1 + names.len());
        let cleanups = self.cleanups.clone();
        self.current = Some(yes_block);
        if let Some((pattern, value)) = bindings {
            self.bind(pattern, value)?;
        }
        let result = self.expr(yes)?;
        let yes_normal = self.current.is_some();
        self.join_with(join, &names, result);
        self.locals.clone_from(&saved);
        self.cleanups.clone_from(&cleanups);
        self.current = Some(no_block);
        let result = if let Some(no) = no {
            self.expr(no)?
        } else {
            self.unit()
        };
        let no_normal = self.current.is_some();
        self.join_with(join, &names, result);
        self.cleanups = cleanups;
        self.locals = saved;
        if yes_normal || no_normal {
            self.current = Some(join);
            for (id, parameter) in names.into_iter().zip(self.params(join).into_iter().skip(1)) {
                self.locals.insert(id, parameter);
            }
            Ok(self.result_param(join))
        } else {
            Ok(self.register())
        }
    }

    fn join_with(
        &mut self,
        block: BlockId,
        names: &[ril_sema::hir::DefinitionId],
        value: Register,
    ) {
        let args = std::iter::once(value)
            .chain(names.iter().filter_map(|id| self.locals.get(id).copied()))
            .collect();
        self.terminate(Terminator::Jump(block, args));
    }

    fn condition(
        &mut self,
        condition: &Condition,
        yes: BlockId,
        no: BlockId,
    ) -> Result<Option<(PatternId, Register)>> {
        match condition {
            Condition::Expr(expr) => {
                let condition = self.expr(*expr)?;
                self.terminate(Terminator::Branch { condition, yes, no });
                Ok(None)
            }
            Condition::Binding { value, pattern, .. } => {
                let value = self.expr(*value)?;
                self.test_pattern(*pattern, value, yes, no)?;
                Ok(Some((*pattern, value)))
            }
        }
    }

    pub(super) fn while_loop(&mut self, condition: &Condition, body: ExprId) -> Result<Register> {
        let before = self.locals.clone();
        let names: Vec<_> = before.keys().copied().collect();
        let header = self.block(names.len());
        let body_start = self.block(0);
        let exit_source = self.block(0);
        let exit = self.block(names.len());
        let cleanups = self.cleanups.len();
        self.terminate(Terminator::Jump(header, before.values().copied().collect()));
        self.current = Some(header);
        for (&name, param) in names.iter().zip(self.params(header)) {
            self.locals.insert(name, param);
        }
        let args = names
            .iter()
            .filter_map(|id| self.locals.get(id).copied())
            .collect();
        self.term_at(exit_source, Terminator::Jump(exit, args));
        let binding = self.condition(condition, body_start, exit_source)?;
        self.loops.push(Loop {
            header,
            exit,
            names: names.clone(),
            cleanups,
        });
        self.current = Some(body_start);
        if let Some((pattern, value)) = binding {
            self.bind(pattern, value)?;
        }
        self.expr(body)?;
        self.loop_transfer(Transfer::Continue, self.ast().expr(body).span)?;
        self.loops.pop();
        self.locals = before;
        self.current = Some(exit);
        for (name, param) in names.into_iter().zip(self.params(exit)) {
            self.locals.insert(name, param);
        }
        Ok(self.unit())
    }

    pub(super) fn loop_transfer(&mut self, transfer: Transfer, span: Span) -> Result<()> {
        if self.current.is_none() {
            return Ok(());
        }
        let target = self
            .loops
            .last()
            .cloned()
            .ok_or_else(|| self.unsupported(span, "loop control outside a loop"))?;
        self.cleanup_to(target.cleanups);
        let args = target
            .names
            .iter()
            .filter_map(|id| self.locals.get(id).copied())
            .collect();
        let label = if transfer == Transfer::Break {
            target.exit
        } else {
            target.header
        };
        self.terminate(Terminator::Jump(label, args));
        Ok(())
    }

    pub(super) fn match_expr(
        &mut self,
        value: ExprId,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<Register> {
        let value = self.expr(value)?;
        let saved = self.locals.clone();
        let names: Vec<_> = saved.keys().copied().collect();
        let cleanups = self.cleanups.clone();
        let end = self.block(names.len() + 1);
        let mut active = false;
        for arm in arms {
            let success = self.block(0);
            let failure = self.block(0);
            self.test_pattern(arm.pattern, value, success, failure)?;
            self.current = Some(success);
            self.bind(arm.pattern, value)?;
            if let Some(guard) = arm.guard {
                let condition = self.expr(guard)?;
                let passed = self.block(0);
                self.terminate(Terminator::Branch {
                    condition,
                    yes: passed,
                    no: failure,
                });
                self.current = Some(passed);
            }
            let result = self.expr(arm.body)?;
            active |= self.current.is_some();
            self.join_with(end, &names, result);
            self.locals.clone_from(&saved);
            self.cleanups.clone_from(&cleanups);
            self.current = Some(failure);
        }
        let message = self.string("non-exhaustive match reached");
        self.runtime("ril_rt_panic", vec![message]);
        let unit = self.unit();
        self.return_value(unit);
        if active {
            self.current = Some(end);
            for (id, register) in names.into_iter().zip(self.params(end).into_iter().skip(1)) {
                self.locals.insert(id, register);
            }
            Ok(self.result_param(end))
        } else {
            Err(self.unsupported(span, "no normal match branch"))
        }
    }

    pub(super) fn test_pattern(
        &mut self,
        id: PatternId,
        value: Register,
        yes: BlockId,
        no: BlockId,
    ) -> Result<()> {
        let node = self.ast().pattern(id);
        match &node.value {
            Pattern::Binding(..) | Pattern::Wildcard | Pattern::Unit => {
                self.terminate(Terminator::Jump(yes, Vec::new()));
            }
            Pattern::Literal(syntax) => {
                let expected = ty::literal(syntax)
                    .map_err(|_| self.unsupported(node.span, "invalid pattern literal"))?;
                let expected = self.constant(&expected, node.span)?;
                let equal = self.runtime("ril_rt_equal", vec![value, expected]);
                self.terminate(Terminator::Branch {
                    condition: equal,
                    yes,
                    no,
                });
            }
            Pattern::Constructor(path, payload) => {
                let tag = path
                    .segments
                    .last()
                    .map(|part| part.name.value.as_str())
                    .ok_or_else(|| self.unsupported(node.span, "invalid constructor pattern"))?;
                let tag = self.string(tag);
                let test = self.runtime("ril_rt_is_tag", vec![value, tag]);
                let Some(items) = payload.as_ref().filter(|items| !items.is_empty()) else {
                    self.terminate(Terminator::Branch {
                        condition: test,
                        yes,
                        no,
                    });
                    return Ok(());
                };
                let entry = self.block(0);
                self.terminate(Terminator::Branch {
                    condition: test,
                    yes: entry,
                    no,
                });
                self.current = Some(entry);
                self.test_parts(items, value, yes, no)?;
            }
            Pattern::Tuple(items) => self.test_parts(items, value, yes, no)?,
            Pattern::Record { fields, .. } => {
                for item in fields.iter().filter(|item| item.pattern.is_some()) {
                    if let Some(pattern) = item.pattern {
                        let key = self.string(&item.name.value);
                        let field = self.runtime("ril_rt_load", vec![value, key]);
                        let next = self.block(0);
                        self.test_pattern(pattern, field, next, no)?;
                        self.current = Some(next);
                    }
                }
                self.terminate(Terminator::Jump(yes, Vec::new()));
            }
            Pattern::Or(items) => {
                for (index, &item) in items.iter().enumerate() {
                    let last = index + 1 == items.len();
                    let next = if last { no } else { self.block(0) };
                    self.test_pattern(item, value, yes, next)?;
                    if !last {
                        self.current = Some(next);
                    }
                }
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                let lower = self.constant(
                    &ty::literal(low)
                        .map_err(|_| self.unsupported(node.span, "invalid range endpoint"))?,
                    node.span,
                )?;
                let upper = self.constant(
                    &ty::literal(high)
                        .map_err(|_| self.unsupported(node.span, "invalid range endpoint"))?,
                    node.span,
                )?;
                let low = self.runtime("ril_rt_ge", vec![value, lower]);
                let next = self.block(0);
                self.terminate(Terminator::Branch {
                    condition: low,
                    yes: next,
                    no,
                });
                self.current = Some(next);
                let high = self.runtime(
                    if *inclusive { "ril_rt_le" } else { "ril_rt_lt" },
                    vec![value, upper],
                );
                self.terminate(Terminator::Branch {
                    condition: high,
                    yes,
                    no,
                });
            }
            _ => return Err(self.unsupported(node.span, "this match pattern")),
        }
        Ok(())
    }

    fn test_parts(
        &mut self,
        items: &[PatternId],
        value: Register,
        yes: BlockId,
        no: BlockId,
    ) -> Result<()> {
        for (index, &item) in items.iter().enumerate() {
            let key = self.integer(&index.to_string());
            let value = self.runtime("ril_rt_load", vec![value, key]);
            let next = self.block(0);
            self.test_pattern(item, value, next, no)?;
            self.current = Some(next);
        }
        self.terminate(Terminator::Jump(yes, Vec::new()));
        Ok(())
    }

    pub(super) fn propagate(&mut self, value: Register) -> Result<Register> {
        let err = self.string("Err");
        let none = self.string("None");
        let check_none = self.block(0);
        let fail = self.block(0);
        let continue_ = self.block(0);
        let is_err = self.runtime("ril_rt_is_tag", vec![value, err]);
        self.terminate(Terminator::Branch {
            condition: is_err,
            yes: fail,
            no: check_none,
        });
        self.current = Some(check_none);
        let is_none = self.runtime("ril_rt_is_tag", vec![value, none]);
        self.terminate(Terminator::Branch {
            condition: is_none,
            yes: fail,
            no: continue_,
        });
        self.current = Some(fail);
        let prior = self.cleanups.clone();
        self.return_value(value);
        self.cleanups = prior;
        self.current = Some(continue_);
        let key = self.integer("0");
        Ok(self.runtime("ril_rt_load", vec![value, key]))
    }

    pub(super) fn return_value(&mut self, value: Register) {
        if let Some((target, depth)) = self.capture_return {
            self.cleanup_to(depth);
            self.terminate(Terminator::Jump(target, vec![value]));
        } else {
            self.cleanup_to(0);
            self.terminate(Terminator::Return(value));
        }
    }

    fn static_expr(&self, expr: ExprId) -> Option<Value> {
        let node = self.ast().expr(expr);
        if let Some(value) = self.global.typed.static_values.get(&node.span) {
            return Some(value.clone());
        }
        match &node.value {
            Expr::Literal(literal) => ty::literal(literal).ok(),
            Expr::Path(path) => {
                let id = self.global.resolve(path.span)?;
                let def = self.global.typed.hir.definition(id);
                match def.name.value.as_str() {
                    "OS" => Some(Value::Str(std::env::consts::OS.into())),
                    "ARCH" => Some(Value::Str(std::env::consts::ARCH.into())),
                    "HAS_OPENAT" => Some(Value::Bool(cfg!(unix))),
                    _ => {
                        let ast = &self.global.typed.hir.file(def.name.span.file).ast;
                        let ril_sema::syntax::StmtKind::Binding {
                            value: Some(value),
                            is_meta: true,
                            ..
                        } = ast.stmt(def.stmt?).value.kind
                        else {
                            return None;
                        };
                        self.global
                            .typed
                            .static_values
                            .get(&ast.expr(value).span)
                            .cloned()
                    }
                }
            }
            Expr::Binary { op, left, right } => {
                let left = self.static_expr(*left)?;
                let right = self.static_expr(*right)?;
                ty::arithmetic(&op.value, left, right).ok()
            }
            Expr::Unary { op, value } if op.value == "!" => match self.static_expr(*value)? {
                Value::Bool(value) => Some(Value::Bool(!value)),
                _ => None,
            },
            _ => None,
        }
    }
}

enum Destination {
    Local(ril_sema::hir::DefinitionId),
    Object(Register, Register),
}
