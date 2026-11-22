use ril_base::span::Span;
use ril_sema::{
    hir::DefinitionId,
    syntax::{Condition, Expr, ExprId, MatchArm, Name, Pattern, PatternId, Transfer},
    ty::{self, Ty, Value},
};

use super::{
    BlockId, Builder, DraftOp, IntLowering, Loop, ManagedInt, Register, Result, Target, Terminator,
    Work,
};

impl Builder<'_, '_> {
    pub(super) fn binary(
        &mut self,
        operator: &Name,
        left: ExprId,
        right: ExprId,
    ) -> Result<Register> {
        let token = operator.value.as_str();
        if matches!(token, "==" | "!=")
            && let (Some(Value::Type(left)), Some(Value::Type(right))) =
                (self.static_expr(left), self.static_expr(right))
        {
            return Ok(self.boolean((left == right) == (token == "==")));
        }
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
                } => Destination::Object(
                    self.expr(*base)?,
                    self.member_key(member)?,
                    self.is_draft(*base),
                ),
                Expr::Index {
                    base,
                    index,
                    safe: false,
                } => {
                    Destination::Object(self.expr(*base)?, self.expr(*index)?, self.is_draft(*base))
                }
                _ => return Err(self.unsupported(node.span, "non-addressable assignment")),
            };
            let current = if token == "=" {
                None
            } else {
                Some(match target {
                    Destination::Local(slot) => self.read(slot, node.span)?,
                    Destination::Object(base, key, draft) => {
                        let base = if draft {
                            self.draft(DraftOp::Read, vec![base])
                        } else {
                            base
                        };
                        self.runtime("ril_rt_load", vec![base, key])
                    }
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
                    if self.global.boxed.contains(&slot)
                        && let Some(&cell) = self.locals.get(&slot)
                    {
                        let key = self.integer("0");
                        self.runtime("ril_rt_store", vec![cell, key, right]);
                    } else {
                        self.locals.insert(slot, right);
                    }
                }
                Destination::Object(base, key, true) => {
                    self.draft(DraftOp::Write, vec![base, key, right]);
                }
                Destination::Object(base, key, false) => {
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
        let left_span = self.ast().expr(left).span;
        let result_fallback = op == "??"
            && matches!(
                self.global.typed.types.get(&left_span),
                Some(Ty::Result(..))
            );
        let value = self.expr(left)?;
        let names: Vec<_> = self.locals.keys().copied().collect();
        let rhs = self.block(0);
        let early = self.block(0);
        let join = self.block(1 + names.len());
        let (condition, yes, no) = match op {
            "??" => {
                let tag = self.string(if result_fallback { "Err" } else { "None" });
                (self.runtime("ril_rt_is_tag", vec![value, tag]), rhs, early)
            }
            "&&" => (value, rhs, early),
            _ => (value, early, rhs),
        };
        self.terminate(Terminator::Branch { condition, yes, no });
        self.current = Some(early);
        let early_value = if op == "??" {
            let zero = self.integer("0");
            self.runtime("ril_rt_load", vec![value, zero])
        } else {
            value
        };
        self.join_with(join, &names, early_value);
        self.current = Some(rhs);
        let mut right = self.expr(right)?;
        if result_fallback {
            let zero = self.integer("0");
            let error = self.runtime("ril_rt_load", vec![value, zero]);
            right = self.invoke_closure(right, vec![error]);
        }
        self.join_with(join, &names, right);
        Ok(self.join_result(join, &names))
    }

    pub(super) fn index(&mut self, base: Register, index: ExprId, safe: bool) -> Result<Register> {
        if let Expr::Range {
            start,
            end,
            inclusive,
        } = self.ast().expr(index).value
        {
            let start = if let Some(start) = start {
                self.expr(start)?
            } else {
                self.unit()
            };
            let end = if let Some(end) = end {
                self.expr(end)?
            } else {
                self.unit()
            };
            let inclusive = self.boolean(inclusive);
            Ok(self.runtime(
                if safe {
                    "ril_rt_safe_slice"
                } else {
                    "ril_rt_slice"
                },
                vec![base, start, end, inclusive],
            ))
        } else {
            let key = self.expr(index)?;
            Ok(self.runtime(
                if safe {
                    "ril_rt_safe_load"
                } else {
                    "ril_rt_load"
                },
                vec![base, key],
            ))
        }
    }

    pub(super) fn navigation(
        &mut self,
        base: ExprId,
        steps: &[ExprId],
        span: Span,
    ) -> Result<Register> {
        let mut receiver = self.global.typed.types.get(&self.ast().expr(base).span);
        let mut value = self.collection(base)?;
        let names: Vec<_> = self.locals.keys().copied().collect();
        let join = self.block(1 + names.len());
        for &step in steps {
            let node = self.ast().expr(step);
            match &node.value {
                Expr::Member { member, safe, .. } => {
                    if *safe {
                        value = self.navigation_payload(value, join, &names);
                    }
                    let key = self.member_key(member)?;
                    value = self.runtime("ril_rt_load", vec![value, key]);
                }
                Expr::Index { index, safe, .. } => {
                    if *safe
                        && receiver.is_some_and(|ty| matches!(self.concrete(ty), Ty::Option(_)))
                    {
                        value = self.navigation_payload(value, join, &names);
                    }
                    value = self.index(value, *index, *safe)?;
                    if *safe {
                        value = self.navigation_payload(value, join, &names);
                    }
                }
                _ => ril_base::ice!("unexpected navigation step"),
            }
            receiver = self.global.typed.navigation_values.get(&node.span);
        }
        if !self
            .global
            .typed
            .navigation_values
            .get(&span)
            .is_some_and(|ty| matches!(self.concrete(ty), Ty::Option(_)))
        {
            value = self.tag("Some", vec![value]);
        }
        self.join_with(join, &names, value);
        Ok(self.join_result(join, &names))
    }

    fn navigation_payload(
        &mut self,
        option: Register,
        join: BlockId,
        names: &[DefinitionId],
    ) -> Register {
        let none = self.string("None");
        let condition = self.runtime("ril_rt_is_tag", vec![option, none]);
        let missing = self.block(0);
        let present = self.block(0);
        self.terminate(Terminator::Branch {
            condition,
            yes: missing,
            no: present,
        });
        self.current = Some(missing);
        self.join_with(join, names, option);
        self.current = Some(present);
        let zero = self.integer("0");
        self.runtime("ril_rt_load", vec![option, zero])
    }

    fn join_result(&mut self, join: BlockId, names: &[DefinitionId]) -> Register {
        self.current = Some(join);
        for (&name, parameter) in names.iter().zip(self.params(join).into_iter().skip(1)) {
            self.locals.insert(name, parameter);
        }
        self.result_param(join)
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
        let prior_cleanups = self.cleanups.clone();
        let cleanups = prior_cleanups.len();
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
            counter: None,
        });
        self.current = Some(body_start);
        if let Some((pattern, value)) = binding {
            self.bind(pattern, value)?;
        }
        self.expr(body)?;
        self.loop_transfer(Transfer::Continue, self.ast().expr(body).span)?;
        self.loops.pop();
        self.cleanups = prior_cleanups;
        self.locals = before;
        self.current = Some(exit);
        for (name, param) in names.into_iter().zip(self.params(exit)) {
            self.locals.insert(name, param);
        }
        Ok(self.unit())
    }

    pub(super) fn for_loop(
        &mut self,
        iterable: ExprId,
        pattern: PatternId,
        body: ExprId,
    ) -> Result<Register> {
        let (start, end, collection, inclusive) = match self.ast().expr(iterable).value {
            Expr::Range {
                start: Some(start),
                end: Some(end),
                inclusive,
            } => (self.expr(start)?, self.expr(end)?, None, inclusive),
            _ => {
                let value = self.expr(iterable)?;
                let len = self.runtime("ril_rt_len", vec![value]);
                (self.integer("0"), len, Some(value), false)
            }
        };
        let before = self.locals.clone();
        let names: Vec<_> = before.keys().copied().collect();
        let header = self.block(names.len() + 1);
        let body_start = self.block(0);
        let exit_source = self.block(0);
        let exit = self.block(names.len());
        let prior_cleanups = self.cleanups.clone();
        let cleanups = prior_cleanups.len();
        self.terminate(Terminator::Jump(
            header,
            std::iter::once(start)
                .chain(before.values().copied())
                .collect(),
        ));
        self.current = Some(header);
        let mut incoming = self.params(header).into_iter();
        let current = incoming
            .next()
            .unwrap_or_else(|| ril_base::ice!("missing range counter"));
        for (&name, value) in names.iter().zip(incoming) {
            self.locals.insert(name, value);
        }
        let exits = names
            .iter()
            .filter_map(|id| self.locals.get(id).copied())
            .collect();
        self.term_at(exit_source, Terminator::Jump(exit, exits));
        let cond = self.runtime(
            if inclusive { "ril_rt_le" } else { "ril_rt_lt" },
            vec![current, end],
        );
        self.terminate(Terminator::Branch {
            condition: cond,
            yes: body_start,
            no: exit_source,
        });
        self.loops.push(Loop {
            header,
            exit,
            names: names.clone(),
            cleanups,
            counter: Some(current),
        });
        self.current = Some(body_start);
        let element = if let Some(collection) = collection {
            self.runtime("ril_rt_load", vec![collection, current])
        } else {
            current
        };
        self.bind(pattern, element)?;
        self.expr(body)?;
        self.loop_transfer(Transfer::Continue, self.ast().expr(body).span)?;
        self.loops.pop();
        self.cleanups = prior_cleanups;
        self.locals = before;
        self.current = Some(exit);
        for (name, value) in names.into_iter().zip(self.params(exit)) {
            self.locals.insert(name, value);
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
        let mut args = Vec::new();
        if transfer == Transfer::Continue
            && let Some(counter) = target.counter
        {
            let one = self.integer("1");
            let next = self.runtime("ril_rt_int_add", vec![counter, one]);
            args.push(next);
        }
        args.extend(
            target
                .names
                .iter()
                .filter_map(|id| self.locals.get(id).copied()),
        );
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
        if let Expr::Quote(id) = self.ast().expr(value).value {
            let ty = self
                .global
                .typed
                .types
                .get(&self.ast().ty(id).span)
                .map(|ty| self.concrete(ty))
                .unwrap_or(Ty::Unknown);
            for arm in arms {
                let old = self.types.clone();
                if self.static_pattern(arm.pattern, &ty) && arm.guard.is_none() {
                    let result = self.expr(arm.body);
                    self.types = old;
                    return result;
                }
                self.types = old;
            }
            return Err(self.unsupported(span, "dependent type match without a selected arm"));
        }
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
        self.terminate(Terminator::Unreachable);
        self.cleanups = cleanups;
        if active {
            self.current = Some(end);
            for (id, register) in names.into_iter().zip(self.params(end).into_iter().skip(1)) {
                self.locals.insert(id, register);
            }
            Ok(self.result_param(end))
        } else {
            Ok(self.register())
        }
    }

    fn static_pattern(&mut self, pattern: PatternId, target: &Ty) -> bool {
        match &self.ast().pattern(pattern).value {
            Pattern::Wildcard | Pattern::Binding(..) => true,
            Pattern::Type(ty) => self.static_type_pattern(*ty, target),
            Pattern::Or(parts) => parts.iter().any(|&part| self.static_pattern(part, target)),
            _ => false,
        }
    }

    fn static_type_pattern(&mut self, ty: ril_sema::syntax::TypeId, target: &Ty) -> bool {
        use ril_sema::syntax::Type;
        let node = self.ast().ty(ty);
        match (&node.value, target) {
            (Type::PatternWildcard, _) => true,
            (Type::PatternBinding(name), _) => {
                if let Some(id) = self.global.resolve(name.span) {
                    self.types.insert(id, target.clone());
                }
                true
            }
            (Type::Result(ok, err), Ty::Result(a, b)) => {
                self.static_type_pattern(*ok, a) && self.static_type_pattern(*err, b)
            }
            (Type::Option(item), Ty::Option(expected)) => self.static_type_pattern(*item, expected),
            (Type::Array(_, item), Ty::Array(expected)) => {
                self.static_type_pattern(*item, &expected.ty)
            }
            _ => self
                .global
                .typed
                .types
                .get(&node.span)
                .is_some_and(|ty| self.concrete(ty) == *target),
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
            Pattern::Slice { text, elements } => {
                self.test_slice(*text, elements, value, yes, no)?;
            }
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
            Pattern::Subset { .. } => {
                let tags = self
                    .global
                    .typed
                    .subset_tags
                    .get(&node.span)
                    .ok_or_else(|| {
                        self.unsupported(node.span, "subset pattern requires resolved sum tags")
                    })?;
                if tags.is_empty() {
                    self.terminate(Terminator::Jump(no, Vec::new()));
                }
                for (index, tag) in tags.iter().enumerate() {
                    let key = self.string(tag);
                    let condition = self.runtime("ril_rt_is_tag", vec![value, key]);
                    let last = index + 1 == tags.len();
                    let fallback = if last { no } else { self.block(0) };
                    self.terminate(Terminator::Branch {
                        condition,
                        yes,
                        no: fallback,
                    });
                    if !last {
                        self.current = Some(fallback);
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

    pub(super) fn bind_alternatives(
        &mut self,
        span: Span,
        items: &[PatternId],
        value: Register,
    ) -> Result<()> {
        let names = self.global.typed.hir.bindings_within(span);
        if names.is_empty() {
            return Ok(());
        }
        let prior = self.locals.clone();
        let merge = self.block(names.len());
        for &item in items {
            let selected = self.block(0);
            let retry = self.block(0);
            self.test_pattern(item, value, selected, retry)?;
            self.current = Some(selected);
            self.bind(item, value)?;
            let arguments = names
                .iter()
                .map(|id| {
                    self.locals
                        .get(id)
                        .copied()
                        .ok_or_else(|| self.unsupported(span, "missing alternative binding"))
                })
                .collect::<Result<Vec<_>>>()?;
            self.terminate(Terminator::Jump(merge, arguments));
            self.current = Some(retry);
            self.locals.clone_from(&prior);
        }
        self.terminate(Terminator::Unreachable);
        self.current = Some(merge);
        self.locals
            .extend(names.into_iter().zip(self.params(merge)));
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
        self.return_value(value)?;
        self.cleanups = prior;
        self.current = Some(continue_);
        let key = self.integer("0");
        Ok(self.runtime("ril_rt_load", vec![value, key]))
    }

    pub(super) fn return_value(&mut self, value: Register) -> Result<()> {
        self.cleanup_to(0);
        if !self.running_guard && !self.guards.is_empty() {
            self.run_exit_guards(value)?;
        }
        self.terminate(Terminator::Return(value));
        Ok(())
    }

    fn run_exit_guards(&mut self, value: Register) -> Result<()> {
        let check_some = self.block(0);
        let good = self.block(0);
        let done = self.block(0);
        let ok = self.string("Ok");
        let some = self.string("Some");
        let ok = self.runtime("ril_rt_is_tag", vec![value, ok]);
        self.terminate(Terminator::Branch {
            condition: ok,
            yes: good,
            no: check_some,
        });
        self.current = Some(check_some);
        let some = self.runtime("ril_rt_is_tag", vec![value, some]);
        self.terminate(Terminator::Branch {
            condition: some,
            yes: good,
            no: done,
        });
        self.current = Some(good);
        let zero = self.integer("0");
        let input = self.runtime("ril_rt_load", vec![value, zero]);
        for guard in self.guards.clone() {
            self.run_guard(guard, input)?;
        }
        self.terminate(Terminator::Jump(done, Vec::new()));
        self.current = Some(done);
        Ok(())
    }

    pub(super) fn run_guard(&mut self, guard: ExprId, value: Register) -> Result<()> {
        let ast = self.ast();
        let mut node = ast.expr(guard);
        if let Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        let (callee, args) = if let Expr::Call { callee, args } = &node.value {
            (ast.expr(*callee), args.as_slice())
        } else {
            (node, &[][..])
        };
        let Expr::Path(path) = &callee.value else {
            return Err(self.unsupported(node.span, "signature guard expression"));
        };
        let id = self
            .global
            .resolve(path.span)
            .ok_or_else(|| self.unsupported(node.span, "signature guard target"))?;
        let mut arguments = vec![value];
        for argument in args {
            arguments.push(self.expr(argument.value)?);
        }
        let captures = self.named_captures(id);
        let environment = (!captures.is_empty()).then(|| self.environment(&captures));
        let function = self.global.queue(Work::Named(
            id,
            Default::default(),
            captures,
            self.statics.clone(),
        ));
        let target = environment.map_or(Target::Function(function), |environment| {
            Target::FunctionWithEnv {
                function,
                environment,
            }
        });
        let output = self.invoke(target, arguments, false);
        let prior = std::mem::replace(&mut self.running_guard, true);
        self.propagate(output)?;
        self.running_guard = prior;
        Ok(())
    }

    fn static_expr(&self, expr: ExprId) -> Option<Value> {
        let node = self.ast().expr(expr);
        if let Some(value) = self.global.typed.static_values.get(&node.span) {
            return Some(value.clone());
        }
        match &node.value {
            Expr::Literal(literal) => ty::literal(literal).ok(),
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "==" | "!=") => {
                let (Value::Type(left), Value::Type(right)) =
                    (self.static_expr(*left)?, self.static_expr(*right)?)
                else {
                    return None;
                };
                Some(Value::Bool((left == right) == (op.value == "==")))
            }
            Expr::Quote(id) => self
                .global
                .typed
                .types
                .get(&self.ast().ty(*id).span)
                .map(|ty| Value::Type(Box::new(self.concrete(ty)))),
            Expr::Path(path) => {
                let id = self.global.resolve(path.span)?;
                if let Some(value) = self.statics.get(&id) {
                    return Some(value.clone());
                }
                let def = self.global.typed.hir.definition(id);
                match def.name.value.as_str() {
                    "OS" => Some(Value::Str(std::env::consts::OS.into())),
                    "ARCH" => Some(Value::Str(std::env::consts::ARCH.into())),
                    "HAS_OPENAT" => Some(Value::Bool(cfg!(unix))),
                    _ => {
                        let decl = def.stmt?;
                        let ast = &self.global.typed.hir.file(def.name.span.file).ast;
                        let ril_sema::syntax::StmtKind::Binding {
                            value: Some(value),
                            is_meta: true,
                            ..
                        } = ast.stmt(decl).value.kind
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
    Object(Register, Register, bool),
}
