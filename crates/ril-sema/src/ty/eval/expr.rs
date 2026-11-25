use std::collections::BTreeMap;

use ril_hir::{DefinitionId, DefinitionKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{
    self, Argument, Condition, Expr, ExprId, Mode, StmtKind, StringPart, Transfer,
};

use super::{Budget, Eval, Frame, Signal, Values, defect, none, nonstatic, optional_payload};
use crate::ty::{
    GenericValue, MemberMode, Ty, Value, arithmetic,
    check::{Checker, Env},
    literal, render,
    value::{decode_text, ieee_equal},
};

impl Checker<'_> {
    pub(super) fn eval_expr(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        expr: ExprId,
        fuel: &mut Budget,
    ) -> Eval {
        let ast = self.ast(env.file);
        let node = ast.expr(expr);
        let span = node.span;
        if let Some((base, steps)) = ast.navigation_chain(expr) {
            let mut value = self.evaluate(env, slots, base, fuel)?;
            for step in steps {
                let step = ast.expr(step);
                match &step.value {
                    Expr::Member { member, safe, .. } => {
                        if *safe {
                            let Some(payload) = optional_payload(value, step.span)? else {
                                return Ok(none());
                            };
                            value = payload;
                        }
                        value = self.eval_member(env, slots, member, value, step.span, fuel)?;
                    }
                    Expr::Index { index, safe, .. } => {
                        if *safe && matches!(value, Value::Tag(..)) {
                            let Some(payload) = optional_payload(value, step.span)? else {
                                return Ok(none());
                            };
                            value = payload;
                        }
                        value = match self.eval_index(env, slots, value, *index, fuel)? {
                            Some(found) => found,
                            None if *safe => return Ok(none()),
                            None => return Err(defect(step.span, "static index is out of bounds")),
                        };
                    }
                    _ => ril_source::ice!("unexpected static navigation step"),
                }
            }
            return if self
                .navigation_values
                .get(&span)
                .is_some_and(|ty| matches!(self.normalize(ty), Ty::Option(_)))
            {
                Ok(value)
            } else {
                Ok(Value::Tag("Some".into(), vec![value]))
            };
        }
        match &node.value {
            Expr::Literal(value) => {
                literal(value).map_err(|_| defect(span, "invalid static literal"))
            }
            Expr::Unit => Ok(Value::Unit),
            Expr::Path(path) => self.eval_path(env, slots, path, fuel),
            Expr::Quote(ty) => {
                let mut quoted = env.clone();
                quoted.generics.extend(
                    slots
                        .locals
                        .iter()
                        .map(|(&id, value)| (id, GenericValue::Data(value.clone()))),
                );
                let represented = self.type_expr(&mut quoted, *ty);
                if env.require_concrete_types && represented.has_unresolved_static_type() {
                    return Err(Signal::Dependent(span));
                }
                Ok(Value::Type(Box::new(represented)))
            }
            Expr::Unary { op, value } => {
                let value = self.evaluate(env, slots, *value, fuel)?;
                match (op.value.as_str(), value) {
                    ("-", Value::Int(v)) => Ok(Value::Int(-v)),
                    ("-", Value::F64(v)) => Ok(Value::F64((-f64::from_bits(v)).to_bits())),
                    ("!", Value::Bool(v)) => Ok(Value::Bool(!v)),
                    ("~", Value::Int(v)) => Ok(Value::Int(!v)),
                    ("ref" | "new" | "^mut", v) => Ok(v),
                    ("?", Value::Tag(tag, mut values)) if matches!(tag.as_str(), "Some" | "Ok") => {
                        Ok(values.pop().unwrap_or(Value::Unit))
                    }
                    ("?", Value::Tag(tag, values)) if matches!(tag.as_str(), "Err" | "None") => {
                        Err(Signal::Return(Value::Tag(tag, values)))
                    }
                    _ => Err(defect(span, "invalid static unary operand")),
                }
            }
            Expr::Binary { op, left, right } => {
                let op = op.value.as_str();
                if matches!(
                    op,
                    "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | ">>=" | "<<="
                ) {
                    let place = self.eval_place(env, slots, *left, fuel)?;
                    let current = if op == "=" {
                        None
                    } else {
                        Some(place.slot(slots, false)?.clone())
                    };
                    let mut value = self.evaluate(env, slots, *right, fuel)?;
                    if let Some(current) = current {
                        let operator = op.strip_suffix('=').unwrap_or_default();
                        value = arithmetic(operator, current, value)
                            .map_err(|message| defect(span, message))?;
                    }
                    *place.slot(slots, op == "=")? = value;
                    return Ok(Value::Unit);
                }
                let a = self.evaluate(env, slots, *left, fuel)?;
                match (op, a) {
                    ("&&", Value::Bool(false)) => Ok(Value::Bool(false)),
                    ("||", Value::Bool(true)) => Ok(Value::Bool(true)),
                    ("??", Value::Tag(tag, mut values))
                        if matches!(tag.as_str(), "Some" | "Ok") =>
                    {
                        Ok(values.pop().unwrap_or(Value::Unit))
                    }
                    ("??", Value::Tag(tag, _)) if tag == "None" => {
                        self.evaluate(env, slots, *right, fuel)
                    }
                    ("??", Value::Tag(tag, values)) if tag == "Err" => {
                        self.eval_closure(env, slots, *right, values, span, fuel)
                    }
                    (operator, a) => {
                        let b = self.evaluate(env, slots, *right, fuel)?;
                        arithmetic(operator, a, b).map_err(|message| defect(span, message))
                    }
                }
            }
            Expr::Block { statements, .. } => {
                let mut result = Value::Unit;
                for &stmt in statements {
                    let node = ast.stmt(stmt);
                    result = match &node.value.kind {
                        StmtKind::Binding {
                            pattern,
                            storage,
                            value: Some(value),
                            fallback,
                            resource: false,
                            ..
                        } => {
                            let subject = self.pattern_subject(env, slots, *value, fuel)?;
                            if !self.bind_pattern_value(
                                env,
                                slots,
                                *pattern,
                                &subject,
                                storage.mode,
                            ) {
                                if let Some(fallback) = fallback {
                                    self.evaluate(env, slots, *fallback, fuel)?;
                                } else {
                                    return Err(defect(
                                        node.span,
                                        "static binding pattern did not match",
                                    ));
                                }
                            }
                            Value::Unit
                        }
                        StmtKind::Expr(expr) => self.evaluate(env, slots, *expr, fuel)?,
                        StmtKind::Type(_) | StmtKind::Import(_) => Value::Unit,
                        _ => return Err(nonstatic(node.span)),
                    };
                }
                Ok(result)
            }
            Expr::If { condition, yes, no } => {
                if self.eval_condition(env, slots, condition, fuel)? {
                    self.evaluate(env, slots, *yes, fuel)
                } else if let Some(no) = no {
                    self.evaluate(env, slots, *no, fuel)
                } else {
                    Ok(Value::Unit)
                }
            }
            Expr::While { condition, body } => {
                while self.eval_condition(env, slots, condition, fuel)? {
                    fuel.step(span)?;
                    match self.evaluate(env, slots, *body, fuel) {
                        Err(Signal::Break) => break,
                        Ok(_) | Err(Signal::Continue) => {}
                        Err(signal) => return Err(signal),
                    }
                }
                Ok(Value::Unit)
            }
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                if let Expr::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                } = ast.expr(*iterable).value
                {
                    let Value::Int(mut current) = self.evaluate(env, slots, start, fuel)? else {
                        return Err(defect(span, "range endpoint is not int"));
                    };
                    let Value::Int(end) = self.evaluate(env, slots, end, fuel)? else {
                        return Err(defect(span, "range endpoint is not int"));
                    };
                    while current < end || inclusive && current == end {
                        let value = Value::Int(current.clone());
                        if !self.eval_loop(env, slots, *pattern, &value, *body, fuel)? {
                            break;
                        }
                        current += 1;
                    }
                } else {
                    let values = match self.evaluate(env, slots, *iterable, fuel)? {
                        Value::Array(items) => items,
                        Value::Str(s) => s.chars().map(|ch| Value::Str(ch.to_string())).collect(),
                        Value::Bytes(bytes) => {
                            bytes.into_iter().map(|b| Value::Int(b.into())).collect()
                        }
                        Value::Map(entries) => entries
                            .into_iter()
                            .map(|(k, v)| Value::Tuple(vec![k, v]))
                            .collect(),
                        _ => return Err(defect(span, "value is not iterable")),
                    };
                    for value in values {
                        if !self.eval_loop(env, slots, *pattern, &value, *body, fuel)? {
                            break;
                        }
                    }
                }
                Ok(Value::Unit)
            }
            Expr::Match { value, arms, mode } => {
                let mut subject = self.pattern_subject(env, slots, *value, fuel)?;
                for arm in arms {
                    let mut local = env.clone();
                    if self.bind_pattern_value(&mut local, slots, arm.pattern, &subject, *mode) {
                        if let Some(guard) = arm.guard
                            && self.evaluate(&mut local, slots, guard, fuel)? != Value::Bool(true)
                        {
                            if let Some(place) = &subject.1 {
                                subject.0 = place.slot(slots, false)?.clone();
                            }
                            continue;
                        }
                        return self.evaluate(&mut local, slots, arm.body, fuel);
                    }
                }
                Err(defect(span, "non-exhaustive static match"))
            }
            Expr::Call { callee, args } => self.eval_call(env, slots, *callee, args, span, fuel),
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let input = Argument {
                    name: None,
                    mode: *mode,
                    value: *value,
                };
                let value = match &ast.expr(*target).value {
                    Expr::Call { callee, args } => {
                        let args: Vec<_> =
                            std::iter::once(input).chain(args.iter().cloned()).collect();
                        self.eval_call(env, slots, *callee, &args, span, fuel)?
                    }
                    _ => self.eval_call(env, slots, *target, &[input], span, fuel)?,
                };
                if *propagate && let Value::Tag(tag, mut values) = value {
                    if matches!(tag.as_str(), "Ok" | "Some") {
                        Ok(values.pop().unwrap_or(Value::Unit))
                    } else {
                        Err(Signal::Return(Value::Tag(tag, values)))
                    }
                } else {
                    Ok(value)
                }
            }
            Expr::Cast { value, .. } => self.evaluate(env, slots, *value, fuel),
            Expr::Member { base, member, .. } => {
                let base = self.evaluate(env, slots, *base, fuel)?;
                self.eval_member(env, slots, member, base, span, fuel)
            }
            Expr::Index { base, index, .. } => {
                let base = self.evaluate(env, slots, *base, fuel)?;
                self.eval_index(env, slots, base, *index, fuel)?
                    .ok_or_else(|| defect(span, "static index is out of bounds"))
            }
            Expr::Range { .. } => Err(nonstatic(span)),
            Expr::Tuple(items) => self.eval_list(env, slots, items, fuel).map(Value::Tuple),
            Expr::Array(items) => self.eval_list(env, slots, items, fuel).map(Value::Array),
            Expr::Map(entries) => {
                let mut map = Vec::new();
                for &(key, value) in entries {
                    let key = self.evaluate(env, slots, key, fuel)?;
                    let value = self.evaluate(env, slots, value, fuel)?;
                    if let Some((_, slot)) =
                        map.iter_mut().find(|(stored, _)| ieee_equal(stored, &key))
                    {
                        *slot = value;
                    } else {
                        map.push((key, value));
                    }
                }
                Ok(Value::Map(map))
            }
            Expr::Record { name, fields } => {
                let mut record = BTreeMap::new();
                for field in fields {
                    let value = if let Some(expr) = field.value {
                        self.evaluate(env, slots, expr, fuel)?
                    } else if let Some(id) = self.resolve(field.name.span) {
                        self.eval_def(env, slots, id, field.name.span, fuel)?
                    } else {
                        return Err(nonstatic(field.name.span));
                    };
                    record.insert(field.name.value.clone(), value);
                }
                if let Some(path) = name
                    && let Some(id) = self.resolve(path.span)
                {
                    let def = self.hir.definition(id);
                    if let Some(stmt) = def.stmt {
                        let def_file = def.name.span.file;
                        let def_scope = def.scope;
                        let defaults: Vec<(String, ExprId)> =
                            match &self.ast(def_file).stmt(stmt).value.kind {
                                StmtKind::Type(decl) => match decl.definition {
                                    syntax::TypeDefinition::Data(ty_id) => {
                                        if let syntax::Type::Record { fields, .. } =
                                            &self.ast(def_file).ty(ty_id).value
                                        {
                                            fields
                                                .iter()
                                                .filter_map(|f| {
                                                    f.default
                                                        .filter(|_| {
                                                            !record.contains_key(&f.name.value)
                                                        })
                                                        .map(|d| (f.name.value.clone(), d))
                                                })
                                                .collect()
                                        } else {
                                            Vec::new()
                                        }
                                    }
                                    _ => Vec::new(),
                                },
                                _ => Vec::new(),
                            };
                        if !defaults.is_empty() {
                            let mut def_env = Env::new(def_file, def_scope);
                            def_env.phase = env.phase;
                            let mut def_slots = Frame::default();
                            for (field_name, default_expr) in defaults {
                                let val = self.evaluate(
                                    &mut def_env,
                                    &mut def_slots,
                                    default_expr,
                                    fuel,
                                )?;
                                record.insert(field_name, val);
                            }
                        }
                    }
                }
                Ok(Value::Record(record))
            }
            Expr::Interpolated(parts) => {
                let mut text = String::new();
                for part in parts {
                    match part {
                        StringPart::Text(part) => {
                            let bytes = decode_text(part, false)
                                .map_err(|_| defect(span, "malformed text literal"))?;
                            text.push_str(
                                &String::from_utf8(bytes)
                                    .map_err(|_| defect(span, "malformed UTF-8 output"))?,
                            );
                        }
                        StringPart::Interpolation(id) => {
                            match self.evaluate(env, slots, *id, fuel)? {
                                Value::Str(part) => text.push_str(&part),
                                part => text.push_str(&render(&part)),
                            }
                        }
                    }
                }
                Ok(Value::Str(text))
            }
            Expr::Transfer { kind, value } => Err(match kind {
                Transfer::Break => Signal::Break,
                Transfer::Continue => Signal::Continue,
                Transfer::Return => Signal::Return(if let Some(value) = value {
                    self.evaluate(env, slots, *value, fuel)?
                } else {
                    Value::Unit
                }),
            }),
            Expr::Closure { .. } | Expr::Accessor(_) | Expr::Hole => Err(nonstatic(span)),
        }
    }

    fn eval_list(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        items: &[ExprId],
        fuel: &mut Budget,
    ) -> Eval<Vec<Value>> {
        items
            .iter()
            .map(|&id| self.evaluate(env, slots, id, fuel))
            .collect()
    }

    fn eval_loop(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        pattern: syntax::PatternId,
        value: &Value,
        body: ExprId,
        fuel: &mut Budget,
    ) -> Eval<bool> {
        fuel.step(self.ast(env.file).expr(body).span)?;
        let mut bindings = Values::new();
        if self.value_pattern(env, pattern, value, &mut bindings) {
            slots.locals.extend(bindings);
            match self.evaluate(env, slots, body, fuel) {
                Err(Signal::Break) => return Ok(false),
                Ok(_) | Err(Signal::Continue) => {}
                Err(signal) => return Err(signal),
            }
        }
        Ok(true)
    }

    fn eval_condition(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        condition: &Condition,
        fuel: &mut Budget,
    ) -> Eval<bool> {
        match condition {
            Condition::Expr(expr) => match self.evaluate(env, slots, *expr, fuel)? {
                Value::Bool(value) => Ok(value),
                _ => Err(defect(
                    self.ast(env.file).expr(*expr).span,
                    "expected bool in static condition",
                )),
            },
            Condition::Binding {
                pattern,
                value,
                mode,
            } => {
                let subject = self.pattern_subject(env, slots, *value, fuel)?;
                Ok(self.bind_pattern_value(env, slots, *pattern, &subject, *mode))
            }
        }
    }

    fn eval_path(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        path: &syntax::Path,
        fuel: &mut Budget,
    ) -> Eval {
        let id = self
            .resolve(path.span)
            .ok_or_else(|| nonstatic(path.span))?;
        self.eval_def(env, slots, id, path.span, fuel)
    }

    fn eval_def(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        id: DefinitionId,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        if let Some(place) = slots.draft_places.get(&id).cloned() {
            return place.slot(slots, false).cloned();
        }
        if let Some(value) = slots.locals.get(&id) {
            return Ok(value.clone());
        }
        if let Some(GenericValue::Data(value)) = env.generics.get(&id) {
            return Ok(value.clone());
        }
        if let Some(GenericValue::Mode(value)) = env.generics.get(&id) {
            return Ok(Value::Mode(*value));
        }
        if self.meta_parameters.contains(&id) {
            return Err(Signal::Dependent(span));
        }
        let def = self.hir.definition(id);
        match def.kind {
            DefinitionKind::Constant => {
                let stmt = def.stmt.ok_or_else(|| nonstatic(span))?;
                let mut local = Env::new(def.name.span.file, def.scope);
                local.phase = env.phase;
                let StmtKind::Binding {
                    value: Some(value), ..
                } = self.ast(local.file).stmt(stmt).value.kind
                else {
                    return Err(nonstatic(span));
                };
                let expr = self.ast(local.file).expr(value);
                if let Some(value) = self.static_values.get(&expr.span) {
                    return Ok(value.clone());
                }
                fuel.step(span)?;
                if fuel.depth >= 96 {
                    return Err(Signal::Error(
                        Code::E0811,
                        span,
                        "compile-time evaluation exceeded recursion capacity",
                    ));
                }
                fuel.depth += 1;
                let result = self.evaluate(&mut local, &mut Frame::default(), value, fuel);
                fuel.depth -= 1;
                result
            }
            DefinitionKind::Variant(parent)
                if self.hir.std_type(parent) == Some(ril_hir::StdType::FieldMode) =>
            {
                match def.name.value.as_str() {
                    "Let" => Ok(Value::Mode(MemberMode::PLAIN)),
                    "Var" => Ok(Value::Mode(MemberMode {
                        variable: true,
                        mode: Mode::Plain,
                    })),
                    "Mut" | "VarMut" => Ok(Value::Mode(MemberMode {
                        variable: def.name.value == "VarMut",
                        mode: Mode::Mut,
                    })),
                    "Ref" | "VarRef" => Ok(Value::Mode(MemberMode {
                        variable: def.name.value == "VarRef",
                        mode: Mode::Ref,
                    })),
                    "SharedMut" | "VarSharedMut" => Ok(Value::Mode(MemberMode {
                        variable: def.name.value == "VarSharedMut",
                        mode: Mode::Shared,
                    })),
                    _ => Err(nonstatic(span)),
                }
            }
            DefinitionKind::Variant(_) => Ok(Value::Tag(def.name.value.clone(), Vec::new())),
            DefinitionKind::Type if self.hir.unit_constructor(id) => {
                Ok(Value::Tag(def.name.value.clone(), Vec::new()))
            }
            _ => Err(nonstatic(span)),
        }
    }
}
