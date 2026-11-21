use std::collections::{BTreeMap, HashMap};

use num_bigint::BigInt;
use num_traits::{FromPrimitive, Signed, ToPrimitive, Zero};
use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind, PrimitivePhase},
    syntax::{
        self, Argument, Condition, Expr, ExprId, Member as Coordinate, Mode, StmtKind, StringPart,
        Transfer,
    },
};

use super::{
    AdtKind, GenericValue, MemberMode, Ty, Value, arithmetic,
    check::{Checker, Env, Phase},
    literal, render,
    value::{decode_text, ieee_equal},
};

type Values = HashMap<DefinitionId, Value>;
type Eval<T = Value> = Result<T, Signal>;

enum Signal {
    Error(Code, Span, &'static str),
    Return(Value),
    Break,
    Continue,
}

struct Budget {
    remaining: u64,
    depth: usize,
}

impl Budget {
    fn step(&mut self, span: Span) -> Eval<()> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Signal::Error(
            Code::E0811,
            span,
            "compile-time step budget exhausted",
        ))?;
        Ok(())
    }
}

fn defect(span: Span, message: &'static str) -> Signal {
    Signal::Error(Code::E0831, span, message)
}

fn nonstatic(span: Span) -> Signal {
    Signal::Error(Code::E0814, span, "expression is not statically evaluable")
}

impl Checker<'_> {
    pub(super) fn eval_root(&mut self, env: &Env, expr: ExprId, required: bool) -> Option<Value> {
        if env.shadow {
            return None;
        }
        let span = self.ast(env.file).expr(expr).span;
        let mut env = env.clone();
        let mut slots = Values::new();
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let result = self.evaluate(&mut env, &mut slots, expr, &mut fuel);
        self.finish_eval(span, result, required)
    }

    pub(super) fn eval_call_root(
        &mut self,
        env: &Env,
        id: DefinitionId,
        args: &[Argument],
        span: Span,
    ) -> Option<Value> {
        let mut root = env.clone();
        let mut slots = Values::new();
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let output = self
            .eval_args(&mut root, &mut slots, args, &mut fuel)
            .and_then(|args| self.eval_function(&root, id, args, span, &mut fuel));
        self.finish_eval(span, output, true)
    }

    fn finish_eval(&mut self, span: Span, result: Eval, required: bool) -> Option<Value> {
        match result {
            Ok(value) | Err(Signal::Return(value)) => {
                self.static_values.insert(span, value.clone());
                Some(value)
            }
            Err(Signal::Error(code, span, message)) => {
                if required {
                    self.error(code, span, message);
                }
                None
            }
            Err(_) => {
                if required {
                    self.error(
                        Code::E0814,
                        span,
                        "control transfer has no static evaluation target",
                    );
                }
                None
            }
        }
    }

    fn evaluate(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        expr: ExprId,
        fuel: &mut Budget,
    ) -> Eval {
        let mut value = self.eval_expr(env, slots, expr, fuel)?;
        let span = self.ast(env.file).expr(expr).span;
        for _ in 0..self.narrowings.get(&span).copied().unwrap_or_default() {
            if let Value::Tag(tag, mut children) = value
                && tag == "Some"
                && let Some(child) = children.pop()
            {
                value = child;
            } else {
                return Err(defect(span, "invalid narrowed static value"));
            }
        }
        Ok(value)
    }

    fn eval_expr(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        expr: ExprId,
        fuel: &mut Budget,
    ) -> Eval {
        let ast = self.ast(env.file);
        let node = ast.expr(expr);
        let span = node.span;
        match &node.value {
            Expr::Literal(value) => {
                literal(value).map_err(|_| defect(span, "invalid static literal"))
            }
            Expr::Unit => Ok(Value::Unit),
            Expr::Path(path) => self.eval_path(env, slots, path, fuel),
            Expr::Quote(ty) => Ok(Value::Type(Box::new(self.type_expr(env, *ty)))),
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
                if op == "=" {
                    let value = self.evaluate(env, slots, *right, fuel)?;
                    self.assign(env, slots, *left, value, fuel)?;
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
                        if matches!(
                            operator,
                            "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | ">>=" | "<<="
                        ) {
                            let op = operator.strip_suffix('=').unwrap_or_default();
                            let value =
                                arithmetic(op, a, b).map_err(|message| defect(span, message))?;
                            self.assign(env, slots, *left, value, fuel)?;
                            Ok(Value::Unit)
                        } else {
                            arithmetic(operator, a, b).map_err(|message| defect(span, message))
                        }
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
                            value: Some(value),
                            fallback,
                            resource: false,
                            ..
                        } => {
                            let value = self.evaluate(env, slots, *value, fuel)?;
                            let mut bindings = Values::new();
                            if self.value_pattern(env, *pattern, &value, &mut bindings) {
                                slots.extend(bindings);
                            } else if let Some(fallback) = fallback {
                                self.evaluate(env, slots, *fallback, fuel)?;
                            } else {
                                return Err(defect(
                                    node.span,
                                    "static binding pattern did not match",
                                ));
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
            Expr::Match { value, arms, .. } => {
                let value = self.evaluate(env, slots, *value, fuel)?;
                for arm in arms {
                    let mut local = env.clone();
                    let mut bindings = Values::new();
                    if self.value_pattern(&mut local, arm.pattern, &value, &mut bindings) {
                        slots.extend(bindings);
                        if let Some(guard) = arm.guard
                            && self.evaluate(&mut local, slots, guard, fuel)? != Value::Bool(true)
                        {
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
            Expr::Member { base, member, safe } => {
                let base = self.evaluate(env, slots, *base, fuel)?;
                if *safe && let Value::Tag(tag, mut items) = base {
                    if tag == "None" {
                        return Ok(Value::Tag(tag, items));
                    }
                    let base = items
                        .pop()
                        .ok_or_else(|| defect(span, "invalid optional payload"))?;
                    let item = self.eval_member(env, slots, member, base, span, fuel)?;
                    Ok(Value::Tag("Some".into(), vec![item]))
                } else {
                    self.eval_member(env, slots, member, base, span, fuel)
                }
            }
            Expr::Index { base, index, safe } => {
                let base = self.evaluate(env, slots, *base, fuel)?;
                let value = self.eval_index(env, slots, base, *index, fuel)?;
                if *safe {
                    Ok(value.map_or_else(
                        || Value::Tag("None".into(), Vec::new()),
                        |item| Value::Tag("Some".into(), vec![item]),
                    ))
                } else {
                    value.ok_or_else(|| defect(span, "static index is out of bounds"))
                }
            }
            Expr::Range { .. } => Err(nonstatic(span)),
            Expr::Tuple(items) => self.eval_list(env, slots, items, fuel).map(Value::Tuple),
            Expr::Array(items) => self.eval_list(env, slots, items, fuel).map(Value::Array),
            Expr::Map(entries) => {
                let entries = entries
                    .iter()
                    .map(|&(key, value)| {
                        let key = self.evaluate(env, slots, key, fuel)?;
                        Ok((key, self.evaluate(env, slots, value, fuel)?))
                    })
                    .collect::<Eval<Vec<_>>>()?;
                Ok(Value::Map(entries))
            }
            Expr::Record { fields, .. } => {
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
        slots: &mut Values,
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
        slots: &mut Values,
        pattern: syntax::PatternId,
        value: &Value,
        body: ExprId,
        fuel: &mut Budget,
    ) -> Eval<bool> {
        fuel.step(self.ast(env.file).expr(body).span)?;
        let mut bindings = Values::new();
        if self.value_pattern(env, pattern, value, &mut bindings) {
            slots.extend(bindings);
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
        slots: &mut Values,
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
            Condition::Binding { pattern, value, .. } => {
                let value = self.evaluate(env, slots, *value, fuel)?;
                let mut bindings = Values::new();
                let matched = self.value_pattern(env, *pattern, &value, &mut bindings);
                if matched {
                    slots.extend(bindings);
                }
                Ok(matched)
            }
        }
    }

    fn eval_path(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
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
        slots: &mut Values,
        id: DefinitionId,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        if let Some(value) = slots.get(&id) {
            return Ok(value.clone());
        }
        if let Some(GenericValue::Data(value)) = env.generics.get(&id) {
            return Ok(value.clone());
        }
        if let Some(GenericValue::Mode(value)) = env.generics.get(&id) {
            return Ok(Value::Mode(*value));
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
                let result = self.evaluate(&mut local, &mut Values::new(), value, fuel);
                fuel.depth -= 1;
                result
            }
            DefinitionKind::Variant(_) => Ok(Value::Tag(def.name.value.clone(), Vec::new())),
            DefinitionKind::Primitive(_) => match def.name.value.as_str() {
                "None" => Ok(Value::Tag("None".into(), Vec::new())),
                "OS" => Ok(Value::Str(std::env::consts::OS.into())),
                "ARCH" => Ok(Value::Str(std::env::consts::ARCH.into())),
                "HAS_OPENAT" => Ok(Value::Bool(cfg!(unix))),
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
            },
            _ => Err(nonstatic(span)),
        }
    }

    fn eval_args(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        args: &[Argument],
        fuel: &mut Budget,
    ) -> Eval<Vec<(Option<String>, Value)>> {
        args.iter()
            .map(|arg| {
                Ok((
                    arg.name.as_ref().map(|name| name.value.clone()),
                    self.evaluate(env, slots, arg.value, fuel)?,
                ))
            })
            .collect()
    }

    fn eval_call(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        callee: ExprId,
        args: &[Argument],
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        let node = self.ast(env.file).expr(callee);
        if let Expr::Path(path) = &node.value {
            let id = self.resolve(path.span).ok_or_else(|| nonstatic(span))?;
            let def = self.hir.definition(id);
            let name = def.name.value.as_str();
            match def.kind {
                DefinitionKind::Primitive(PrimitivePhase::Runtime) => Err(Signal::Error(
                    Code::E0810,
                    span,
                    "runtime primitive in static evaluation",
                )),
                DefinitionKind::Primitive(_) if matches!(name, "filter" | "map") => {
                    let [array, callback] = args else {
                        return Err(nonstatic(span));
                    };
                    let Value::Array(items) = self.evaluate(env, slots, array.value, fuel)? else {
                        return Err(nonstatic(span));
                    };
                    let mut result = Vec::new();
                    for item in items {
                        let answer = self.eval_closure(
                            env,
                            slots,
                            callback.value,
                            vec![item.clone()],
                            span,
                            fuel,
                        )?;
                        if name == "map" {
                            result.push(answer);
                        } else if answer == Value::Bool(true) {
                            result.push(item);
                        }
                    }
                    Ok(Value::Array(result))
                }
                DefinitionKind::Primitive(_) => {
                    fuel.step(span)?;
                    let args = self
                        .eval_args(env, slots, args, fuel)?
                        .into_iter()
                        .map(|(_, value)| value)
                        .collect();
                    self.eval_primitive(env, name, args, span)
                }
                DefinitionKind::Variant(_) | DefinitionKind::Type => {
                    let values = self
                        .eval_args(env, slots, args, fuel)?
                        .into_iter()
                        .map(|(_, value)| value)
                        .collect();
                    Ok(Value::Tag(name.into(), values))
                }
                DefinitionKind::Function => {
                    let args = self.eval_args(env, slots, args, fuel)?;
                    self.eval_function(env, id, args, span, fuel)
                }
                _ => Err(nonstatic(span)),
            }
        } else {
            let values = self
                .eval_args(env, slots, args, fuel)?
                .into_iter()
                .map(|(_, value)| value)
                .collect();
            self.eval_closure(env, slots, callee, values, span, fuel)
        }
    }

    fn eval_function(
        &mut self,
        env: &Env,
        id: DefinitionId,
        args: Vec<(Option<String>, Value)>,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        let def = self.hir.definition(id);
        let mut local = Env::new(def.name.span.file, def.scope);
        local.phase = if env.phase == Phase::TypeEval {
            Phase::TypeEval
        } else {
            Phase::MetaValue
        };
        let ast = self.ast(local.file);
        let stmt = def.stmt.ok_or_else(|| nonstatic(span))?;
        let StmtKind::Function(fun) = &ast.stmt(stmt).value.kind else {
            return Err(nonstatic(span));
        };
        if !fun.is_meta {
            return Err(Signal::Error(
                Code::E0810,
                span,
                "ordinary fn in static evaluation",
            ));
        }
        let body = fun.body.ok_or_else(|| nonstatic(span))?;
        fuel.step(span)?;
        if fuel.depth >= 96 {
            return Err(Signal::Error(
                Code::E0811,
                span,
                "compile-time evaluation exceeded recursion capacity",
            ));
        }
        let mut bound = vec![None; fun.signature.params.len()];
        for (label, value) in args {
            let index = if let Some(label) = label {
                fun.signature
                    .params
                    .iter()
                    .position(|p| p.name.as_ref().is_some_and(|name| name.value == label))
            } else {
                bound.iter().position(Option::is_none)
            };
            let Some(slot) = index.and_then(|i| bound.get_mut(i)) else {
                return Err(nonstatic(span));
            };
            *slot = Some(value);
        }
        fuel.depth += 1;
        let result = (|| {
            let mut slots = Values::new();
            for (param, input) in fun.signature.params.iter().zip(bound) {
                let input = if let Some(input) = input {
                    input
                } else if let Some(default) = param.default {
                    self.evaluate(&mut local, &mut slots, default, fuel)?
                } else {
                    return Err(nonstatic(span));
                };
                if let Some(id) = param.name.as_ref().and_then(|name| self.resolve(name.span)) {
                    slots.insert(id, input);
                }
            }
            match self.evaluate(&mut local, &mut slots, body, fuel) {
                Err(Signal::Return(value)) => Ok(value),
                rest => rest,
            }
        })();
        fuel.depth -= 1;
        result
    }

    fn eval_closure(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        id: ExprId,
        input: Vec<Value>,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        fuel.step(span)?;
        let ast = self.ast(env.file);
        match &ast.expr(id).value {
            Expr::Closure { params, body, .. } if params.len() == input.len() => {
                let mut bindings = Values::new();
                for (param, value) in params.iter().zip(input) {
                    if let Some(pattern) = param.pattern {
                        if !self.value_pattern(env, pattern, &value, &mut bindings) {
                            return Err(defect(span, "closure parameter pattern did not match"));
                        }
                    } else if let Some(id) =
                        param.name.as_ref().and_then(|name| self.resolve(name.span))
                    {
                        bindings.insert(id, value);
                    }
                }
                slots.extend(bindings);
                match self.evaluate(env, slots, *body, fuel) {
                    Err(Signal::Return(value)) => Ok(value),
                    rest => rest,
                }
            }
            Expr::Accessor(segments) => {
                let mut input = input.into_iter();
                let mut value = input.next().ok_or_else(|| nonstatic(span))?;
                for (_, member) in segments {
                    value = self.eval_member(env, slots, member, value, span, fuel)?;
                }
                Ok(value)
            }
            Expr::Path(path)
                if self
                    .resolve(path.span)
                    .is_some_and(|id| self.is_meta_fn(id)) =>
            {
                let id = self
                    .resolve(path.span)
                    .unwrap_or_else(|| ril_base::ice!("resolved static callable disappeared"));
                self.eval_function(
                    env,
                    id,
                    input.into_iter().map(|value| (None, value)).collect(),
                    span,
                    fuel,
                )
            }
            _ => Err(nonstatic(span)),
        }
    }

    fn eval_primitive(&mut self, env: &Env, name: &str, mut args: Vec<Value>, span: Span) -> Eval {
        match (name, args.as_slice()) {
            ("assert", [Value::Bool(true), ..]) => Ok(Value::Unit),
            ("assert", [Value::Bool(false), ..]) => {
                Err(Signal::Error(Code::E0830, span, "static assertion failed"))
            }
            ("panic", _) => Err(defect(span, "static evaluation panicked")),
            ("Some" | "Ok" | "Err", [_]) => Ok(Value::Tag(name.into(), args)),
            ("len", [Value::Array(items)]) => Ok(integer(items.len())),
            ("len", [Value::Map(items)]) => Ok(integer(items.len())),
            ("len", [Value::Str(str)]) => Ok(integer(str.chars().count())),
            ("len", [Value::Bytes(bytes)]) => Ok(integer(bytes.len())),
            ("clone", [_]) => Ok(args.pop().unwrap_or(Value::Unit)),
            ("inner", [Value::Tag(_, values)]) if values.len() == 1 => {
                values.first().cloned().ok_or_else(|| nonstatic(span))
            }
            ("inner", [Value::Tag(_, values)]) => Ok(Value::Tuple(values.clone())),
            ("inspect", [value]) => Ok(Value::Str(render(value))),
            ("contains", [Value::Array(values), item]) => {
                Ok(Value::Bool(values.iter().any(|v| ieee_equal(v, item))))
            }
            ("contains", [Value::Map(values), item]) => {
                Ok(Value::Bool(values.iter().any(|(k, _)| ieee_equal(k, item))))
            }
            ("type_name", [Value::Type(ty)]) => Ok(Value::Str(ty.display(self.hir).to_string())),
            ("coords", [Value::Type(ty)]) => self.eval_coords(env, ty, span),
            ("variants", [Value::Type(ty)]) => {
                if let Ty::Adt(adt) = ty.as_ref() {
                    if adt.kind == AdtKind::Foreign {
                        return Err(Signal::Error(
                            Code::E0907,
                            span,
                            "foreign representation is sealed",
                        ));
                    }
                    if adt.kind == AdtKind::OpaqueSum && adt.defining_scope != env.scope {
                        return Err(Signal::Error(
                            Code::E0308,
                            span,
                            "opaque representation is sealed",
                        ));
                    }
                    Ok(Value::Array(
                        self.sum_variants(adt, &mut Default::default())
                            .into_keys()
                            .map(Value::Str)
                            .collect(),
                    ))
                } else {
                    Err(Signal::Error(
                        Code::E0301,
                        span,
                        "variants requires a sum type",
                    ))
                }
            }
            ("has_default", [Value::Type(ty), Value::Str(field)]) => Ok(Value::Bool(
                self.record_defaults(&Some((**ty).clone())).contains(field),
            )),
            ("to_f64", [Value::Int(value)]) => Ok(Value::F64(
                value
                    .to_f64()
                    .unwrap_or_else(|| {
                        if value.is_negative() {
                            f64::NEG_INFINITY
                        } else {
                            f64::INFINITY
                        }
                    })
                    .to_bits(),
            )),
            ("convert" | "to_int" | "trunc", [Value::F64(value)]) => {
                let value = f64::from_bits(*value);
                let integer = if name == "trunc" || value.fract() == 0.0 {
                    BigInt::from_f64(value.trunc())
                } else {
                    None
                };
                Ok(integer.map_or_else(
                    || Value::Tag("None".into(), Vec::new()),
                    |value| Value::Tag("Some".into(), vec![Value::Int(value)]),
                ))
            }
            ("checked_div" | "checked_rem", [Value::Int(a), Value::Int(b)]) => {
                if b.is_zero() {
                    Ok(Value::Tag("None".into(), Vec::new()))
                } else {
                    Ok(Value::Tag(
                        "Some".into(),
                        vec![Value::Int(if name == "checked_div" {
                            a / b
                        } else {
                            a % b
                        })],
                    ))
                }
            }
            _ => Err(nonstatic(span)),
        }
    }

    fn eval_coords(&mut self, env: &Env, ty: &Ty, span: Span) -> Eval {
        let rep;
        let ty = if let Ty::Adt(adt) = ty {
            if adt.kind == AdtKind::Foreign {
                return Err(Signal::Error(
                    Code::E0907,
                    span,
                    "foreign representation is sealed",
                ));
            }
            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                && adt.defining_scope != env.scope
            {
                return Err(Signal::Error(
                    Code::E0308,
                    span,
                    "opaque representation is sealed",
                ));
            }
            rep = self.representation(env, adt);
            rep.as_ref().unwrap_or(ty)
        } else {
            ty
        };
        let entries = match ty {
            Ty::Record(fields, _) => fields
                .iter()
                .map(|(key, member)| {
                    Value::Tuple(vec![Value::Mode(member.mode), Value::Str(key.clone())])
                })
                .collect(),
            Ty::Tuple(items) => items
                .iter()
                .enumerate()
                .map(|(position, member)| {
                    Value::Tuple(vec![Value::Mode(member.mode), integer(position)])
                })
                .collect(),
            _ => {
                return Err(Signal::Error(
                    Code::E0358,
                    span,
                    "coords requires a record or tuple",
                ));
            }
        };
        Ok(Value::Array(entries))
    }

    fn eval_member(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        member: &Coordinate,
        base: Value,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        let coordinate = match member {
            Coordinate::Name(name) => Value::Str(name.value.clone()),
            Coordinate::Index(name) => Value::Int(
                name.value
                    .parse()
                    .map_err(|_| defect(span, "invalid tuple index"))?,
            ),
            Coordinate::Computed(expr) => self.evaluate(env, slots, *expr, fuel)?,
        };
        match (base, coordinate) {
            (Value::Record(mut fields), Value::Str(key)) => fields
                .remove(&key)
                .ok_or_else(|| defect(span, "unknown static field")),
            (Value::Tuple(items), Value::Int(index)) => index
                .to_usize()
                .and_then(|i| items.into_iter().nth(i))
                .ok_or_else(|| defect(span, "tuple index out of bounds")),
            _ => Err(defect(span, "invalid static member access")),
        }
    }

    fn eval_index(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        base: Value,
        index: ExprId,
        fuel: &mut Budget,
    ) -> Eval<Option<Value>> {
        let ast = self.ast(env.file);
        let node = ast.expr(index);
        if let Expr::Range {
            start,
            end,
            inclusive,
        } = node.value
        {
            let length = match &base {
                Value::Array(items) => items.len(),
                Value::Bytes(bytes) => bytes.len(),
                Value::Str(s) => s.chars().count(),
                _ => return Err(defect(node.span, "cannot slice value")),
            };
            let mut bound = |maybe: Option<ExprId>, default| -> Eval<Option<usize>> {
                if let Some(id) = maybe {
                    match self.evaluate(env, slots, id, fuel)? {
                        Value::Int(value) => Ok(value.to_usize()),
                        _ => Err(defect(node.span, "expected integer slice bound")),
                    }
                } else {
                    Ok(Some(default))
                }
            };
            let (Some(start), Some(mut end)) = (bound(start, 0)?, bound(end, length)?) else {
                return Ok(None);
            };
            if inclusive && let Some(exclusive) = end.checked_add(1) {
                end = exclusive;
            }
            return Ok(match base {
                Value::Array(items) => items
                    .get(start..end)
                    .map(|slice| Value::Array(slice.to_vec())),
                Value::Bytes(bytes) => bytes
                    .get(start..end)
                    .map(|slice| Value::Bytes(slice.to_vec())),
                Value::Str(text) if start <= end && end <= length => Some(Value::Str(
                    text.chars().skip(start).take(end - start).collect(),
                )),
                _ => None,
            });
        }
        let index = self.evaluate(env, slots, index, fuel)?;
        Ok(match (base, index) {
            (Value::Array(items), Value::Int(index)) => {
                index.to_usize().and_then(|i| items.into_iter().nth(i))
            }
            (Value::Str(text), Value::Int(index)) => index
                .to_usize()
                .and_then(|i| text.chars().nth(i))
                .map(|c| Value::Str(c.to_string())),
            (Value::Bytes(bytes), Value::Int(index)) => index
                .to_usize()
                .and_then(|i| bytes.get(i).copied())
                .map(|v| Value::Int(v.into())),
            (Value::Map(items), key) => items
                .into_iter()
                .find(|(k, _)| ieee_equal(k, &key))
                .map(|(_, v)| v),
            _ => return Err(defect(node.span, "invalid static index")),
        })
    }

    fn assign(
        &mut self,
        env: &mut Env,
        slots: &mut Values,
        lhs: ExprId,
        value: Value,
        fuel: &mut Budget,
    ) -> Eval<()> {
        let node = self.ast(env.file).expr(lhs);
        match &node.value {
            Expr::Path(path) => {
                let id = self
                    .resolve(path.span)
                    .ok_or_else(|| nonstatic(node.span))?;
                if !slots.contains_key(&id) {
                    return Err(Signal::Error(
                        Code::E0813,
                        node.span,
                        "static assignment cannot update outer runtime storage",
                    ));
                }
                slots.insert(id, value);
                Ok(())
            }
            Expr::Member {
                base,
                member,
                safe: false,
            } => {
                let mut old = self.evaluate(env, slots, *base, fuel)?;
                match (member, &mut old) {
                    (Coordinate::Name(name), Value::Record(fields))
                        if fields.contains_key(&name.value) =>
                    {
                        fields.insert(name.value.clone(), value);
                    }
                    (Coordinate::Index(index), Value::Tuple(values)) => {
                        let slot = index
                            .value
                            .parse::<usize>()
                            .ok()
                            .and_then(|index| values.get_mut(index))
                            .ok_or_else(|| defect(node.span, "invalid tuple assignment"))?;
                        *slot = value;
                    }
                    _ => return Err(defect(node.span, "invalid static assignment")),
                }
                self.assign(env, slots, *base, old, fuel)
            }
            _ => Err(defect(node.span, "invalid static assignment target")),
        }
    }
}

fn integer(value: usize) -> Value {
    Value::Int(value.into())
}
