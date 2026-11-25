mod builtins;
mod call;
mod expr;

use std::collections::HashMap;

use num_traits::ToPrimitive;
use ril_hir::DefinitionId;
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Argument, Expr, ExprId, Member as Coordinate, Mode};

use super::{
    Ty, Value,
    check::{Checker, Env, Phase},
    pattern::MatchedValues,
    value::ieee_equal,
};

type Values = HashMap<DefinitionId, Value>;
type Eval<T = Value> = Result<T, Signal>;

pub(super) enum Signal {
    Dependent(Span),
    Error(Code, Span, &'static str),
    Return(Value),
    Break,
    Continue,
}

#[derive(Default)]
struct Frame {
    locals: Values,
    draft_places: HashMap<DefinitionId, Place>,
}

#[derive(Clone)]
struct Place {
    root: DefinitionId,
    path: Vec<Value>,
    span: Span,
}

impl Place {
    fn slot<'a>(&self, slots: &'a mut Frame, insert: bool) -> Eval<&'a mut Value> {
        let mut value = slots.locals.get_mut(&self.root).ok_or(Signal::Error(
            Code::E0813,
            self.span,
            "static assignment cannot update outer runtime storage",
        ))?;
        for (index, key) in self.path.iter().enumerate() {
            value = match (value, key) {
                (Value::Record(fields), Value::Str(name)) => fields.get_mut(name),
                (
                    Value::Array(items) | Value::Tuple(items) | Value::Tag(_, items),
                    Value::Int(key),
                ) => key.to_usize().and_then(|index| items.get_mut(index)),
                (Value::Map(entries), key) => {
                    let existing = entries
                        .iter()
                        .position(|(stored, _)| ieee_equal(stored, key));
                    if let Some(key) = existing {
                        entries.get_mut(key).map(|(_, value)| value)
                    } else if insert && index + 1 == self.path.len() {
                        entries.push((key.clone(), Value::Unit));
                        entries.last_mut().map(|(_, value)| value)
                    } else {
                        None
                    }
                }
                _ => None,
            }
            .ok_or_else(|| defect(self.span, "invalid static assignment target"))?;
        }
        Ok(value)
    }
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

fn none() -> Value {
    Value::Tag("None".into(), Vec::new())
}

fn optional_payload(value: Value, span: Span) -> Eval<Option<Value>> {
    match value {
        Value::Tag(tag, _) if tag == "None" => Ok(None),
        Value::Tag(tag, mut items) if tag == "Some" => items
            .pop()
            .map(Some)
            .ok_or_else(|| defect(span, "missing static optional payload")),
        _ => Err(defect(span, "expected a static option")),
    }
}

fn defect(span: Span, message: &'static str) -> Signal {
    Signal::Error(Code::E0831, span, message)
}

fn nonstatic(span: Span) -> Signal {
    Signal::Error(Code::E0814, span, "expression is not statically evaluable")
}

fn integer(value: usize) -> Value {
    Value::Int(value.into())
}

impl Checker<'_> {
    pub(super) fn eval_root(&mut self, env: &Env, expr: ExprId, required: bool) -> Option<Value> {
        if env.shadow {
            return None;
        }
        let span = self.ast(env.file).expr(expr).span;
        let result = self.evaluate_static(env, expr);
        self.finish_eval(span, result, required)
    }

    pub(super) fn evaluate_static(&mut self, env: &Env, expr: ExprId) -> Eval {
        self.evaluate_with_bindings(env, expr, &mut Values::new())
    }

    pub(super) fn evaluate_with_bindings(
        &mut self,
        env: &Env,
        expr: ExprId,
        bindings: &mut Values,
    ) -> Eval {
        let mut env = env.clone();
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let mut slots = Frame {
            locals: std::mem::take(bindings),
            ..Frame::default()
        };
        let result = self.evaluate(&mut env, &mut slots, expr, &mut fuel);
        *bindings = slots.locals;
        match result {
            Err(Signal::Return(value)) => Ok(value),
            result => result,
        }
    }

    pub(super) fn stage_static_call(
        &mut self,
        env: &Env,
        id: DefinitionId,
        args: &[Argument],
        span: Span,
    ) {
        let mut concrete = env.clone();
        concrete.require_concrete_types = true;
        match self.evaluate_static_call(&concrete, id, args, span) {
            Err(Signal::Dependent(_)) => {
                self.static_folds.insert(
                    span,
                    super::staging::StaticFold {
                        caller: env.clone(),
                        target: id,
                        args: args.to_vec(),
                    },
                );
            }
            result => {
                self.finish_eval(span, result, true);
            }
        }
    }

    pub(super) fn evaluate_static_call(
        &mut self,
        env: &Env,
        id: DefinitionId,
        args: &[Argument],
        span: Span,
    ) -> Eval {
        let mut root = env.clone();
        let mut slots = Frame::default();
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let args = self.eval_args(&mut root, &mut slots, args, &mut fuel)?;
        self.eval_function(&root, id, args, span, &mut fuel)
    }

    pub(super) fn stage_static_argument(
        &mut self,
        env: &Env,
        expression: ExprId,
        supplied: bool,
    ) -> Option<super::staging::StaticInput> {
        use super::staging::StaticInput;
        let mut concrete = env.clone();
        concrete.require_concrete_types = true;
        match self.evaluate_static(&concrete, expression) {
            Err(Signal::Dependent(_)) if supplied => Some(StaticInput::Supplied(expression)),
            Err(Signal::Dependent(_)) => Some(StaticInput::Default(expression)),
            result => self
                .finish_eval(self.ast(env.file).expr(expression).span, result, true)
                .map(StaticInput::Ready),
        }
    }

    pub(super) fn eval_introspection_root(
        &mut self,
        env: &Env,
        name: &str,
        args: &[Argument],
        span: Span,
    ) {
        let mut local = env.clone();
        local.phase = Phase::MetaValue;
        local.require_concrete_types = true;
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let result = self
            .eval_args(&mut local, &mut Frame::default(), args, &mut fuel)
            .and_then(|values| {
                let values = values.into_iter().map(|(_, value)| value).collect();
                self.eval_primitive(&local, name, values, span)
            });
        match result {
            Ok(value) => {
                self.static_values.insert(span, value);
            }
            Err(Signal::Dependent(_)) => {}
            other => {
                self.finish_eval(span, other, true);
            }
        }
    }

    pub(super) fn eval_metadata_root(
        &mut self,
        env: &Env,
        path: &syntax::Path,
        args: &[Argument],
        span: Span,
    ) {
        let mut env = env.clone();
        env.phase = Phase::MetaValue;
        let mut fuel = Budget {
            remaining: self.budget,
            depth: 0,
        };
        let result = self
            .eval_args(&mut env, &mut Frame::default(), args, &mut fuel)
            .and_then(|values| {
                let values = values
                    .into_iter()
                    .map(|(_, value)| value)
                    .collect::<Vec<_>>();
                self.eval_metadata(&mut env, path, &values, span)
            });
        self.finish_eval(span, result, true);
    }

    fn finish_eval(&mut self, span: Span, result: Eval, required: bool) -> Option<Value> {
        match result {
            Ok(value) | Err(Signal::Return(value)) => {
                self.static_values.insert(span, value.clone());
                Some(value)
            }
            Err(Signal::Dependent(span)) => {
                if required {
                    self.error(Code::E0814, span, "static argument is not known here");
                }
                None
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
        slots: &mut Frame,
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

    fn pattern_subject(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        expression: ExprId,
        fuel: &mut Budget,
    ) -> Eval<(Value, Option<Place>)> {
        if !self.is_draft_path(env, slots, expression) {
            return self
                .evaluate(env, slots, expression, fuel)
                .map(|value| (value, None));
        }
        let place = self.eval_place(env, slots, expression, fuel)?;
        let value = place.slot(slots, false)?.clone();
        Ok((value, Some(place)))
    }

    fn is_draft_path(&self, env: &Env, slots: &Frame, expression: ExprId) -> bool {
        let mut node = self.ast(env.file).expr(expression);
        loop {
            node = match &node.value {
                Expr::Path(path) => {
                    return self
                        .resolve(path.span)
                        .is_some_and(|id| slots.draft_places.contains_key(&id));
                }
                Expr::Member {
                    base, safe: false, ..
                } => self
                    .ast(env.file)
                    .expr(self.tuple_inner_receiver(env, *base).unwrap_or(*base)),
                Expr::Index {
                    base,
                    index,
                    safe: false,
                } => {
                    let ast = self.ast(env.file);
                    if matches!(ast.expr(*index).value, Expr::Range { .. })
                        || matches!(
                            self.types.get(&ast.expr(*base).span),
                            Some(Ty::Str | Ty::Bytes)
                        )
                    {
                        return false;
                    }
                    ast.expr(*base)
                }
                Expr::Unary { op, value } if op.value == "ref" => self.ast(env.file).expr(*value),
                expression => {
                    let Some((base, _)) = self.hir.inner_operand(env.file, expression) else {
                        return false;
                    };
                    if matches!(self.types.get(&node.span), Some(Ty::Tuple(_) | Ty::Unit)) {
                        return false;
                    }
                    self.ast(env.file).expr(base)
                }
            };
        }
    }

    fn tuple_inner_receiver(&self, env: &Env, base: ExprId) -> Option<ExprId> {
        let node = self.ast(env.file).expr(base);
        if !matches!(self.types.get(&node.span), Some(Ty::Tuple(_))) {
            return None;
        }
        let (argument, mode) = self.hir.inner_operand(env.file, &node.value)?;
        (mode == Mode::Mut).then_some(argument)
    }

    fn bind_pattern_value(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        pattern: syntax::PatternId,
        (value, place): &(Value, Option<Place>),
        mode: Mode,
    ) -> bool {
        let mut matched = MatchedValues::default();
        if !self.value_pattern_at(
            env,
            pattern,
            value,
            &mut matched,
            place.as_ref().map(|_| &[][..]),
        ) {
            return false;
        }
        for (id, value) in matched.locals {
            let alias = matched.paths.remove(&id).and_then(|(path, explicit)| {
                let mode = if explicit == Mode::Plain {
                    mode
                } else {
                    explicit
                };
                if matches!(mode, Mode::Mut | Mode::Ref | Mode::Via) {
                    place.as_ref().map(|base| {
                        let mut alias = base.clone();
                        alias.path.extend(path);
                        alias
                    })
                } else {
                    None
                }
            });
            if let Some(alias) = alias {
                slots.draft_places.insert(id, alias);
            } else {
                slots.draft_places.remove(&id);
            }
            slots.locals.insert(id, value);
        }
        true
    }

    fn eval_member(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
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
        slots: &mut Frame,
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

    fn eval_place(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        lhs: ExprId,
        fuel: &mut Budget,
    ) -> Eval<Place> {
        let node = self.ast(env.file).expr(lhs);
        let mut place = match &node.value {
            Expr::Path(path) => {
                let root = self
                    .resolve(path.span)
                    .ok_or_else(|| nonstatic(node.span))?;
                let mut place = slots.draft_places.get(&root).cloned().unwrap_or(Place {
                    root,
                    path: Vec::new(),
                    span: node.span,
                });
                place.span = node.span;
                Ok(place)
            }
            Expr::Unary { op, value } if op.value == "ref" => {
                self.eval_place(env, slots, *value, fuel)
            }
            Expr::Member {
                base,
                member,
                safe: false,
            } => {
                let base = self.tuple_inner_receiver(env, *base).unwrap_or(*base);
                let mut place = self.eval_place(env, slots, base, fuel)?;
                let key = match member {
                    Coordinate::Name(name) => Value::Str(name.value.clone()),
                    Coordinate::Index(index) => Value::Int(
                        index
                            .value
                            .parse()
                            .map_err(|_| defect(index.span, "invalid tuple index"))?,
                    ),
                    Coordinate::Computed(key) => self.evaluate(env, slots, *key, fuel)?,
                };
                place.path.push(key);
                place.span = node.span;
                Ok(place)
            }
            Expr::Index {
                base,
                index,
                safe: false,
            } => {
                let mut place = self.eval_place(env, slots, *base, fuel)?;
                place.path.push(self.evaluate(env, slots, *index, fuel)?);
                place.span = node.span;
                Ok(place)
            }
            expression => {
                let (argument, _) = self
                    .hir
                    .inner_operand(env.file, expression)
                    .ok_or_else(|| defect(node.span, "invalid static assignment target"))?;
                let mut place = self.eval_place(env, slots, argument, fuel)?;
                if !matches!(place.slot(slots, false)?, Value::Tag(_, items) if items.len() == 1) {
                    return Err(defect(
                        node.span,
                        "static inner place requires a single nominal payload",
                    ));
                }
                place.path.push(Value::Int(0.into()));
                place.span = node.span;
                Ok(place)
            }
        }?;
        let narrowed = self.narrowings.get(&node.span).copied().unwrap_or_default();
        place
            .path
            .extend(std::iter::repeat_with(|| Value::Int(0.into())).take(narrowed));
        Ok(place)
    }
}
