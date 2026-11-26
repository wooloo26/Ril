use ril_hir::{DefinitionId, DefinitionKind, PrimitivePhase};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Argument, Expr, ExprId, StmtKind};

use super::{
    Budget, Eval, Frame, Place, Signal, Values, builtins::eval_text, defect, none, nonstatic,
};
use crate::ty::{
    GenericValue, Ty, Value,
    check::{Checker, Env, Phase},
    value::ieee_equal,
};

impl Checker<'_> {
    fn order_primitive_args(
        &self,
        id: DefinitionId,
        args: Vec<(Option<String>, Value)>,
        span: Span,
    ) -> Eval<Vec<Value>> {
        if !args.iter().any(|(label, _)| label.is_some()) {
            return Ok(args.into_iter().map(|(_, value)| value).collect());
        }
        let def = self.hir.definition(id);
        let Some(stmt) = def.stmt else {
            return Ok(args.into_iter().map(|(_, value)| value).collect());
        };
        let StmtKind::Function(fun) = &self.ast(def.name.span.file).stmt(stmt).value.kind else {
            return Ok(args.into_iter().map(|(_, value)| value).collect());
        };
        let params = &fun.signature.params;
        let mut bound = vec![None; params.len()];
        for (label, value) in args {
            let index = if let Some(label) = label {
                params
                    .iter()
                    .position(|p| p.name.as_ref().is_some_and(|name| name.value == label))
            } else {
                bound.iter().position(Option::is_none)
            };
            let Some(slot) = index.and_then(|i| bound.get_mut(i)) else {
                return Err(nonstatic(span));
            };
            if slot.replace(value).is_some() {
                return Err(nonstatic(span));
            }
        }
        let mut out = Vec::with_capacity(params.len());
        for (param, value) in params.iter().zip(bound) {
            if let Some(value) = value {
                out.push(value);
            } else if param.default.is_none() {
                return Err(nonstatic(span));
            }
        }
        Ok(out)
    }

    pub(super) fn eval_args(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
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

    pub(super) fn eval_call(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
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
                DefinitionKind::Primitive(_) if name == "derive" => {
                    self.eval_derive(env, slots, args, span, fuel)
                }
                DefinitionKind::Primitive(_)
                    if name == "push" && self.hir.primitive_module(id) == Some("Array") =>
                {
                    let [array, item] = args else {
                        return Err(nonstatic(span));
                    };
                    fuel.step(span)?;
                    let place = self.eval_place(env, slots, array.value, fuel)?;
                    let item = self.evaluate(env, slots, item.value, fuel)?;
                    let Value::Array(items) = place.slot(slots, false)? else {
                        return Err(defect(span, "static Array::push requires an array"));
                    };
                    items.push(item);
                    Ok(Value::Unit)
                }
                DefinitionKind::Primitive(_)
                    if name == "pop" && self.hir.primitive_module(id) == Some("Array") =>
                {
                    let [array] = args else {
                        return Err(nonstatic(span));
                    };
                    fuel.step(span)?;
                    let place = self.eval_place(env, slots, array.value, fuel)?;
                    let Value::Array(items) = place.slot(slots, false)? else {
                        return Err(defect(span, "static Array::pop requires an array"));
                    };
                    Ok(items
                        .pop()
                        .map_or_else(none, |item| Value::Tag("Some".into(), vec![item])))
                }
                DefinitionKind::Primitive(_)
                    if name == "insert" && self.hir.primitive_module(id) == Some("Map") =>
                {
                    let [map, key, value] = args else {
                        return Err(nonstatic(span));
                    };
                    fuel.step(span)?;
                    let place = self.eval_place(env, slots, map.value, fuel)?;
                    let key = self.evaluate(env, slots, key.value, fuel)?;
                    let value = self.evaluate(env, slots, value.value, fuel)?;
                    let Value::Map(entries) = place.slot(slots, false)? else {
                        return Err(defect(span, "static Map::insert requires a map"));
                    };
                    if let Some((_, existing)) = entries
                        .iter_mut()
                        .find(|(stored, _)| ieee_equal(stored, &key))
                    {
                        *existing = value;
                    } else {
                        entries.push((key, value));
                    }
                    Ok(Value::Unit)
                }
                DefinitionKind::Primitive(_)
                    if name == "remove" && self.hir.primitive_module(id) == Some("Map") =>
                {
                    let [map, key] = args else {
                        return Err(nonstatic(span));
                    };
                    fuel.step(span)?;
                    let place = self.eval_place(env, slots, map.value, fuel)?;
                    let key = self.evaluate(env, slots, key.value, fuel)?;
                    let Value::Map(entries) = place.slot(slots, false)? else {
                        return Err(defect(span, "static Map::remove requires a map"));
                    };
                    let removed = entries
                        .iter()
                        .position(|(stored, _)| ieee_equal(stored, &key))
                        .map(|index| entries.remove(index).1);
                    Ok(removed.map_or_else(none, |item| Value::Tag("Some".into(), vec![item])))
                }
                DefinitionKind::Primitive(_) if name == "inspect" => {
                    let [argument] = args else {
                        return Err(nonstatic(span));
                    };
                    fuel.step(span)?;
                    let value = self.evaluate(env, slots, argument.value, fuel)?;
                    let argument_span = self.ast(env.file).expr(argument.value).span;
                    let ty = self
                        .types
                        .get(&argument_span)
                        .cloned()
                        .unwrap_or_else(|| self.expr(env, argument.value, None));
                    Ok(Value::Str(
                        crate::ty::inspect::Plan::build(self, env, &ty).render(&value),
                    ))
                }
                DefinitionKind::Primitive(_) => {
                    fuel.step(span)?;
                    let raw_args = self.eval_args(env, slots, args, fuel)?;
                    let ordered = self.order_primitive_args(id, raw_args, span)?;
                    if let Some(intrinsic) = self.hir.intrinsic(id)
                        && let Some(result) = eval_text(intrinsic, &ordered, span)
                    {
                        return result;
                    }
                    if self.hir.primitive_module(id) == Some("Reflect")
                        && matches!(name, "attrs" | "field_attrs" | "variant_attrs")
                    {
                        self.eval_metadata(env, path, &ordered, span)
                    } else {
                        self.eval_primitive(env, name, ordered, span)
                    }
                }
                DefinitionKind::Variant(_) | DefinitionKind::Type => {
                    let mut values: Vec<_> = self
                        .eval_args(env, slots, args, fuel)?
                        .into_iter()
                        .map(|(_, value)| value)
                        .collect();
                    if def.kind == DefinitionKind::Type
                        && self.record_adts.contains(&id)
                        && let [Value::Record(record)] = values.as_mut_slice()
                    {
                        if let [arg] = args
                            && matches!(
                                self.ast(env.file).expr(arg.value).value,
                                Expr::Record { name: None, .. }
                            )
                            && let Some(stmt) = def.stmt
                        {
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
                        return Ok(Value::Record(std::mem::take(record)));
                    }
                    if values.is_empty()
                        && matches!(self.types.get(&self.ast(env.file).expr(callee).span),
                            Some(Ty::Callable(call)) if matches!(call.parameters.as_slice(), [parameter] if self.normalize(&parameter.ty) == Ty::Unit))
                    {
                        values.push(Value::Unit);
                    }
                    if self.tuple_payloads.contains_key(&span)
                        && let [Value::Tuple(items)] = values.as_slice()
                    {
                        Ok(Value::Tag(name.into(), items.clone()))
                    } else {
                        Ok(Value::Tag(name.into(), values))
                    }
                }
                DefinitionKind::Function => {
                    if self.hir.is_stdlib_file(def.name.span.file)
                        && self.hir.primitive_module(id) == Some("Prelude")
                        && name == "assert"
                    {
                        fuel.step(span)?;
                        let raw_args = self.eval_args(env, slots, args, fuel)?;
                        let ordered = self.order_primitive_args(id, raw_args, span)?;
                        return match ordered.as_slice() {
                            [Value::Bool(true), ..] => Ok(Value::Unit),
                            [Value::Bool(false), ..] => {
                                Err(Signal::Error(Code::E0830, span, "static assertion failed"))
                            }
                            _ => Err(nonstatic(span)),
                        };
                    }
                    if self.hir.is_stdlib_file(def.name.span.file)
                        && self.hir.primitive_module(id) == Some("Array")
                        && matches!(name, "filter" | "map")
                    {
                        let [array, callback] = args else {
                            return Err(nonstatic(span));
                        };
                        let Value::Array(items) = self.evaluate(env, slots, array.value, fuel)?
                        else {
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
                        return Ok(Value::Array(result));
                    }
                    let mut evaluated = Vec::with_capacity(args.len());
                    for arg in args {
                        let place = if arg.mode == syntax::Mode::Mut {
                            self.eval_place(env, slots, arg.value, fuel).ok()
                        } else {
                            None
                        };
                        let value = self.evaluate(env, slots, arg.value, fuel)?;
                        evaluated.push((
                            arg.name.as_ref().map(|name| name.value.clone()),
                            value,
                            place,
                        ));
                    }
                    self.eval_function_with_writeback(env, Some(slots), id, evaluated, span, fuel)
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

    fn eval_derive(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
        args: &[Argument],
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        let [base, update] = args else {
            return Err(nonstatic(span));
        };
        let base = self.evaluate(env, slots, base.value, fuel)?;
        let ast = self.ast(env.file);
        let Expr::Closure { params, body, .. } = &ast.expr(update.value).value else {
            return Err(nonstatic(span));
        };
        let [parameter] = params.as_slice() else {
            return Err(nonstatic(span));
        };
        let name = if let Some(pattern) = parameter.pattern {
            match &ast.pattern(pattern).value {
                syntax::Pattern::Binding(_, name) => Some(name),
                syntax::Pattern::Wildcard => None,
                _ => return Err(nonstatic(span)),
            }
        } else {
            parameter.name.as_ref()
        };
        fuel.step(span)?;
        let Some(id) = name.and_then(|name| self.resolve(name.span)) else {
            self.eval_closure(env, slots, update.value, vec![base.clone()], span, fuel)?;
            return Ok(base);
        };
        let previous = slots.locals.insert(id, base);
        let outer_places = slots.draft_places.clone();
        slots.draft_places.insert(
            id,
            Place {
                root: id,
                path: Vec::new(),
                span,
            },
        );
        let result = self.evaluate(env, slots, *body, fuel);
        slots.draft_places = outer_places;
        let updated = slots.locals.remove(&id);
        if let Some(previous) = previous {
            slots.locals.insert(id, previous);
        }
        match result {
            Ok(_) | Err(Signal::Return(_)) => updated.ok_or_else(|| nonstatic(span)),
            Err(signal) => Err(signal),
        }
    }

    pub(super) fn eval_function(
        &mut self,
        env: &Env,
        id: DefinitionId,
        args: Vec<(Option<String>, Value)>,
        span: Span,
        fuel: &mut Budget,
    ) -> Eval {
        let args = args
            .into_iter()
            .map(|(label, value)| (label, value, None))
            .collect();
        self.eval_function_with_writeback(env, None, id, args, span, fuel)
    }

    fn eval_function_with_writeback(
        &mut self,
        env: &Env,
        caller_slots: Option<&mut Frame>,
        id: DefinitionId,
        args: Vec<(Option<String>, Value, Option<Place>)>,
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
        local.generics.clone_from(&env.generics);
        let ast = self.ast(local.file);
        let stmt = def.stmt.ok_or_else(|| nonstatic(span))?;
        let StmtKind::Function(fun) = &ast.stmt(stmt).value.kind else {
            return Err(nonstatic(span));
        };
        if !fun.is_meta && !self.hir.is_stdlib_file(def.name.span.file) {
            return Err(Signal::Error(
                Code::E0810,
                span,
                "ordinary fn in static evaluation",
            ));
        }
        let body = fun.body.ok_or_else(|| nonstatic(span))?;
        self.function(&local, fun);
        local.require_concrete_types = env.require_concrete_types;
        if let Some(arguments) = self.generic_arguments.get(&span) {
            local
                .generics
                .extend(arguments.iter().map(|(&id, argument)| {
                    let argument = match argument {
                        GenericValue::Type(ty) => GenericValue::Type(crate::ty::check::substitute(
                            &self.normalize(ty),
                            &env.generics,
                        )),
                        value => value.clone(),
                    };
                    (id, argument)
                }));
        }
        fuel.step(span)?;
        if fuel.depth >= 96 {
            return Err(Signal::Error(
                Code::E0811,
                span,
                "compile-time evaluation exceeded recursion capacity",
            ));
        }
        let mut bound: Vec<Option<(Value, Option<Place>)>> = vec![None; fun.signature.params.len()];
        for (label, value, place) in args {
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
            *slot = Some((value, place));
        }
        fuel.depth += 1;
        let result = (|| {
            let mut slots = Frame::default();
            let mut guards = Vec::new();
            let mut writebacks = Vec::new();
            for (param, input) in fun.signature.params.iter().zip(bound) {
                let (input, place) = if let Some((input, place)) = input {
                    (input, place)
                } else if let Some(default) = param.default {
                    (self.evaluate(&mut local, &mut slots, default, fuel)?, None)
                } else {
                    return Err(nonstatic(span));
                };
                if param.is_meta && !param.guards.is_empty() {
                    guards.push((&param.guards, input.clone()));
                }
                if let Some(id) = param.name.as_ref().and_then(|name| self.resolve(name.span)) {
                    if param.mode == syntax::Mode::Mut
                        && let Some(place) = place
                    {
                        writebacks.push((id, place));
                    }
                    slots.locals.insert(id, input);
                }
            }
            if !guards.is_empty() {
                local.generics.extend(
                    slots
                        .locals
                        .iter()
                        .map(|(&id, value)| (id, GenericValue::Data(value.clone()))),
                );
                for (checks, input) in guards {
                    self.check_meta_input(&mut local, checks, &input, span);
                }
            }
            let outcome = match self.evaluate(&mut local, &mut slots, body, fuel) {
                Err(Signal::Return(value)) => Ok(value),
                rest => rest,
            };
            if outcome.is_ok()
                && let Some(caller_slots) = caller_slots
            {
                for (param_id, place) in writebacks {
                    if let Some(updated) = slots.locals.get(&param_id).cloned() {
                        *place.slot(caller_slots, false)? = updated;
                    }
                }
            }
            outcome
        })();
        fuel.depth -= 1;
        result
    }

    pub(super) fn eval_closure(
        &mut self,
        env: &mut Env,
        slots: &mut Frame,
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
                slots.locals.extend(bindings);
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
                    .unwrap_or_else(|| ril_source::ice!("resolved static callable disappeared"));
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
}
