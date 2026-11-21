use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use num_traits::{Signed, Zero};
use ril_base::{diag::Code, span::Span};

use ril_frontend::{
    hir::{DefinitionId, DefinitionKind, PrimitivePhase, Resolution},
    syntax::{
        self, Argument, Condition, Expr, ExprId, Mode, StmtKind, Transfer, TypeDefinition,
        ValueField,
    },
};

use super::{
    AdtKind, Callable, LiteralError, Member, Parameter, Ty, Value,
    check::{Checker, Env, ImplicitExits, Phase, substitute, unknown_callable},
    literal,
};

impl<'a> Checker<'a> {
    pub(super) fn expect(&mut self, env: &mut Env, expr: ExprId, expected: &Ty) -> Ty {
        let found = self.expr(env, expr, Some(expected));
        self.require(env, self.ast(env.file).expr(expr).span, &found, expected);
        found
    }

    pub(super) fn expr(&mut self, env: &mut Env, id: ExprId, expected: Option<&Ty>) -> Ty {
        let node = self.ast(env.file).expr(id);
        let known = expected.map(|ty| self.normalize(ty));
        let expected = known.as_ref();
        let span = node.span;
        let ty = match &node.value {
            Expr::Path(path) => self.path_expr(env, path, expected, false),
            Expr::Unit => Ty::Unit,
            Expr::Literal(value) => self.literal_type(value, span),
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let syntax::StringPart::Interpolation(value) = part {
                        let ty = self.expr(env, *value, None);
                        if !matches!(
                            ty,
                            Ty::Str | Ty::Bool | Ty::Int | Ty::F64 | Ty::Unknown | Ty::Never
                        ) {
                            self.error(
                                Code::E0301,
                                self.ast(env.file).expr(*value).span,
                                "interpolation requires str, bool, int, or f64",
                            );
                        }
                    }
                }
                Ty::Str
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                for &helper in helpers {
                    if !matches!(
                        &self.ast(env.file).stmt(helper).value.kind,
                        StmtKind::Function(_)
                    ) {
                        self.statement(env, helper, false);
                    }
                }
                let mut result = Ty::Unit;
                for (index, &item) in statements.iter().enumerate() {
                    let last = index + 1 == statements.len();
                    let right = if last
                        && let StmtKind::Expr(expr) = self.ast(env.file).stmt(item).value.kind
                    {
                        self.expr(env, expr, expected)
                    } else {
                        self.statement(env, item, last)
                    };
                    if result != Ty::Never {
                        result = right;
                    }
                }
                for &helper in helpers {
                    if let StmtKind::Function(fun) = &self.ast(env.file).stmt(helper).value.kind {
                        self.function(env, fun);
                    }
                }
                if self.exposes_type(&result, |id| {
                    let def = self.hir.definition(id);
                    def.name.span.file == env.file
                        && def.stmt.is_some_and(|stmt| helpers.contains(&stmt))
                }) {
                    self.error(Code::E0315, span, "block result exposes a local type");
                    Ty::Unknown
                } else {
                    result
                }
            }
            Expr::Unary { op, value } => self.unary(env, op, *value),
            Expr::Binary { op, left, right } => self.binary(env, op, *left, *right, expected),
            Expr::Cast { value, target } => {
                let actual = self.expr(env, *value, None);
                let target = self.type_expr(env, *target);
                if !self.sum_subset(env, &actual, &target) {
                    self.require(env, span, &actual, &target);
                }
                target
            }
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let argument = Argument {
                    name: None,
                    mode: *mode,
                    value: *value,
                };
                let target_node = self.ast(env.file).expr(*target);
                let result = if let Expr::Call { callee, args } = &target_node.value {
                    let arguments = std::iter::once(argument)
                        .chain(args.iter().cloned())
                        .collect::<Vec<_>>();
                    self.call(env, *callee, &arguments, expected, span)
                } else {
                    self.call(env, *target, &[argument], expected, span)
                };
                if *propagate {
                    self.propagate(env, result, span)
                } else {
                    result
                }
            }
            Expr::Member { base, member, safe } => {
                let receiver = self.expr(env, *base, None);
                if !safe
                    && matches!(receiver, Ty::Option(_))
                    && let Some(code) = self
                        .narrow_errors
                        .get(&self.ast(env.file).expr(*base).span)
                        .copied()
                {
                    self.error(code, span, "projection depends on an invalidated narrowing");
                    return Ty::Unknown;
                }
                if *safe {
                    match self.normalize(&receiver) {
                        Ty::Option(inner) => {
                            Ty::Option(Box::new(self.project(env, member, &inner, span, false)))
                        }
                        Ty::Unknown | Ty::Never => Ty::Unknown,
                        _ => {
                            self.error(Code::E0715, span, "safe member access requires an option");
                            Ty::Unknown
                        }
                    }
                } else {
                    self.project(env, member, &receiver, span, false)
                }
            }
            Expr::Index { base, index, safe } => self.index(env, *base, *index, *safe, span),
            Expr::Range { start, end, .. } => {
                for &value in start.iter().chain(end) {
                    self.expect(env, value, &Ty::Int);
                }
                Ty::Range
            }
            Expr::Call { callee, args } => self.call(env, *callee, args, expected, span),
            Expr::Record { name, fields } => {
                self.record(env, name.as_ref(), fields, expected, span)
            }
            Expr::Array(items) => {
                let member = if let Some(Ty::Array(member)) = expected {
                    (**member).clone()
                } else {
                    Member::plain(self.fresh())
                };
                if items.is_empty() && expected.is_none() {
                    self.error(
                        Code::E0344,
                        span,
                        "empty array requires an expected element type",
                    );
                }
                for &item in items {
                    self.expect(env, item, &member.ty);
                }
                Ty::Array(Box::new(member))
            }
            Expr::Tuple(items) => {
                let mut members = Vec::new();
                for (position, &item) in items.iter().enumerate() {
                    let member = match expected {
                        Some(Ty::Tuple(known)) => known.get(position),
                        _ => None,
                    };
                    let ty = self.expr(env, item, member.map(|m| &m.ty));
                    members.push(Member {
                        mode: member.map_or(super::MemberMode::PLAIN, |m| m.mode),
                        ty,
                    });
                }
                Ty::Tuple(members)
            }
            Expr::Map(items) => {
                let (key, member) = match expected {
                    Some(Ty::Map(key, value)) => ((**key).clone(), (**value).clone()),
                    _ => (self.fresh(), Member::plain(self.fresh())),
                };
                if items.is_empty() && expected.is_none() {
                    self.error(
                        Code::E0344,
                        span,
                        "empty map requires expected key and value types",
                    );
                }
                for &(k, v) in items {
                    self.expect(env, k, &key);
                    self.expect(env, v, &member.ty);
                }
                if matches!(
                    self.normalize(&key),
                    Ty::F64 | Ty::Callable(_) | Ty::Draft(_)
                ) {
                    self.error(Code::E0328, span, "invalid map key type");
                }
                Ty::Map(Box::new(key), Box::new(member))
            }
            Expr::Quote(ty) => Ty::TypeValue(Some(Box::new(self.type_expr(env, *ty)))),
            Expr::If { condition, yes, no } => {
                let mut yes_env = env.clone();
                self.condition(&mut yes_env, condition);
                let mut no_env = env.clone();
                if let Condition::Expr(_) = condition {
                    no_env.refinements = yes_env.refinements.clone();
                }
                self.assumption(&mut yes_env, condition, true);
                self.assumption(&mut no_env, condition, false);
                let yes = self.expr(&mut yes_env, *yes, expected);
                let no = no
                    .map(|no| self.expr(&mut no_env, no, expected))
                    .unwrap_or(Ty::Unit);
                env.refinements = self.merge_refinements(&yes_env, &no_env, &yes, &no);
                env.effects_seen.extend(yes_env.effects_seen);
                env.effects_seen.extend(no_env.effects_seen);
                self.join(env, span, yes, no)
            }
            Expr::While { condition, body } => {
                let mut body_env = env.clone();
                self.condition(&mut body_env, condition);
                self.assumption(&mut body_env, condition, true);
                let body_result = self.expr(&mut body_env, *body, None);
                env.refinements = self.merge_refinements(env, &body_env, &Ty::Unit, &body_result);
                env.effects_seen.extend(body_env.effects_seen);
                if matches!(condition, Condition::Expr(test) if matches!(&self.ast(env.file).expr(*test).value,
                    Expr::Literal(value) if matches!(literal(value), Ok(Value::Bool(true)))))
                    && !self.has_break(env, *body)
                {
                    Ty::Never
                } else {
                    Ty::Unit
                }
            }
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                let ty = self.expr(env, *iterable, None);
                let item = match self.normalize(&ty) {
                    Ty::Range => Ty::Int,
                    Ty::Array(item) => item.ty,
                    Ty::Map(key, value) => Ty::Tuple(vec![Member::plain(*key), *value]),
                    Ty::Set(item) => *item,
                    Ty::Str => Ty::Str,
                    Ty::Bytes => Ty::Int,
                    Ty::Unknown => Ty::Unknown,
                    _ => {
                        self.error(
                            Code::E0355,
                            self.ast(env.file).expr(*iterable).span,
                            "value is not iterable",
                        );
                        Ty::Unknown
                    }
                };
                self.pattern(env, *pattern, &item);
                self.expr(env, *body, None);
                Ty::Unit
            }
            Expr::Match { value, arms, .. } => {
                let input = self.expr(env, *value, None);
                self.check_match(env, arms, &input, expected, span)
            }
            Expr::Closure {
                params,
                obligations,
                body,
            } => self.closure(env, params, obligations, *body, expected),
            Expr::Accessor(segments) => {
                let label = match expected {
                    Some(Ty::Callable(call)) => call.parameters.first().map(|p| p.ty.clone()),
                    _ => None,
                }
                .unwrap_or(Ty::Unknown);
                let mut base = label.clone();
                for (safe, coordinate) in segments {
                    base = if *safe && let Ty::Option(inner) = base {
                        Ty::Option(Box::new(self.project(env, coordinate, &inner, span, false)))
                    } else {
                        self.project(env, coordinate, &base, span, false)
                    };
                }
                Ty::Callable(Arc::new(Callable {
                    parameters: vec![Parameter {
                        label: None,
                        mode: Mode::Plain,
                        ty: label,
                        optional: false,
                        is_meta: false,
                    }],
                    result: base,
                    ..unknown_callable()
                }))
            }
            Expr::Transfer { kind, value } => {
                if *kind == Transfer::Return {
                    self.check_return(env, *value, span);
                }
                Ty::Never
            }
            Expr::Hole => {
                self.error(Code::E0360, span, "unfinished expression hole");
                Ty::Never
            }
        };
        let ty = self.apply_refinement(env, id, ty);
        self.types.insert(span, ty.clone());
        ty
    }

    pub(super) fn literal_type(&mut self, syntax: &syntax::Literal, span: Span) -> Ty {
        match literal(syntax) {
            Ok(Value::Int(_)) => Ty::Int,
            Ok(Value::F64(_)) => Ty::F64,
            Ok(Value::Str(_)) => Ty::Str,
            Ok(Value::Bytes(_)) => Ty::Bytes,
            Ok(Value::Bool(_)) => Ty::Bool,
            Err(LiteralError::Overflow) => {
                self.error(
                    Code::E0326,
                    span,
                    "floating literal is outside the finite f64 range",
                );
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn path_expr(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        expected: Option<&Ty>,
        called: bool,
    ) -> Ty {
        if let Some(id) = self.resolve(path.span) {
            let def = self.hir.definition(id);
            if matches!(def.kind, DefinitionKind::Variant(_)) {
                return self.variant(env, id, expected, path.span);
            }
            if matches!(def.kind, DefinitionKind::Primitive(_)) {
                match def.name.value.as_str() {
                    "None" => {
                        let ty = if let Some(Ty::Option(ty)) = expected {
                            (**ty).clone()
                        } else {
                            self.fresh()
                        };
                        return Ty::Option(Box::new(ty));
                    }
                    "HAS_OPENAT" => return Ty::Bool,
                    "OS" | "ARCH" => return Ty::Str,
                    _ => {}
                }
            }
            let ty = self.def_type(env, id, path.span, called);
            substitute(&ty, &env.generics)
        } else {
            if matches!(self.hir.resolve(path.span), Some(Resolution::Module(_))) {
                self.error(Code::E0319, path.span, "module cannot be used as a value");
            }
            Ty::Unknown
        }
    }

    fn unary(&mut self, env: &mut Env, op: &syntax::Name, value: ExprId) -> Ty {
        let ty = self.expr(env, value, None);
        match op.value.as_str() {
            "!" => {
                if !self.fits(env, &ty, &Ty::Bool) {
                    self.error(Code::E0350, op.span, "logical negation requires bool");
                }
                Ty::Bool
            }
            "-" => {
                self.require_domain(env, &ty, &[Ty::Int, Ty::F64], op.span);
                ty
            }
            "~" => {
                self.require_domain(env, &ty, &[Ty::Int], op.span);
                ty
            }
            "?" => self.propagate(env, ty, op.span),
            "ref" | "^mut" if ty.is_value() => {
                self.error(
                    Code::E0402,
                    op.span,
                    "value types do not have live access modes",
                );
                ty
            }
            _ => ty,
        }
    }

    fn binary(
        &mut self,
        env: &mut Env,
        op: &syntax::Name,
        left: ExprId,
        right: ExprId,
        expected: Option<&Ty>,
    ) -> Ty {
        let name = op.value.as_str();
        let assignment = matches!(
            name,
            "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | "&=" | "|=" | "^="
        );
        let ast = self.ast(env.file);
        let previous = env.unrefined;
        if assignment {
            env.unrefined = Some(ast.expr(left).span);
        }
        let a = self.expr(
            env,
            left,
            if name == "??" {
                None
            } else {
                expected.filter(|_| matches!(name, "+" | "-" | "*" | "/" | "%"))
            },
        );
        env.unrefined = previous;
        let a = self.normalize(&a);
        let right_expected = match (&a, name) {
            (Ty::Option(item), "??") => Some(item.as_ref()),
            (_, "??" | "<<" | ">>") => None,
            _ => Some(&a),
        };
        let b = self.expr(env, right, right_expected);
        let b = self.normalize(&b);
        if !assignment
            && matches!(
                name,
                "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | "&" | "|" | "^"
            )
        {
            for expression in [left, right] {
                let span = ast.expr(expression).span;
                if let Some(code) = self.narrow_errors.get(&span).copied() {
                    self.error(code, span, "operation depends on an invalidated narrowing");
                    return Ty::Unknown;
                }
            }
        }
        if matches!(
            name,
            "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<" | ">" | "<=" | ">="
        ) && matches!(a, Ty::Infer(_))
            && !matches!(b, Ty::Infer(_) | Ty::Unknown)
        {
            self.fits(env, &a, &b);
        }
        let a = self.normalize(&a);
        if name == "??" {
            return match &a {
                Ty::Option(ty) => {
                    self.require(env, op.span, &b, ty);
                    (**ty).clone()
                }
                Ty::Result(..) => {
                    if let Ty::Callable(call) = b
                        && call.parameters.len() == 1
                        && let Ty::Result(ok, err) = a
                    {
                        if let Some(param) = call.parameters.first() {
                            self.require(env, op.span, &err, &param.ty);
                        }
                        self.require(env, op.span, &call.result, &ok);
                        return *ok;
                    }
                    self.error(
                        Code::E0711,
                        op.span,
                        "result fallback requires a one-argument callable",
                    );
                    Ty::Unknown
                }
                Ty::Unknown | Ty::Never => Ty::Unknown,
                _ => {
                    self.error(
                        Code::E0714,
                        op.span,
                        "fallback requires an option or result",
                    );
                    Ty::Unknown
                }
            };
        }
        if matches!(name, "&&" | "||") {
            let valid = self.fits(env, &a, &Ty::Bool) && self.fits(env, &b, &Ty::Bool);
            if !valid {
                self.error(
                    Code::E0350,
                    op.span,
                    "logical operators require bool operands",
                );
            }
            return Ty::Bool;
        }
        let comparison = matches!(name, "==" | "!=" | "<" | ">" | "<=" | ">=");
        if matches!(name, "==" | "!=") && [left, right].iter().any(|&expr| self.is_none(env, expr))
        {
            for (id, ty) in [(left, &a), (right, &b)] {
                let span = ast.expr(id).span;
                if self.narrowings.contains_key(&span) && !matches!(ty, Ty::Option(_) | Ty::Unknown)
                {
                    self.error(
                        Code::E0311,
                        span,
                        "None test contradicts the current narrowing",
                    );
                    return Ty::Bool;
                }
            }
        }
        let base = if assignment {
            name.strip_suffix('=').unwrap_or_default()
        } else {
            name
        };
        let equality = matches!(name, "==" | "!=");
        if !equality || !matches!((&a, &b), (Ty::TypeValue(_), Ty::TypeValue(_))) {
            self.require(env, op.span, &b, &a);
        }
        match base {
            "" => {}
            "+" | "-" | "*" | "/" | "%" => {
                self.require_domain(env, &a, &[Ty::Int, Ty::F64], op.span);
            }
            "&" | "|" | "^" | "<<" | ">>" => self.require_domain(env, &a, &[Ty::Int], op.span),
            "<" | ">" | "<=" | ">=" => {
                self.require_domain(env, &a, &[Ty::Int, Ty::F64, Ty::Str, Ty::Bytes], op.span);
            }
            "==" | "!="
                if !(self.is_none(env, left) || self.is_none(env, right))
                    && !self.equatable(env, &a, &mut HashSet::new()) =>
            {
                self.error(Code::E0327, op.span, "type does not support equality");
            }
            _ => {}
        }
        if matches!(base, "/" | "%" | "<<" | ">>")
            && let Some(integer) = self.literal_integer(env, right)
            && (matches!(base, "/" | "%") && integer.is_zero()
                || matches!(base, "<<" | ">>") && integer.is_negative())
        {
            self.error(
                Code::E0361,
                self.ast(env.file).expr(right).span,
                "invalid literal divisor or shift count",
            );
        }
        if assignment {
            self.writes_place(env, left);
            Ty::Unit
        } else if comparison {
            Ty::Bool
        } else {
            a
        }
    }

    pub(super) fn is_none(&self, env: &Env, id: ExprId) -> bool {
        matches!(&self.ast(env.file).expr(id).value, Expr::Path(path) if path.segments.last().is_some_and(|part| part.name.value == "None"))
    }

    fn equatable(&mut self, env: &Env, ty: &Ty, seen: &mut HashSet<DefinitionId>) -> bool {
        match ty {
            Ty::Callable(_)
            | Ty::Draft(_)
            | Ty::Scope
            | Ty::Task(_)
            | Ty::Sender(_)
            | Ty::Receiver(_) => false,
            Ty::Array(item) => self.equatable(env, &item.ty, seen),
            Ty::Tuple(items) => items.iter().all(|item| self.equatable(env, &item.ty, seen)),
            Ty::Record(fields, _) => fields
                .values()
                .all(|field| self.equatable(env, &field.ty, seen)),
            Ty::Result(ok, err) => self.equatable(env, ok, seen) && self.equatable(env, err, seen),
            Ty::Option(ty) | Ty::Set(ty) => self.equatable(env, ty, seen),
            Ty::Map(key, value) => {
                self.equatable(env, key, seen) && self.equatable(env, &value.ty, seen)
            }
            Ty::Adt(adt) if adt.kind == AdtKind::Foreign => false,
            Ty::Adt(adt) if seen.insert(adt.definition) => self
                .representation(env, adt)
                .is_none_or(|ty| self.equatable(env, &ty, seen)),
            _ => true,
        }
    }

    fn literal_integer(&self, env: &Env, id: ExprId) -> Option<num_bigint::BigInt> {
        let ast = self.ast(env.file);
        match &ast.expr(id).value {
            Expr::Literal(number) => match literal(number).ok()? {
                Value::Int(number) => Some(number),
                _ => None,
            },
            Expr::Unary { op, value } if op.value == "-" => {
                self.literal_integer(env, *value).map(|i| -i)
            }
            _ => None,
        }
    }

    fn require_domain(&mut self, env: &Env, actual: &Ty, valid: &[Ty], span: Span) {
        let valid_type = match actual {
            Ty::Param(id) => env
                .domains
                .get(id)
                .is_some_and(|domain| domain.iter().all(|item| valid.contains(item))),
            Ty::Unknown | Ty::Never => true,
            Ty::Infer(_) => false,
            _ => valid.contains(actual),
        };
        if !valid_type {
            self.error(
                Code::E0327,
                span,
                format!("operator does not accept {}", actual.display(self.hir)),
            );
        }
    }

    fn condition(&mut self, env: &mut Env, condition: &Condition) {
        match condition {
            Condition::Binding { pattern, value, .. } => {
                let ty = self.expr(env, *value, None);
                self.pattern(env, *pattern, &ty);
            }
            Condition::Expr(value) => {
                let ty = self.expr(env, *value, Some(&Ty::Bool));
                if !self.fits(env, &ty, &Ty::Bool) {
                    self.error(
                        Code::E0350,
                        self.ast(env.file).expr(*value).span,
                        "condition must be bool",
                    );
                }
            }
        }
    }

    fn has_break(&self, env: &Env, id: ExprId) -> bool {
        let ast = self.ast(env.file);
        match &ast.expr(id).value {
            Expr::Transfer {
                kind: Transfer::Break,
                ..
            } => true,
            Expr::Block { statements, .. } => {
                statements
                    .iter()
                    .any(|&stmt| match ast.stmt(stmt).value.kind {
                        StmtKind::Expr(id) => self.has_break(env, id),
                        _ => false,
                    })
            }
            Expr::If { yes, no, .. } => {
                self.has_break(env, *yes) || no.is_some_and(|no| self.has_break(env, no))
            }
            Expr::Match { arms, .. } => arms.iter().any(|arm| self.has_break(env, arm.body)),
            _ => false,
        }
    }

    fn propagate(&mut self, env: &Env, actual: Ty, span: Span) -> Ty {
        match self.normalize(&actual) {
            Ty::Result(ok, error) => {
                if let Some(index) = env.inferred_return {
                    if !env.shadow {
                        self.closure_exits(index).errors.push(*error);
                    }
                } else if !matches!(&env.expected_return, Some(Ty::Result(_, target))
                    if self.fits(env, &error, target) || self.sum_subset(env, &error, target))
                {
                    self.error(
                        Code::E0713,
                        span,
                        "enclosing function cannot propagate this error type",
                    );
                }
                *ok
            }
            Ty::Option(ok) => {
                if let Some(index) = env.inferred_return {
                    if !env.shadow {
                        self.closure_exits(index).none = true;
                    }
                } else if !matches!(env.expected_return, Some(Ty::Option(_))) {
                    self.error(
                        Code::E0713,
                        span,
                        "enclosing function cannot propagate None",
                    );
                }
                *ok
            }
            Ty::Unknown | Ty::Never => actual,
            _ => {
                self.error(Code::E0712, span, "propagation requires Result or Option");
                Ty::Unknown
            }
        }
    }

    fn check_return(&mut self, env: &mut Env, value: Option<ExprId>, span: Span) {
        let target = env.expected_return.clone();
        let actual = value.map_or(Ty::Unit, |value| self.expr(env, value, target.as_ref()));
        if env.return_scope.is_some_and(|scope| {
            self.exposes_type(&actual, |id| {
                let name = self.hir.definition(id).name.span;
                name.file == scope.file && scope.start <= name.start && name.end <= scope.end
            })
        }) {
            self.error(
                Code::E0315,
                span,
                "return exposes a type declared inside the callable",
            );
        } else if let Some(target) = target {
            self.require(env, span, &actual, &target);
        } else if let Some(index) = env.inferred_return
            && !env.shadow
        {
            self.closure_exits(index).returns.push((span, actual));
        }
    }

    fn infer_closure_result(
        &mut self,
        env: &Env,
        body: Ty,
        exits: ImplicitExits,
        span: Span,
    ) -> Ty {
        let result = exits
            .returns
            .into_iter()
            .fold(body, |result, (at, returned)| {
                self.join(env, at, result, returned)
            });
        let result = self.normalize(&result);
        if exits.errors.is_empty() && !exits.none {
            return result;
        }
        if exits.none {
            if exits.errors.is_empty() {
                let target = Ty::Option(Box::new(self.fresh()));
                if self.fits(env, &result, &target) {
                    return self.normalize(&target);
                }
            }
        } else {
            let mut errors = exits
                .errors
                .iter()
                .map(|ty| self.normalize(ty))
                .collect::<Vec<_>>();
            let mut greatest = None;
            // A candidate must dominate every error originating at a propagation site.
            // Distinct nominal types with equal tag sets are still separate candidates.
            while let Some(candidate) = errors.pop() {
                if exits.errors.iter().all(|ty| {
                    let ty = self.normalize(ty);
                    ty == candidate || self.sum_subset(env, &ty, &candidate)
                }) {
                    if greatest
                        .as_ref()
                        .is_some_and(|previous| previous != &candidate)
                    {
                        greatest = None;
                        break;
                    }
                    greatest = Some(candidate);
                }
            }
            if let Some(error) = greatest {
                let target = Ty::Result(Box::new(self.fresh()), Box::new(error));
                if self.fits(env, &result, &target) {
                    return self.normalize(&target);
                }
            }
        }
        self.error(
            Code::E0344,
            span,
            "cannot infer a fallible closure result from these propagation sites",
        );
        Ty::Unknown
    }

    pub(super) fn sum_subset(&mut self, env: &Env, actual: &Ty, target: &Ty) -> bool {
        let (Ty::Adt(actual), Ty::Adt(target)) = (self.normalize(actual), self.normalize(target))
        else {
            return false;
        };
        self.sum_includes(env, &actual, &target, &mut HashSet::new())
    }

    fn sum_includes(
        &mut self,
        env: &Env,
        actual: &super::Adt,
        target: &super::Adt,
        active: &mut HashSet<DefinitionId>,
    ) -> bool {
        if !matches!(target.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
            return false;
        }
        if actual.definition == target.definition {
            return actual.arguments == target.arguments;
        }
        if (target.kind == AdtKind::OpaqueSum && env.scope != target.defining_scope)
            || !active.insert(target.definition)
        {
            return false;
        }
        let mut local = self.instantiate_adt(target);
        let includes = self.sum_declaration(target).is_some_and(|variants| {
            variants.iter().any(|variant| {
                let syntax::Variant::Spread(ty) = variant else {
                    return false;
                };
                let Ty::Adt(subset) = self.type_expr(&mut local, *ty) else {
                    return false;
                };
                self.sum_includes(&local, actual, &subset, active)
            })
        });
        active.remove(&target.definition);
        includes
    }

    fn sum_declaration(&self, adt: &super::Adt) -> Option<&'a [syntax::Variant]> {
        let definition = self.hir.definition(adt.definition);
        let stmt = definition.stmt?;
        let StmtKind::Type(decl) = &self.ast(definition.name.span.file).stmt(stmt).value.kind
        else {
            return None;
        };
        match &decl.definition {
            TypeDefinition::Sum(variants) => Some(variants),
            _ => None,
        }
    }

    pub(super) fn sum_variants(
        &mut self,
        adt: &super::Adt,
        seen: &mut HashSet<DefinitionId>,
    ) -> BTreeMap<String, Vec<Ty>> {
        if !seen.insert(adt.definition) {
            return BTreeMap::new();
        }
        let mut local = self.instantiate_adt(adt);
        let Some(stmt) = self.hir.definition(adt.definition).stmt else {
            return BTreeMap::new();
        };
        let StmtKind::Type(decl) = &self.ast(local.file).stmt(stmt).value.kind else {
            return BTreeMap::new();
        };
        let TypeDefinition::Sum(variants) = &decl.definition else {
            return BTreeMap::new();
        };
        let mut all = BTreeMap::new();
        for variant in variants {
            match variant {
                syntax::Variant::Constructor { name, payload, .. } => {
                    let payload = payload
                        .iter()
                        .flatten()
                        .map(|&ty| self.type_expr(&mut local, ty))
                        .collect();
                    all.insert(name.value.clone(), payload);
                }
                syntax::Variant::Spread(ty) => {
                    if let Ty::Adt(subset) = self.type_expr(&mut local, *ty) {
                        for (name, types) in self.sum_variants(&subset, seen) {
                            if all.get(&name).is_some_and(|prior| prior != &types) {
                                self.error(
                                    Code::E0213,
                                    self.ast(local.file).ty(*ty).span,
                                    format!("conflicting variant {name}"),
                                );
                            } else {
                                all.insert(name, types);
                            }
                        }
                    }
                }
                syntax::Variant::Extensible => {}
            }
        }
        seen.remove(&adt.definition);
        all
    }

    fn index(&mut self, env: &mut Env, base: ExprId, index: ExprId, safe: bool, span: Span) -> Ty {
        let base = self.expr(env, base, None);
        let (key, value) = match self.normalize(&base) {
            Ty::Array(item) => (Ty::Int, item.ty),
            Ty::Map(key, value) => (*key, value.ty),
            Ty::Str => (Ty::Int, Ty::Str),
            Ty::Bytes => (Ty::Int, Ty::Int),
            Ty::Unknown => (Ty::Unknown, Ty::Unknown),
            _ => {
                self.error(
                    Code::E0352,
                    span,
                    "index target must be an array, map, str, or bytes",
                );
                (Ty::Unknown, Ty::Unknown)
            }
        };
        let index_ty = self.expr(env, index, Some(&key));
        let ty = if index_ty == Ty::Range && matches!(base, Ty::Array(_) | Ty::Str | Ty::Bytes) {
            base
        } else {
            self.require(env, self.ast(env.file).expr(index).span, &index_ty, &key);
            value
        };
        if safe { Ty::Option(Box::new(ty)) } else { ty }
    }

    fn record(
        &mut self,
        env: &mut Env,
        name: Option<&syntax::Path>,
        fields: &[ValueField],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let data = name
            .map(|path| self.named_type(env, path))
            .or_else(|| expected.cloned());
        let mut raw = data.clone();
        if let Some(Ty::Adt(adt)) = &data {
            if adt.kind == AdtKind::Foreign {
                self.error(Code::E0907, span, "cannot construct a foreign handle");
                return Ty::Unknown;
            }
            if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
                self.error(Code::E0308, span, "opaque type construction is sealed");
                return Ty::Unknown;
            }
            raw = self.representation(env, adt);
        }
        if let Some(Ty::Record(required, open)) = raw {
            let mut provided = BTreeMap::new();
            for field in fields {
                let found = required.get(&field.name.value);
                if found.is_none() && !open {
                    self.error(Code::E0302, field.name.span, "unexpected record field");
                }
                let ty = self.field_expr(env, field, found.map(|m| &m.ty));
                let mode = found.map_or_else(|| self.member_mode(env, &field.storage), |r| r.mode);
                if let Some(found) = found {
                    self.require(env, field.name.span, &ty, &found.ty);
                    let written = self.member_mode(env, &field.storage);
                    if written != super::MemberMode::PLAIN
                        && written != mode
                        && mode.mode != Mode::Via
                    {
                        self.error(Code::E0357, field.name.span, "incompatible field mode");
                    }
                }
                provided.insert(field.name.value.as_str(), ());
            }
            let defaults = self.record_defaults(&data);
            for field in required.keys() {
                if !provided.contains_key(field.as_str()) && !defaults.contains(field) && !open {
                    self.error(Code::E0307, span, format!("missing record field {field}"));
                }
            }
            data.unwrap_or(Ty::Unknown)
        } else if name.is_some() && !matches!(data, Some(Ty::Unknown)) {
            self.error(
                Code::E0301,
                span,
                "named record construction requires a record representation",
            );
            Ty::Unknown
        } else {
            let fields = fields
                .iter()
                .map(|field| {
                    (
                        field.name.value.clone(),
                        Member {
                            mode: self.member_mode(env, &field.storage),
                            ty: self.field_expr(env, field, None),
                        },
                    )
                })
                .collect();
            Ty::Record(fields, false)
        }
    }

    pub(super) fn record_defaults(&self, ty: &Option<Ty>) -> HashSet<String> {
        let Some(Ty::Adt(adt)) = ty else {
            return HashSet::new();
        };
        let def = self.hir.definition(adt.definition);
        let Some(stmt) = def.stmt else {
            return HashSet::new();
        };
        let ast = self.ast(def.name.span.file);
        let StmtKind::Type(decl) = &ast.stmt(stmt).value.kind else {
            return HashSet::new();
        };
        let TypeDefinition::Data(ty) = decl.definition else {
            return HashSet::new();
        };
        if let syntax::Type::Record { fields, .. } = &ast.ty(ty).value {
            fields
                .iter()
                .filter(|field| field.default.is_some())
                .map(|field| field.name.value.clone())
                .collect()
        } else {
            HashSet::new()
        }
    }

    fn field_expr(&mut self, env: &mut Env, field: &ValueField, expected: Option<&Ty>) -> Ty {
        if let Some(expr) = field.value {
            self.expr(env, expr, expected)
        } else if let Some(id) = self.resolve(field.name.span) {
            self.def_type(env, id, field.name.span, false)
        } else {
            Ty::Unknown
        }
    }

    fn closure(
        &mut self,
        env: &Env,
        params: &[syntax::Parameter],
        obligations: &syntax::Obligations,
        body: ExprId,
        expected: Option<&Ty>,
    ) -> Ty {
        let expected_call = if let Some(Ty::Callable(call)) = expected {
            Some(call)
        } else {
            None
        };
        let mut local = env.clone();
        local.expected_return = expected_call.map(|sig| sig.result.clone());
        local.inferred_return = None;
        local.return_scope = Some(self.ast(env.file).expr(body).span);
        let mut parameters = Vec::new();
        for (index, item) in params.iter().enumerate() {
            let expected_param = expected_call.and_then(|sig| sig.parameters.get(index));
            let ty = if let Some(ty) = item.ty {
                self.type_expr(&mut local, ty)
            } else if let Some(param) = expected_param {
                param.ty.clone()
            } else {
                self.fresh()
            };
            if let Some(pattern) = item.pattern {
                self.pattern(&mut local, pattern, &ty);
            } else if let Some(name) = &item.name {
                self.define_name(name, ty.clone());
            }
            if let Some(default) = item.default {
                self.expect(&mut local, default, &ty);
            }
            parameters.push(Parameter {
                label: item.name.as_ref().map(|name| name.value.clone()),
                mode: item.mode,
                ty,
                optional: item.default.is_some(),
                is_meta: item.is_meta,
            });
        }
        let infer_result = local.expected_return.is_none();
        if infer_result {
            local.inferred_return = Some(self.implicit_exits.len());
            self.implicit_exits.push(ImplicitExits::default());
        }
        let target = local.expected_return.clone();
        let result = self.expr(&mut local, body, target.as_ref());
        let result = if infer_result {
            let exits = self.implicit_exits.pop().unwrap_or_else(|| {
                ril_base::ice!("missing inference state for the current closure")
            });
            self.infer_closure_result(&local, result, exits, self.ast(env.file).expr(body).span)
        } else {
            result
        };
        let effects = if obligations.effects.is_empty() {
            let mut used: Vec<_> = local
                .effects_seen
                .difference(&env.effects_seen)
                .cloned()
                .collect();
            used.sort();
            used
        } else {
            obligations
                .effects
                .iter()
                .map(|path| self.effect_label(path))
                .collect()
        };
        Ty::Callable(Arc::new(Callable {
            parameters,
            result,
            effects,
            open_effects: obligations.open_effects,
            ..unknown_callable()
        }))
    }

    fn call(
        &mut self,
        env: &mut Env,
        callee_id: ExprId,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let ast = self.ast(env.file);
        let callee = ast.expr(callee_id);
        let path = match &callee.value {
            Expr::Path(path) => Some(path),
            _ => None,
        };
        let def_id = path.and_then(|p| self.resolve(p.span));
        if !env.shadow
            && let Some(effect) = def_id.and_then(|id| self.hir.operation_effect(id))
        {
            env.effects_seen.insert(self.hir.effect_label(effect));
        }
        let mut pending_meta = false;
        let (ty, generics) = if let Some(id) = def_id {
            let def = self.hir.definition(id);
            match def.kind {
                DefinitionKind::Primitive(phase) => {
                    if let Some(module @ ("Fiber" | "Channel")) = self.hir.primitive_module(id) {
                        return self.concurrent_call(
                            env,
                            module,
                            &def.name.value,
                            args,
                            expected,
                            span,
                        );
                    }
                    if !env.shadow
                        && phase == PrimitivePhase::Runtime
                        && env.phase != Phase::Runtime
                    {
                        self.error(
                            Code::E0810,
                            callee.span,
                            "runtime primitive called in static computation",
                        );
                    }
                    return self.primitive_call(env, &def.name.value, args, expected, span);
                }
                DefinitionKind::Type => {
                    let ty = self.named_type(
                        env,
                        path.unwrap_or_else(|| ril_base::ice!("constructor without path")),
                    );
                    return self.nominal_constructor(env, ty, args, span);
                }
                DefinitionKind::Function => {
                    pending_meta =
                        self.is_meta_fn(id) && env.phase == Phase::Runtime && !env.shadow;
                    if !env.shadow && !self.is_meta_fn(id) && env.phase != Phase::Runtime {
                        self.error(
                            Code::E0810,
                            callee.span,
                            "ordinary runtime fn called in static computation",
                        );
                    }
                    let args = path
                        .and_then(|p| p.segments.last())
                        .map_or(&[][..], |p| p.arguments.as_slice());
                    (
                        Ty::Callable(self.declare_function(id)),
                        self.call_argument_types(env, id, args, span),
                    )
                }
                _ => (
                    self.path_expr(
                        env,
                        path.unwrap_or_else(|| ril_base::ice!("resolved call without path")),
                        expected,
                        true,
                    ),
                    Default::default(),
                ),
            }
        } else {
            (self.expr(env, callee_id, None), Default::default())
        };
        self.types.insert(callee.span, ty.clone());
        let Ty::Callable(call) = self.normalize(&ty) else {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            if ty != Ty::Unknown && ty != Ty::Never {
                self.error(Code::E0338, callee.span, "expression is not callable");
            }
            return Ty::Unknown;
        };

        let result = substitute(&call.result, &generics);
        if let Some(expect) = expected {
            self.fits(env, &result, expect);
        }
        let mut used = vec![false; call.parameters.len()];
        for arg in args {
            let location = if let Some(name) = &arg.name {
                call.parameters
                    .iter()
                    .position(|p| p.label.as_deref() == Some(&name.value))
            } else {
                used.iter().position(|used| !used)
            };
            let arg_span = ast.expr(arg.value).span;
            let Some(index) = location else {
                self.error(
                    if arg.name.is_some() {
                        Code::E0339
                    } else {
                        Code::E0314
                    },
                    arg_span,
                    "no parameter matches this argument",
                );
                self.expr(env, arg.value, None);
                continue;
            };
            if used.get(index) == Some(&true) {
                self.error(Code::E0325, arg_span, "parameter was already supplied");
            }
            if let Some(used) = used.get_mut(index) {
                *used = true;
            }
            let parameter = call
                .parameters
                .get(index)
                .unwrap_or_else(|| ril_base::ice!("bound argument without parameter"));
            self.expect(env, arg.value, &substitute(&parameter.ty, &generics));
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && self.types.get(&arg_span).is_some_and(Ty::is_value)
            {
                self.error(
                    Code::E0402,
                    arg_span,
                    "value-type argument cannot carry live authority",
                );
            }
            if !parameter.is_meta && parameter.mode != Mode::Via && parameter.mode != arg.mode {
                self.error(
                    if arg.mode == Mode::Plain {
                        Code::E0405
                    } else {
                        Code::E0406
                    },
                    arg_span,
                    "required explicit argument mode does not match",
                );
            }
            if parameter.is_meta && !env.shadow {
                self.eval_root(env, arg.value, true);
            }
        }
        if call
            .parameters
            .iter()
            .zip(used)
            .any(|(param, supplied)| !supplied && !param.optional)
        {
            self.error(Code::E0314, span, "required argument is missing");
        }
        if call.open_effects || call.open_state {
            self.invalidate_live(env, Code::E0533);
        } else if call
            .state
            .iter()
            .any(|clause| clause == "mut" || clause == "^mut")
        {
            for argument in args
                .iter()
                .filter(|arg| matches!(arg.mode, Mode::Mut | Mode::Shared))
            {
                self.writes_place(env, argument.value);
            }
        }
        if !env.shadow {
            env.effects_seen.extend(call.effects.iter().cloned());
        }
        if let Some(known) = def_id {
            self.validate_generic_uses(env, known, &generics, span);
        }
        if pending_meta && let Some(id) = def_id {
            self.eval_call_root(env, id, args, span);
        }
        self.normalize(&result)
    }

    fn nominal_constructor(&mut self, env: &mut Env, ty: Ty, args: &[Argument], span: Span) -> Ty {
        let Ty::Adt(adt) = &ty else {
            if ty != Ty::Unknown {
                self.error(Code::E0338, span, "type is not a payload constructor");
            }
            return Ty::Unknown;
        };
        if adt.kind == AdtKind::Foreign {
            self.error(Code::E0907, span, "foreign nominal cannot be constructed");
            return Ty::Unknown;
        }
        if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
            self.error(Code::E0308, span, "opaque constructor is sealed");
            return Ty::Unknown;
        }
        let params = match self.representation(env, adt) {
            Some(Ty::Unit | Ty::Record(..)) | None => {
                self.error(
                    Code::E0338,
                    span,
                    "unit and record types do not use payload call syntax",
                );
                return Ty::Unknown;
            }
            Some(Ty::Tuple(fields)) => fields.into_iter().map(|m| m.ty).collect(),
            Some(one) => vec![one],
        };
        if args.len() != params.len() {
            self.error(Code::E0314, span, "invalid constructor payload arity");
        }
        for (arg, ty) in args.iter().zip(params) {
            if arg.mode != Mode::Plain {
                self.error(
                    Code::E0406,
                    self.ast(env.file).expr(arg.value).span,
                    "constructors receive plain payloads",
                );
            }
            self.expect(env, arg.value, &ty);
        }
        ty
    }

    pub(super) fn primitive_type(
        &mut self,
        _env: &Env,
        name: &str,
        span: Span,
        callee: bool,
    ) -> Ty {
        match name {
            "Let" => Ty::Mode,
            "Var" | "Mut" | "Ref" | "SharedMut" | "VarMut" | "VarRef" | "VarSharedMut" => Ty::Mode,
            "bool" | "int" | "f64" | "str" | "bytes" | "never" | "Type" if !callee => {
                self.error(Code::E0319, span, "type value requires angle quotation");
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn primitive_call(
        &mut self,
        env: &mut Env,
        name: &str,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        if name == "derive"
            && let [base, update] = args
        {
            let base = self.expr(env, base.value, expected);
            if base.is_value() {
                self.error(
                    Code::E0536,
                    span,
                    "derive requires a shared-object snapshot",
                );
            }
            let callback = Ty::Callable(Arc::new(Callable {
                parameters: vec![Parameter {
                    label: None,
                    mode: Mode::Mut,
                    ty: Ty::Draft(Box::new(base.clone())),
                    optional: false,
                    is_meta: false,
                }],
                result: Ty::Unit,
                result_mode: Mode::Infer,
                open_state: true,
                open_effects: true,
                ..unknown_callable()
            }));
            self.expect(env, update.value, &callback);
            return base;
        }
        let context_arg = match (name, expected) {
            ("Some", Some(Ty::Option(ty)))
            | ("Ok", Some(Ty::Result(ty, _)))
            | ("Err", Some(Ty::Result(_, ty))) => Some(ty.as_ref()),
            _ => None,
        };
        let mut types = Vec::new();
        for arg in args {
            types.push(self.expr(env, arg.value, context_arg));
        }
        let first =
            types
                .first()
                .cloned()
                .unwrap_or(if name == "Ok" { Ty::Unit } else { Ty::Unknown });
        let arity = match name {
            "Some" | "Err" | "panic" | "print" | "println" | "len" | "clone" | "inner"
            | "inspect" | "type_name" | "coords" | "variants" | "to_f64" | "to_int" | "trunc"
            | "absorb_panic" | "panic_message" => Some(1..=1),
            "Ok" => Some(0..=1),
            "assert" => Some(1..=2),
            "has_default" | "contains" | "push" | "filter" | "map" | "checked_div"
            | "checked_rem" | "derive" => Some(2..=2),
            _ => None,
        };
        if arity.is_some_and(|range| !range.contains(&args.len())) {
            self.error(
                Code::E0314,
                span,
                format!("invalid argument count for {name}"),
            );
        }
        match name {
            "read" | "write" => {
                self.require(env, span, &first, &Ty::Str);
                if name == "write"
                    && let Some(content) = types.get(1)
                {
                    self.require(env, span, content, &Ty::Str);
                }
                if !env.shadow {
                    env.effects_seen.insert("io".into());
                }
                Ty::Result(
                    Box::new(if name == "read" { Ty::Str } else { Ty::Unit }),
                    Box::new(Ty::Str),
                )
            }
            "Some" => Ty::Option(Box::new(first)),
            "Ok" => Ty::Result(
                Box::new(first),
                expected
                    .and_then(|ty| match ty {
                        Ty::Result(_, err) => Some(err.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| Box::new(self.fresh())),
            ),
            "Err" => Ty::Result(
                expected
                    .and_then(|ty| match ty {
                        Ty::Result(ok, _) => Some(ok.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| Box::new(self.fresh())),
                Box::new(first),
            ),
            "panic" | "print" | "println" => {
                self.require(env, span, &first, &Ty::Str);
                if name == "panic" {
                    Ty::Never
                } else {
                    if !env.shadow {
                        env.effects_seen.insert("io".into());
                    }
                    Ty::Unit
                }
            }
            "assert" => {
                self.require(env, span, &first, &Ty::Bool);
                if let Some(message) = types.get(1) {
                    self.require(env, span, message, &Ty::Str);
                }
                Ty::Unit
            }
            "len" => {
                if !matches!(
                    first,
                    Ty::Str
                        | Ty::Bytes
                        | Ty::Array(_)
                        | Ty::Map(..)
                        | Ty::Set(_)
                        | Ty::Unknown
                        | Ty::Param(_)
                ) {
                    self.error(
                        Code::E0301,
                        span,
                        "len requires text, bytes, or a collection",
                    );
                }
                Ty::Int
            }
            "clone" => {
                if first.is_value()
                    || matches!(&first, Ty::Adt(adt) if adt.kind == AdtKind::Foreign)
                {
                    self.error(Code::E0301, span, "clone requires a clonable shared object");
                }
                first
            }
            "inner" => match &first {
                Ty::Adt(adt) if adt.kind == AdtKind::Foreign => {
                    self.error(Code::E0907, span, "foreign representation is sealed");
                    Ty::Unknown
                }
                Ty::Adt(adt) if adt.kind == AdtKind::Nominal => {
                    self.representation(env, adt).unwrap_or(Ty::Unknown)
                }
                Ty::Unknown => Ty::Unknown,
                _ => {
                    self.error(Code::E0301, span, "inner requires a nominal wrapper");
                    Ty::Unknown
                }
            },
            "to_f64" => {
                self.require(env, span, &first, &Ty::Int);
                Ty::F64
            }
            "to_int" | "trunc" | "convert" => {
                self.require(env, span, &first, &Ty::F64);
                Ty::Option(Box::new(Ty::Int))
            }
            "checked_div" | "checked_rem" => {
                for ty in types {
                    self.require(env, span, &ty, &Ty::Int);
                }
                Ty::Option(Box::new(Ty::Int))
            }
            "coords" => {
                let key = if let Ty::TypeValue(Some(ty)) = first {
                    match *ty {
                        Ty::Record(..) => Ty::Str,
                        Ty::Tuple(_) => Ty::Int,
                        Ty::Adt(adt) if adt.kind == AdtKind::Foreign => {
                            self.error(Code::E0907, span, "foreign representation is sealed");
                            Ty::Unknown
                        }
                        Ty::Adt(adt)
                            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                                && adt.defining_scope != env.scope =>
                        {
                            self.error(Code::E0308, span, "opaque representation is sealed");
                            Ty::Unknown
                        }
                        Ty::Adt(adt)
                            if matches!(self.representation(env, &adt), Some(Ty::Record(..))) =>
                        {
                            Ty::Str
                        }
                        Ty::Param(_) | Ty::Unknown => Ty::Unknown,
                        _ => {
                            self.error(Code::E0358, span, "coords requires a tuple or record type");
                            Ty::Unknown
                        }
                    }
                } else {
                    Ty::Unknown
                };
                Ty::Array(Box::new(Member::plain(Ty::Tuple(vec![
                    Member::plain(Ty::Mode),
                    Member::plain(key),
                ]))))
            }
            "variants" => Ty::Array(Box::new(Member::plain(Ty::Str))),
            "contains" | "has_default" => Ty::Bool,
            "type_name" | "inspect" | "panic_message" => Ty::Str,
            "push" => {
                if let (Ty::Array(member), Some(item)) = (&first, types.get(1)) {
                    self.require(env, span, item, &member.ty);
                }
                Ty::Unit
            }
            "filter" => first,
            "map" => {
                let ty = types
                    .get(1)
                    .and_then(|ty| match ty {
                        Ty::Callable(sig) => Some(sig.result.clone()),
                        _ => None,
                    })
                    .unwrap_or(Ty::Unknown);
                Ty::Array(Box::new(Member::plain(ty)))
            }
            "derive" => first,
            "absorb_panic" => match first {
                Ty::Callable(call) => {
                    Ty::Result(Box::new(call.result.clone()), Box::new(Ty::Unknown))
                }
                _ => Ty::Unknown,
            },
            _ => Ty::Unknown,
        }
    }
}
