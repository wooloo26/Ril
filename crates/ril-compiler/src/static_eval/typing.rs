//! Static definitions still undergo ordinary typing when no evaluation requests
//! them. This checker deliberately refuses a proof it cannot currently express.
use super::*;
#[path = "typing_application_interfaces.rs"]
mod application_interfaces;
#[path = "typing_application_sources.rs"]
mod application_sources;
#[path = "typing_applications.rs"]
pub(super) mod applications;
#[path = "typing_bounds.rs"]
pub(super) mod bounds;
#[path = "coalescing.rs"]
mod coalescing;
#[path = "typing_const_int.rs"]
pub(super) mod const_int;
#[path = "typing_construction_contexts.rs"]
mod construction_contexts;
#[path = "typing_contexts.rs"]
mod contexts;
#[path = "typing_loops.rs"]
mod loops;
#[path = "result_flow.rs"]
mod result_flow;
#[path = "typing_runtime_application.rs"]
pub(super) mod runtime_applications;

pub(super) fn verify_result_flows(
    evaluator: &Evaluator,
    program: &Program,
    output: &mut Evaluation,
) -> bool {
    result_flow::verify(evaluator, program, output)
}
pub(super) fn closed_result_contract(evaluator: &Evaluator, syntax: &TypeExpr) -> bool {
    Typer::new(evaluator, None)
        .ty(syntax, &Env::new())
        .is_ok_and(|ty| matches!(ty, Ty::Result(..)) && !contains_generic_type(&ty))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Ty {
    Intrinsic(ril_compiler_core::builtin_types::AtomicBuiltinType),
    Unit,
    Bool,
    Number(String),
    /// An immutable int value fact, distinct from its ordinary `int` type.
    IntegerConstant(i128),
    String,
    Bytes,
    Meta,
    TypeParameter,
    Constructor(usize),
    Unknown,
    Infer,
    Generic(String),
    ForbiddenDefault(String),
    /// None admits dynamic length; Some retains a statically proved length.
    Array(Box<Ty>, Option<usize>),
    Map(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(BTreeMap<String, (bool, Ty)>),
    Optional(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    Callable(Vec<Ty>, Box<Ty>, Vec<Vec<application::ParameterSpec>>),
    Never,
}
type Env = BTreeMap<String, Ty>;

fn numeric_type(ty: &Ty) -> Option<crate::numeric_literals::NumberType> {
    match ty {
        Ty::IntegerConstant(_) => Some(crate::numeric_literals::NumberType::Int),
        Ty::Number(name) => numeric_contexts::number_name(name),
        _ => None,
    }
}

pub(super) fn verify_binding(evaluator: &Evaluator, binding: &Binding) -> Result<()> {
    let checker = Typer::new(evaluator, None);
    let mut env = evaluator
        .values
        .iter()
        .map(|(name, value)| Ok((name.clone(), checker.value_type(value)?)))
        .collect::<Result<Env>>()?;
    let initializer = record_contexts::expression(&binding.value, binding.ty.as_ref());
    let expected = binding
        .ty
        .as_ref()
        .map(|ty| checker.ty(ty, &env))
        .transpose()?;
    let result_context = binding
        .ty
        .as_ref()
        .map(|syntax| checker.context_for_syntax(syntax, &env))
        .transpose()?;
    let actual = checker.expr_result_expected(
        &initializer,
        &mut env,
        expected.as_ref(),
        result_context.as_ref(),
    )?;
    if let Some(expected) = &binding.ty {
        checker.type_names(expected, &env)?;
        require(&actual, &checker.ty(expected, &env)?)?;
    }
    Ok(())
}

/// Infer a symbolic type without running the operand, charging its operations,
/// allocating its environment, or introducing inspection duties.
pub(super) fn type_of(evaluator: &Evaluator, operand: &Expr) -> Result<TypeExpr> {
    let mut checker = Typer::new(evaluator, None);
    checker.unevaluated = true;
    let mut env = evaluator
        .values
        .iter()
        .map(|(name, value)| Ok((name.clone(), checker.value_type(value)?)))
        .collect::<Result<Env>>()?;
    if let ExprKind::Range { start, end, .. } = &operand.kind {
        let endpoints = start
            .iter()
            .chain(end)
            .map(|value| checker.expr(value, &mut env))
            .collect::<Result<Vec<_>>>()?;
        let integer = |name: &str| {
            matches!(
                name,
                "int" | "bigint" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
            )
        };
        if endpoints.iter().any(|ty| {
            !matches!(ty, Ty::IntegerConstant(_))
                && !matches!(ty, Ty::Number(name) if integer(name))
        }) {
            return Err(Failure::Diagnostic(
                "E0327",
                "range endpoints require integer values".into(),
            ));
        }
        let element = endpoints
            .iter()
            .find(|ty| matches!(ty, Ty::Number(_)))
            .cloned()
            .unwrap_or(Ty::Number("int".into()));
        for endpoint in &endpoints {
            if let (Ty::IntegerConstant(value), Ty::Number(name)) = (endpoint, &element) {
                let (bits, signed) = match name.as_str() {
                    "bigint" => continue,
                    "int" => (evaluator.layout.pointer_bits as u32, true),
                    name => (name[1..].parse::<u32>().unwrap(), name.starts_with('i')),
                };
                let fits = if signed {
                    *value >= -(1i128 << (bits - 1)) && *value < (1i128 << (bits - 1))
                } else {
                    *value >= 0 && *value < (1i128 << bits)
                };
                if !fits {
                    return Err(Failure::Diagnostic(
                        "E0326",
                        "range endpoint does not fit its integer type".into(),
                    ));
                }
            } else {
                require(endpoint, &element)?;
            }
        }
        return Ok(TypeExpr {
            hir_id: None,
            kind: TypeKind::Name {
                path: vec!["Prelude".into(), "Range".into()],
                arguments: vec![reify_type(&element, operand.span)?],
            },
            text: String::new(),
            span: operand.span,
        });
    }
    let ty = checker.expr(operand, &mut env)?;
    reify_type(&ty, operand.span)
}

fn reify_type(ty: &Ty, span: Span) -> Result<TypeExpr> {
    let name = match ty {
        Ty::Intrinsic(identity) => Some(identity.name()),
        Ty::Bool => Some("bool"),
        Ty::String => Some("str"),
        Ty::Bytes => Some("bytes"),
        Ty::Never => Some("never"),
        Ty::IntegerConstant(_) => Some("int"),
        Ty::Number(name) => Some(name.as_str()),
        _ => None,
    };
    let kind = if let Some(name) = name {
        TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: vec![],
        }
    } else {
        match ty {
            Ty::Unit => TypeKind::Tuple(vec![]),
            Ty::Tuple(items) => TypeKind::Tuple(
                items
                    .iter()
                    .map(|item| reify_type(item, span))
                    .collect::<Result<_>>()?,
            ),
            // Cardinality is a fact about a value, and is not sufficient to
            // reconstruct whether its declared array type is fixed or dynamic.
            _ => return Err(Failure::Unsupported(
                "typeof aggregate or callable needs its complete declared type and qualification"
                    .into(),
            )),
        }
    };
    Ok(TypeExpr {
        hir_id: None,
        kind,
        text: String::new(),
        span,
    })
}

pub(super) fn verify(evaluator: &Evaluator, output: &mut Evaluation, source: &Program) {
    let checker = Typer::new(evaluator, None);
    let contexts = std::sync::Arc::new(contexts::collect(evaluator, source));
    for function in output.static_definitions.clone() {
        let result = (|| {
            let mut env = contexts
                .get(&function.name)
                .map(|scope| scope.values.clone())
                .unwrap_or_else(|| checker.globals());
            for generic in &function.generics {
                env.insert(generic.name.clone(), Ty::TypeParameter);
            }
            let captured = contexts
                .get(&function.name)
                .cloned()
                .unwrap_or_else(|| bounds::BoundEnvironment::captured(checker.globals()));
            let scope = checker.function_generic_environment(&function, &captured)?;
            env = scope.values.clone();
            let mut checker =
                Typer::with_bound_environment(evaluator, None, std::sync::Arc::new(scope));
            checker.function_contexts = contexts.clone();
            let default_environment = env.clone();
            for parameter in &function.parameters {
                if let Some(ty) = &parameter.ty {
                    checker.type_names(ty, &env)?;
                }
                if parameter.mode != ParameterMode::Read {
                    return Err(Failure::Unsupported(
                        "static definition has a writable formal".into(),
                    ));
                }
                let ty = parameter.ty.as_ref().map_or(
                    Err(Failure::Unsupported(
                        "untyped named static parameter".into(),
                    )),
                    |ty| checker.ty(ty, &env),
                )?;
                checker.bind(&parameter.pattern, ty, &mut env)?;
                let schema = parameter
                    .ty
                    .as_ref()
                    .map(|syntax| {
                        checker.complete_source_syntax(
                            syntax,
                            checker.bound_environment.as_ref().unwrap(),
                        )
                    })
                    .transpose()?
                    .flatten();
                checker.bind_source_schema(&parameter.pattern, schema)?;
            }
            let Some(body) = &function.body else {
                return Err(Failure::Diagnostic(
                    "E0810",
                    "bodyless definition has no static implementation".into(),
                ));
            };
            let expected = function
                .return_type
                .as_ref()
                .map_or(Ok(Ty::Unit), |ty| checker.ty(ty, &env))?;
            let mut checker = checker.child(Some(expected.clone()));
            checker.return_context = function
                .return_type
                .as_ref()
                .map(|syntax| checker.context_for_syntax(syntax, &env))
                .transpose()?;
            checker.verify_defaults(&function.parameters, &default_environment)?;
            let body = record_contexts::block(body, function.return_type.as_ref());
            let actual = checker.block_result_expected(
                &body,
                &mut env,
                Some(&expected),
                checker.return_context.as_ref(),
            )?;
            if contains_meta_type(&actual) {
                return Err(Failure::Diagnostic(
                    "E0812",
                    "meta functions cannot return type values".into(),
                ));
            }
            require(&actual, &expected)
        })();
        if let Err(failure) = result {
            output.failure(failure, function.span);
        }
    }
    for declaration in output.type_functions.clone() {
        let Some(TypeExpr {
            kind: TypeKind::TypeFunction { parameters, body },
            ..
        }) = &declaration.value
        else {
            continue;
        };
        let result = (|| {
            let mut env = contexts
                .get(&declaration.name)
                .map(|scope| scope.values.clone())
                .unwrap_or_else(|| checker.globals());
            for parameter in parameters {
                if let Some(bound) = &parameter.bound {
                    bind_row_types(bound, &mut env, evaluator);
                    checker.type_names(bound, &env)?;
                }
                let ty = if parameter
                    .name
                    .chars()
                    .next()
                    .is_some_and(char::is_uppercase)
                {
                    if let Some(TypeExpr {
                        kind: TypeKind::KeyOf(_),
                        ..
                    }) = &parameter.bound
                    {
                        Ty::String
                    } else {
                        parameter
                            .bound
                            .as_ref()
                            .filter(|bound| matches!(bound.kind, TypeKind::KindArrow { .. }))
                            .map_or(Ty::TypeParameter, |bound| {
                                Ty::Constructor(types::kind_arity(bound))
                            })
                    }
                } else if let Some(bound) = &parameter.bound {
                    checker.ty(bound, &env)?
                } else {
                    return Err(Failure::Unsupported(
                        "static value parameter has no sort".into(),
                    ));
                };
                env.insert(parameter.name.clone(), ty);
            }
            let checker = Typer::new(evaluator, Some(Ty::Meta));
            let actual = checker.expr(body, &mut env)?;
            require(&actual, &Ty::Meta)
        })();
        if let Err(failure) = result {
            output.failure(failure, declaration.span);
        }
    }
}
struct Typer<'a> {
    evaluator: &'a Evaluator,
    return_type: Option<Ty>,
    return_context: Option<applications::ResultContext>,
    returns: std::cell::RefCell<Vec<Ty>>,
    unevaluated: bool,
    loops: std::cell::RefCell<Vec<loops::Frame>>,
    reachable: std::cell::Cell<bool>,
    bound_environment: Option<std::sync::Arc<bounds::BoundEnvironment>>,
    function_contexts: std::sync::Arc<BTreeMap<String, bounds::BoundEnvironment>>,
    schema_bindings: std::cell::RefCell<
        BTreeMap<String, Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>>,
    >,
    const_shadows: std::cell::RefCell<BTreeSet<String>>,
    application_sequence: std::rc::Rc<std::cell::Cell<u64>>,
    schema_work: std::rc::Rc<budget::Budget>,
    interface_applications: std::rc::Rc<std::cell::RefCell<BTreeSet<String>>>,
}
impl<'a> Typer<'a> {
    fn rigid_numeric_peer(&self, expression: &Expr, env: &Env) -> Option<Ty> {
        if let ExprKind::Binary {
            operator,
            left,
            right,
        } = &expression.kind
            && matches!(
                operator.as_str(),
                "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^"
            )
        {
            return self
                .rigid_numeric_peer(left, env)
                .or_else(|| self.rigid_numeric_peer(right, env));
        }
        if let Some(name) = expression_name(expression)
            && let Some(ty) = env.get(&name)
            && numeric_type(ty).is_some()
        {
            return Some(ty.clone());
        }
        let syntax = self.evaluator.rigid_numeric_peer(expression)?;
        self.ty(&syntax, env).ok()
    }
    fn new(evaluator: &'a Evaluator, return_type: Option<Ty>) -> Self {
        Self {
            evaluator,
            return_type,
            return_context: None,
            returns: std::cell::RefCell::new(vec![]),
            unevaluated: false,
            loops: std::cell::RefCell::new(vec![]),
            reachable: std::cell::Cell::new(true),
            bound_environment: None,
            function_contexts: Default::default(),
            schema_bindings: Default::default(),
            const_shadows: Default::default(),
            application_sequence: Default::default(),
            schema_work: std::rc::Rc::new(budget::Budget::default()),
            interface_applications: Default::default(),
        }
    }
    pub(super) fn with_bound_environment(
        evaluator: &'a Evaluator,
        return_type: Option<Ty>,
        environment: std::sync::Arc<bounds::BoundEnvironment>,
    ) -> Self {
        let mut typer = Self::new(evaluator, return_type);
        typer.bound_environment = Some(environment);
        typer
    }
    fn child(&self, return_type: Option<Ty>) -> Self {
        let mut typer = Self::new(self.evaluator, return_type);
        typer.bound_environment = self.bound_environment.clone();
        typer.function_contexts = self.function_contexts.clone();
        typer.schema_bindings = self.schema_bindings.clone();
        typer.const_shadows = self.const_shadows.clone();
        typer.application_sequence = self.application_sequence.clone();
        typer.schema_work = self.schema_work.clone();
        typer.interface_applications = self.interface_applications.clone();
        typer
    }
    fn callable_result(&self, actual: Ty) -> Result<Ty> {
        let returns = self.returns.borrow();
        let mut result = actual;
        for returned in returns.iter() {
            if result == Ty::Never {
                result = returned.clone();
            } else {
                result = join_types(returned, &result)?;
            }
        }
        Ok(result)
    }
    fn verify_defaults(&self, parameters: &[Parameter], environment: &Env) -> Result<()> {
        self.with_const_shadow_scope(|| {
            let mut earlier = environment.clone();
            for (index, parameter) in parameters.iter().enumerate() {
                let ty = parameter
                    .ty
                    .as_ref()
                    .map_or(Ok(Ty::Unknown), |ty| self.ty(ty, &earlier))?;
                if let Some(default) = &parameter.default {
                    if parameter.mode != ParameterMode::Read {
                        return Err(Failure::Diagnostic(
                            "E0404",
                            "mutable parameters cannot have defaults".into(),
                        ));
                    }
                    let mut forbidden = BTreeSet::new();
                    for later in &parameters[index..] {
                        application::binding_names(&later.pattern, &mut forbidden);
                    }
                    let mut scope = earlier.clone();
                    for name in forbidden {
                        scope.insert(name.clone(), Ty::ForbiddenDefault(name));
                    }
                    let syntax = record_contexts::expression(default, parameter.ty.as_ref());
                    let context = parameter
                        .ty
                        .as_ref()
                        .map(|syntax| self.context_for_syntax(syntax, &scope))
                        .transpose()?;
                    require(
                        &self.expr_result_expected(
                            &syntax,
                            &mut scope,
                            Some(&ty),
                            context.as_ref(),
                        )?,
                        &ty,
                    )?;
                }
                let mut source_scope = self
                    .bound_environment
                    .as_deref()
                    .cloned()
                    .unwrap_or_default();
                source_scope.values = earlier.clone();
                self.apply_const_shadows(&mut source_scope)?;
                let source = parameter
                    .ty
                    .as_ref()
                    .map(|syntax| self.complete_source_syntax(syntax, &source_scope))
                    .transpose()?
                    .flatten();
                self.bind(&parameter.pattern, ty, &mut earlier)?;
                self.bind_source_schema(&parameter.pattern, source)?;
            }
            Ok(())
        })
    }
    fn globals(&self) -> Env {
        self.evaluator
            .global_values
            .iter()
            .map(|(name, value)| (name.clone(), self.value_type(value).unwrap_or(Ty::Unknown)))
            .collect()
    }
    fn value_type(&self, value: &StaticValue) -> Result<Ty> {
        match value {
            StaticValue::Callable(StaticCallable::Prepared(prepared)) => {
                let env = prepared
                    .environment
                    .values
                    .iter()
                    .map(|(name, value)| (name.clone(), value_ty(value)))
                    .collect();
                let syntax = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: self.evaluator.functions[&prepared.name].span,
                    kind: TypeKind::Callable {
                        parameters: prepared.signature.parameters.clone(),
                        result: prepared.signature.result.clone().map(Box::new),
                        annotations: vec![],
                    },
                };
                self.ty(&syntax, &env)
            }
            StaticValue::Result(produced) if produced.ty.is_some() => {
                self.ty(produced.ty.as_deref().unwrap(), &Env::new())
            }
            StaticValue::Callable(StaticCallable::View(view)) => {
                let env = view
                    .captured
                    .values
                    .iter()
                    .map(|(name, value)| (name.clone(), value_ty(value)))
                    .collect();
                self.ty(&view.signature, &env)
            }
            StaticValue::Callable(StaticCallable::Named { name, captured }) => {
                let env = self
                    .evaluator
                    .declaration_environment(*captured)?
                    .values
                    .iter()
                    .map(|(name, value)| (name.clone(), value_ty(value)))
                    .collect();
                self.function_ty(name, &env)
            }
            StaticValue::Callable(StaticCallable::Lambda {
                parameters,
                body,
                captured,
                return_type,
            }) => {
                let binder = self.child(None);
                let mut env: Env = captured
                    .values
                    .iter()
                    .map(|(name, value)| (name.clone(), value_ty(value)))
                    .collect();
                let mut inputs = vec![];
                for parameter in parameters {
                    let ty = parameter.ty.as_ref().map_or(
                        Err(Failure::Unsupported(
                            "static callable value needs an input context".into(),
                        )),
                        |ty| self.ty(ty, &env),
                    )?;
                    binder.bind(&parameter.pattern, ty.clone(), &mut env)?;
                    inputs.push(ty);
                }
                let expected = return_type
                    .as_deref()
                    .map(|ty| self.ty(ty, &env))
                    .transpose()?;
                let mut checker = binder.child(Some(expected.clone().unwrap_or(Ty::Infer)));
                checker.return_context = return_type
                    .as_deref()
                    .map(|syntax| checker.context_for_syntax(syntax, &env))
                    .transpose()?;
                let result = checker.callable_result(checker.expr_result_expected(
                    body,
                    &mut env,
                    expected.as_ref(),
                    checker.return_context.as_ref(),
                )?)?;
                Ok(Ty::Callable(
                    inputs,
                    Box::new(result),
                    vec![
                        parameters
                            .iter()
                            .map(application::ParameterSpec::from)
                            .collect(),
                    ],
                ))
            }
            _ => Ok(value_ty(value)),
        }
    }
    fn ty(&self, syntax: &TypeExpr, env: &Env) -> Result<Ty> {
        if let Some(scope) = &self.bound_environment {
            let mut current = (**scope).clone();
            current.values = env.clone();
            self.apply_const_shadows(&mut current)?;
            return self.bound_type(syntax, &current);
        }
        // A closed annotation outside a generic frame can instantiate a pure
        // structural alias before ordinary typing visits its fields. An open
        // lexical type environment must keep its real binder registry instead.
        if !env
            .values()
            .any(|ty| matches!(ty, Ty::TypeParameter | Ty::Constructor(_)))
            && let Some(witness) =
                self.complete_source_syntax(syntax, &bounds::BoundEnvironment::default())?
        {
            return self.ty_seen(&witness.syntax, env, &mut BTreeSet::new());
        }
        let ty = self.ty_seen(syntax, env, &mut BTreeSet::new())?;
        Ok(match &self.bound_environment {
            Some(scope) => scope.canonical_type(ty),
            None => ty,
        })
    }
    fn ty_seen(&self, syntax: &TypeExpr, env: &Env, seen: &mut BTreeSet<String>) -> Result<Ty> {
        Ok(match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                let name = name.strip_prefix("Prelude::").unwrap_or(&name);
                if let Some(identity) =
                    ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(name)
                {
                    if !arguments.is_empty() {
                        return Err(Failure::Diagnostic(
                            "E0340",
                            "intrinsic atomic type has no generic arguments".into(),
                        ));
                    }
                    return Ok(Ty::Intrinsic(identity));
                }
                match name {
                    "bool" => Ty::Bool,
                    "str" => Ty::String,
                    "bytes" => Ty::Bytes,
                    "never" => Ty::Never,
                    "type" => Ty::Meta,
                    "Option" if arguments.len() == 1 => {
                        Ty::Optional(Box::new(self.ty_seen(&arguments[0], env, seen)?))
                    }
                    "Result" if arguments.len() == 2 => Ty::Result(
                        Box::new(self.ty_seen(&arguments[0], env, seen)?),
                        Box::new(self.ty_seen(&arguments[1], env, seen)?),
                    ),
                    name if primitive_type(name) => Ty::Number(name.into()),
                    name if env.get(name) == Some(&Ty::TypeParameter) => Ty::Generic(name.into()),
                    name => {
                        if let Some(declaration) = self.evaluator.declarations.get(name) {
                            if declaration.nominal
                                || declaration.opaque
                                || !declaration.variants.is_empty()
                            {
                                return Err(Failure::Unsupported(
                                    "static nominal/sum signature typing".into(),
                                ));
                            }
                            if let Some(value) = &declaration.value {
                                if !seen.insert(name.into()) {
                                    return Err(Failure::Unsupported(
                                        "recursive static signature shape proof".into(),
                                    ));
                                }
                                let result = self.ty_seen(value, env, seen);
                                seen.remove(name);
                                return result;
                            }
                        }
                        return Err(Failure::Unsupported(format!(
                            "static signature type {name}"
                        )));
                    }
                }
            }
            TypeKind::Optional(inner) => Ty::Optional(Box::new(self.ty_seen(inner, env, seen)?)),
            TypeKind::Computation(expression) if matches!(&expression.kind,ExprKind::Unary { operator,.. } if operator == "typeof") =>
            {
                let ExprKind::Unary { operand, .. } = &expression.kind else {
                    unreachable!()
                };
                let mut checker = self.child(None);
                checker.unevaluated = true;
                return checker.expr(operand, &mut env.clone());
            }
            TypeKind::Array { element, length } => {
                let length = length
                    .as_ref()
                    .map(|length| {
                        let actual = self.expr(length, &mut env.clone())?;
                        require(&actual, &Ty::Number("int".into())).map_err(
                            |failure| match failure {
                                Failure::Diagnostic(_, message) => {
                                    Failure::Diagnostic("E0323", message)
                                }
                                other => other,
                            },
                        )?;
                        let Ty::IntegerConstant(value) = actual else {
                            return Err(Failure::Diagnostic(
                                "E0814",
                                "fixed array length is not a known static int".into(),
                            ));
                        };
                        usize::try_from(value).map_err(|_| {
                            Failure::Diagnostic(
                                "E0815",
                                "fixed array length is negative or exceeds the target range".into(),
                            )
                        })
                    })
                    .transpose()?;
                Ty::Array(Box::new(self.ty_seen(element, env, seen)?), length)
            }
            TypeKind::Tuple(items) => {
                if items.is_empty() {
                    Ty::Unit
                } else {
                    Ty::Tuple(
                        items
                            .iter()
                            .map(|item| self.ty_seen(item, env, seen))
                            .collect::<Result<_>>()?,
                    )
                }
            }
            TypeKind::Map { key, value } => {
                let key = self.ty_seen(key, env, seen)?;
                require_static_key(&key)?;
                Ty::Map(Box::new(key), Box::new(self.ty_seen(value, env, seen)?))
            }
            TypeKind::Record { fields, row } => {
                if row.is_some() {
                    return Err(Failure::Unsupported(
                        "static open-row signature typing".into(),
                    ));
                }
                Ty::Record(
                    fields
                        .iter()
                        .map(|field| {
                            Ok((
                                field.name.clone(),
                                (field.mutable, self.ty_seen(&field.ty, env, seen)?),
                            ))
                        })
                        .collect::<Result<_>>()?,
                )
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                if parameters
                    .iter()
                    .any(|parameter| parameter.mode != ParameterMode::Read)
                {
                    return Err(Failure::Unsupported(
                        "static callback data parameter mode typing proof".into(),
                    ));
                }
                if !annotations.is_empty() {
                    return Err(Failure::Unsupported(
                        "static callback has latent invocation obligations".into(),
                    ));
                }
                Ty::Callable(
                    parameters
                        .iter()
                        .map(|parameter| {
                            parameter.ty.as_ref().map_or(
                                Err(Failure::Unsupported("static callback formal type".into())),
                                |ty| self.ty_seen(ty, env, seen),
                            )
                        })
                        .collect::<Result<_>>()?,
                    Box::new(
                        result
                            .as_ref()
                            .map_or(Ok(Ty::Unit), |result| self.ty_seen(result, env, seen))?,
                    ),
                    vec![
                        parameters
                            .iter()
                            .map(|parameter| application::ParameterSpec {
                                label: application::ParameterSpec::from(parameter).label,
                                default: false,
                            })
                            .collect(),
                    ],
                )
            }
            _ => {
                return Err(Failure::Unsupported(
                    "static computed signature typing".into(),
                ));
            }
        })
    }
    fn constructor_parts(
        &self,
        ty: &Ty,
        path: &[String],
        count: usize,
        parenthesized: bool,
    ) -> Result<Vec<Ty>> {
        let name = path.join("::");
        let tag = name.strip_prefix("Prelude::").unwrap_or(&name);
        let payload = match (ty, tag) {
            (Ty::Optional(_), "None") => {
                if parenthesized {
                    return Err(Failure::Diagnostic(
                        "E0353",
                        "a nullary variant tag cannot have argument parentheses".into(),
                    ));
                }
                if count != 0 {
                    return Err(Failure::Diagnostic(
                        "E0314",
                        "nullary constructor has no payload".into(),
                    ));
                }
                return Ok(vec![]);
            }
            (Ty::Optional(inner), "Some") => inner.as_ref(),
            (Ty::Result(ok, _), "Ok") => ok.as_ref(),
            (Ty::Result(_, error), "Err") => error.as_ref(),
            (Ty::Unknown | Ty::Generic(_), _) => {
                return Err(Failure::Unsupported(
                    "static constructor pattern has an unresolved subject type".into(),
                ));
            }
            _ => {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "constructor test does not belong to the subject type".into(),
                ));
            }
        };
        match count {
            0 if !parenthesized || matches!(payload, Ty::Unit | Ty::Infer) => Ok(vec![]),
            1 => Ok(vec![payload.clone()]),
            _ => {
                if let Ty::Tuple(items) = payload
                    && items.len() == count
                {
                    Ok(items.clone())
                } else {
                    Err(Failure::Diagnostic(
                        "E0314",
                        "constructor test arity differs".into(),
                    ))
                }
            }
        }
    }
    fn bind(&self, pattern: &Pattern, ty: Ty, env: &mut Env) -> Result<()> {
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.schema_bindings.borrow_mut().insert(name.clone(), None);
                self.const_shadows.borrow_mut().insert(name.clone());
                env.insert(name.clone(), ty);
            }
            PatternKind::Wildcard => {}
            PatternKind::Tuple(patterns) => self.bind_sequence(patterns, ty, false, env)?,
            PatternKind::Array(patterns) => self.bind_sequence(patterns, ty, true, env)?,
            PatternKind::Rest(_) => {
                return Err(Failure::Diagnostic(
                    "E0347",
                    "rest requires a directly enclosing sequence".into(),
                ));
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                let Ty::Record(mut types) = ty else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "record pattern requires a record".into(),
                    ));
                };
                for field in fields {
                    let ty = types.remove(&field.name).ok_or_else(|| {
                        Failure::Diagnostic("E0336", "record pattern field missing".into())
                    })?;
                    self.bind(&field.pattern, ty.1, env)?;
                }
                if let Some(rest) = rest_binding {
                    env.insert(rest.clone(), Ty::Record(types));
                }
            }
            PatternKind::Type { ty, .. } => {
                bind_type_pattern(ty, env)?;
                self.type_names(ty, env)?;
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => {
                let types = self.constructor_parts(&ty, path, arguments.len(), *parenthesized)?;
                for (pattern, ty) in arguments.iter().zip(types) {
                    self.bind(pattern, ty, env)?;
                }
            }
            PatternKind::Alternative(patterns) => {
                let mut contract: Option<BTreeMap<String, Ty>> = None;
                for pattern in patterns {
                    let mut branch = env.clone();
                    self.bind(pattern, ty.clone(), &mut branch)?;
                    let mut names = BTreeSet::new();
                    application::binding_names(pattern, &mut names);
                    let bindings: BTreeMap<_, _> = names
                        .into_iter()
                        .filter_map(|name| branch.get(&name).cloned().map(|ty| (name, ty)))
                        .collect();
                    if let Some(expected) = &mut contract {
                        if !expected.keys().eq(bindings.keys()) {
                            return Err(Failure::Diagnostic(
                                "E0346",
                                "pattern alternatives have incompatible binding contracts".into(),
                            ));
                        }
                        for (name, ty) in expected {
                            *ty = join_types(ty, &bindings[name]).map_err(
                                |failure| match failure {
                                    Failure::Diagnostic(_, why) => {
                                        Failure::Diagnostic("E0346", why)
                                    }
                                    other => other,
                                },
                            )?;
                        }
                    } else {
                        contract = Some(bindings);
                    }
                }
                if let Some(contract) = contract {
                    env.extend(contract);
                }
            }
            PatternKind::Literal(_) | PatternKind::Value(_) => {
                self.value_test(pattern, &ty, env)?
            }
            _ => return Err(Failure::Unsupported("static binding mode typing".into())),
        }
        Ok(())
    }
    /// Value tests read their leaves; they never introduce pattern bindings.
    /// Check every leaf even when a known tag or earlier component skips it.
    fn value_test(&self, pattern: &Pattern, actual: &Ty, env: &mut Env) -> Result<()> {
        match &pattern.kind {
            PatternKind::Wildcard => Ok(()),
            PatternKind::Value(value) => {
                let expected = self.expr(value, env)?;
                join_types(actual, &expected)?;
                if contains_callable_type(actual) || contains_callable_type(&expected) {
                    return Err(Failure::Diagnostic(
                        "E0305",
                        "callable values do not admit equality".into(),
                    ));
                }
                Ok(())
            }
            PatternKind::Literal(literal) => self.value_test(
                &Pattern {
                    hir_id: None,
                    kind: PatternKind::Value(Box::new(Expr {
                        hir_id: None,
                        kind: ExprKind::Literal(literal.clone()),
                        span: pattern.span,
                    })),
                    span: pattern.span,
                },
                actual,
                env,
            ),
            PatternKind::Tuple(patterns) => {
                let Ty::Tuple(items) = actual else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "tuple test requires a tuple".into(),
                    ));
                };
                if patterns.len() != items.len() {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "tuple test arity differs".into(),
                    ));
                }
                for (pattern, item) in patterns.iter().zip(items) {
                    self.value_test(pattern, item, env)?;
                }
                Ok(())
            }
            PatternKind::Record { ty, fields, .. } => {
                if let Some(ty) = ty {
                    require(actual, &self.ty(ty, env)?)?;
                }
                let Ty::Record(items) = actual else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "record test requires a record".into(),
                    ));
                };
                for field in fields {
                    let item = items.get(&field.name).ok_or_else(|| {
                        Failure::Diagnostic("E0336", "record test field missing".into())
                    })?;
                    self.value_test(&field.pattern, &item.1, env)?;
                }
                Ok(())
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => {
                let types =
                    self.constructor_parts(actual, path, arguments.len(), *parenthesized)?;
                for (pattern, ty) in arguments.iter().zip(types) {
                    self.value_test(pattern, &ty, env)?;
                }
                Ok(())
            }
            PatternKind::Alternative(patterns) => {
                for pattern in patterns {
                    self.value_test(pattern, actual, env)?;
                }
                Ok(())
            }
            _ => Err(Failure::Unsupported(
                "static value test form has no complete typing proof".into(),
            )),
        }
    }
    fn block_expected(&self, block: &Block, env: &mut Env, expected: Option<&Ty>) -> Result<Ty> {
        self.block_result_expected(block, env, expected, None)
    }
    fn block_result_expected(
        &self,
        block: &Block,
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        let entry_reachable = self.reachable.get();
        let entry_schemas = self.schema_bindings.borrow().clone();
        let entry_const_shadows = self.const_shadows.borrow().clone();
        let result =
            self.block_expected_inner(block, env, expected, result_context, entry_reachable);
        *self.schema_bindings.borrow_mut() = entry_schemas;
        *self.const_shadows.borrow_mut() = entry_const_shadows;
        self.reachable.set(entry_reachable);
        result
    }
    fn block_expected_inner(
        &self,
        block: &Block,
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
        entry_reachable: bool,
    ) -> Result<Ty> {
        let mut result = Ty::Unit;
        let mut diverged = false;
        for (index, statement) in block.statements.iter().enumerate() {
            self.reachable.set(entry_reachable && !diverged);
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    if binding.mode != BindingMode::Let {
                        return Err(Failure::Unsupported("static mutable local typing".into()));
                    }
                    let initializer =
                        record_contexts::expression(&binding.value, binding.ty.as_ref());
                    let binding_type =
                        binding.ty.as_ref().map(|ty| self.ty(ty, env)).transpose()?;
                    let binding_context = binding
                        .ty
                        .as_ref()
                        .map(|ty| self.context_for_syntax(ty, env))
                        .transpose()?;
                    let mut actual = self.expr_result_expected(
                        &initializer,
                        env,
                        binding_type.as_ref(),
                        binding_context.as_ref(),
                    )?;
                    if let Some(fallback) = &binding.fallback {
                        require(&self.expr(fallback, &mut env.clone())?, &Ty::Never)?;
                    }
                    diverged |= actual == Ty::Never;
                    if let Some(expected) = &binding.ty {
                        let declared = self.ty(expected, env)?;
                        require(&actual, &declared)?;
                        actual = if let Some(scope) = &self.bound_environment {
                            self.receive_type_interfaces(actual, expected, &declared, scope)?
                        } else {
                            with_interfaces(actual, &declared)
                        };
                    }
                    let mut scope = self
                        .bound_environment
                        .as_deref()
                        .cloned()
                        .unwrap_or_default();
                    scope.values = env.clone();
                    self.apply_const_shadows(&mut scope)?;
                    let schema = if let Some(syntax) = &binding.ty {
                        self.complete_source_syntax(syntax, &scope)?
                    } else {
                        self.expression_source_schema_expected(
                            &initializer,
                            &actual,
                            env,
                            &scope,
                            binding_context.as_ref(),
                            0,
                        )?
                    };
                    self.bind(&binding.pattern, actual, env)?;
                    self.bind_source_schema(&binding.pattern, schema)?;
                    result = Ty::Unit;
                }
                StmtKind::Expr {
                    expression,
                    terminated,
                } => {
                    result = self.expr_result_expected(
                        expression,
                        env,
                        if index + 1 == block.statements.len() && !terminated {
                            expected
                        } else {
                            None
                        },
                        if index + 1 == block.statements.len() && !terminated {
                            result_context
                        } else {
                            None
                        },
                    )?;
                    diverged |= result == Ty::Never;
                    if *terminated && result != Ty::Never {
                        result = Ty::Unit;
                    }
                }
                _ => {
                    if !matches!(statement.kind, StmtKind::Function(_) | StmtKind::Type(_)) {
                        return Err(Failure::Unsupported("static statement typing".into()));
                    }
                }
            }
        }
        Ok(if diverged { Ty::Never } else { result })
    }
    fn expr(&self, expression: &Expr, env: &mut Env) -> Result<Ty> {
        self.expr_expected(expression, env, None)
    }
    fn expr_expected(&self, expression: &Expr, env: &mut Env, expected: Option<&Ty>) -> Result<Ty> {
        self.expr_result_expected(expression, env, expected, None)
    }
    pub(super) fn expr_result_expected(
        &self,
        expression: &Expr,
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        match &expression.kind {
            ExprKind::Literal(literal) => Ok(match literal {
                Literal::Unit => Ty::Unit,
                Literal::Bool(_) => Ty::Bool,
                Literal::String(_) | Literal::RawString(_) => Ty::String,
                Literal::Bytes(_) => Ty::Bytes,
                Literal::Integer(text) => value_ty(&numeric_contexts::selected(
                    text,
                    false,
                    false,
                    expected.and_then(numeric_type),
                    self.evaluator.layout,
                )?),
                Literal::Float(text) => value_ty(&numeric_contexts::selected(
                    text,
                    true,
                    false,
                    expected.and_then(numeric_type),
                    self.evaluator.layout,
                )?),
            }),
            ExprKind::TypeValue(ty) => {
                self.type_names(ty, env)?;
                Ok(Ty::Meta)
            }
            ExprKind::Name(name) => {
                if let Some(ty) = env.get(name) {
                    if let Ty::ForbiddenDefault(name) = ty {
                        return Err(Failure::Diagnostic(
                            "E0408",
                            format!("default refers to itself or later parameter {name}"),
                        ));
                    }
                    if matches!(ty, Ty::TypeParameter | Ty::Constructor(_)) {
                        return Err(Failure::Diagnostic(
                            "E0319",
                            "generic type names require type<T> quotation".into(),
                        ));
                    }
                    return Ok(ty.clone());
                }
                if let Some(value) = self.evaluator.numeric_constant(name) {
                    return Ok(value_ty(&value));
                }
                if self.evaluator.functions.contains_key(name) {
                    return self.function_ty(name, env);
                }
                if self.evaluator.declarations.contains_key(name) {
                    return Err(Failure::Unsupported(
                        "static declared constructor value typing proof".into(),
                    ));
                }
                if name.strip_prefix("Prelude::").unwrap_or(name) == "None" {
                    return Ok(Ty::Optional(Box::new(Ty::Infer)));
                }
                Err(Failure::Unsupported(format!("static lexical name {name}")))
            }
            ExprKind::Path(path) => self.expr(
                &Expr {
                    hir_id: None,
                    kind: ExprKind::Name(path.join("::")),
                    span: expression.span,
                },
                env,
            ),
            ExprKind::Generic { base, arguments } => {
                let name = expression_name(base)
                    .ok_or_else(|| Failure::Unsupported("computed static generic callee".into()))?;
                if let Some(TypeDeclaration {
                    value:
                        Some(TypeExpr {
                            kind: TypeKind::TypeFunction { parameters, .. },
                            ..
                        }),
                    ..
                }) = self.evaluator.declarations.get(&name)
                {
                    let _ = parameters;
                    self.type_names(
                        &TypeExpr {
                            hir_id: None,
                            text: name.clone(),
                            kind: TypeKind::Name {
                                path: name.split("::").map(str::to_owned).collect(),
                                arguments: arguments.clone(),
                            },
                            span: expression.span,
                        },
                        env,
                    )?;
                    Ok(Ty::Meta)
                } else if matches!(env.get(&name), Some(Ty::Constructor(_))) {
                    self.type_names(
                        &TypeExpr {
                            hir_id: None,
                            text: name.clone(),
                            kind: TypeKind::Name {
                                path: vec![name],
                                arguments: arguments.clone(),
                            },
                            span: expression.span,
                        },
                        env,
                    )?;
                    Ok(Ty::Meta)
                } else {
                    Err(Failure::Unsupported(
                        "static generic callable typing".into(),
                    ))
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation {
                        expression, format, ..
                    } = part
                    {
                        let ty = self.expr(expression, env)?;
                        let format = format.as_deref().unwrap_or("");
                        use ril_text_format::{FormatSpec, Kind};
                        let spec = FormatSpec::parse(format, self.evaluator.layout.pointer_bits)
                            .map_err(super::formatting::failure)?;
                        let kind = match &ty {
                            Ty::String => Kind::String,
                            Ty::Bool => Kind::Bool,
                            Ty::Number(name) if matches!(name.as_str(), "f32" | "f64") => {
                                Kind::Float
                            }
                            Ty::Number(_) | Ty::IntegerConstant(_) => Kind::Integer,
                            _ => {
                                return Err(super::formatting::failure(
                                    ril_text_format::Error::Incompatible,
                                ));
                            }
                        };
                        spec.validate(kind).map_err(super::formatting::failure)?;
                    }
                }
                Ok(Ty::String)
            }
            ExprKind::Tuple(items) => Ok(Ty::Tuple(
                items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| {
                        let child_context = self.child_result_context(
                            result_context,
                            applications::ResultProjection::Tuple(index),
                        )?;
                        self.expr_result_expected(
                            item,
                            env,
                            expected.and_then(|ty| {
                                if let Ty::Tuple(items) = ty {
                                    items.get(index)
                                } else {
                                    None
                                }
                            }),
                            child_context.as_ref(),
                        )
                    })
                    .collect::<Result<_>>()?,
            )),
            ExprKind::Array(items) => {
                let source_context = self.child_result_context(
                    result_context,
                    applications::ResultProjection::ArrayElement,
                )?;
                let item_context = expected.and_then(|ty| {
                    if let Ty::Array(item, _) = ty {
                        Some(item.as_ref())
                    } else {
                        None
                    }
                });
                let mut ty = Ty::Infer;
                for item in items {
                    let next = self.expr_result_expected(
                        item,
                        env,
                        item_context,
                        source_context.as_ref(),
                    )?;
                    if ty == Ty::Infer {
                        ty = next;
                    } else {
                        ty = join_types(&next, &ty)?;
                    }
                }
                Ok(Ty::Array(Box::new(erase_constants(ty)), Some(items.len())))
            }
            ExprKind::Map(entries) => {
                let key_source = self
                    .child_result_context(result_context, applications::ResultProjection::MapKey)?;
                let value_source = self.child_result_context(
                    result_context,
                    applications::ResultProjection::MapValue,
                )?;
                let (key_context, value_context) = expected
                    .and_then(|ty| {
                        if let Ty::Map(key, value) = ty {
                            Some((Some(key.as_ref()), Some(value.as_ref())))
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default();
                let mut key = Ty::Infer;
                let mut value = Ty::Infer;
                for (k, v) in entries {
                    let next_key =
                        self.expr_result_expected(k, env, key_context, key_source.as_ref())?;
                    let next_value =
                        self.expr_result_expected(v, env, value_context, value_source.as_ref())?;
                    if key == Ty::Infer {
                        key = next_key;
                    } else {
                        key = join_types(&next_key, &key)?;
                    }
                    if value == Ty::Infer {
                        value = next_value;
                    } else {
                        value = join_types(&next_value, &value)?;
                    }
                }
                require_static_key(&key)?;
                Ok(Ty::Map(
                    Box::new(erase_constants(key)),
                    Box::new(erase_constants(value)),
                ))
            }
            ExprKind::Record { ty, members, .. } => {
                let declared = ty.as_ref().map(|syntax| self.ty(syntax, env)).transpose()?;
                let declared_source = ty
                    .as_ref()
                    .map(|syntax| self.context_for_syntax(syntax, env))
                    .transpose()?;
                let source_context = declared_source.as_ref().or(result_context);
                let record_context = declared.as_ref().or(expected);
                let mut fields = BTreeMap::new();
                let mut overrides = BTreeMap::new();
                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            let field_context = record_context.and_then(|ty| {
                                if let Ty::Record(fields) = ty {
                                    fields.get(&field.name).map(|(_, ty)| ty)
                                } else {
                                    None
                                }
                            });
                            overrides.insert(
                                field.name.clone(),
                                (
                                    false,
                                    self.expr_result_expected(
                                        &field.value,
                                        env,
                                        field_context,
                                        self.child_result_context(
                                            source_context,
                                            applications::ResultProjection::Record(
                                                field.name.clone(),
                                            ),
                                        )?
                                        .as_ref(),
                                    )?,
                                ),
                            );
                        }
                        RecordMember::Spread(value) => {
                            let Ty::Record(values) = self.expr(value, env)? else {
                                return Err(Failure::Diagnostic(
                                    "E0301",
                                    "static record spread requires record data".into(),
                                ));
                            };
                            fields.extend(values);
                        }
                    }
                }
                fields.extend(overrides);
                if let Some(syntax) = ty {
                    self.type_names(syntax, env)?;
                    let expected = self.ty(syntax, env)?;
                    if let Ty::Record(expected_fields) = &expected
                        && fields.keys().eq(expected_fields.keys())
                    {
                        // These are new slots. Check each initializer as a
                        // value, then assign the declared slot type. Later
                        // transfers of mutable slots are invariant.
                        for (name, (_, actual)) in &fields {
                            require(actual, &expected_fields[name].1)?;
                        }
                        return if let Some(scope) = &self.bound_environment {
                            self.receive_type_interfaces(
                                Ty::Record(fields),
                                syntax,
                                &expected,
                                scope,
                            )
                        } else {
                            Ok(expected)
                        };
                    }
                    require(&Ty::Record(fields), &expected)?;
                    Ok(expected)
                } else {
                    construction_contexts::receive_fresh_record_modes(&mut fields, record_context);
                    Ok(Ty::Record(fields))
                }
            }
            ExprKind::Unary { operator, operand } => {
                if operator == "-"
                    && let ExprKind::Literal(literal) = &operand.kind
                {
                    match literal {
                        Literal::Integer(text) => {
                            return Ok(value_ty(&numeric_contexts::selected(
                                text,
                                false,
                                true,
                                expected.and_then(numeric_type),
                                self.evaluator.layout,
                            )?));
                        }
                        Literal::Float(text) => {
                            return Ok(value_ty(&numeric_contexts::selected(
                                text,
                                true,
                                true,
                                expected.and_then(numeric_type),
                                self.evaluator.layout,
                            )?));
                        }
                        _ => {}
                    }
                }
                let ty = self.expr_expected(
                    operand,
                    env,
                    if operator == "-" { expected } else { None },
                )?;
                match operator.as_str() {
                    "!" => {
                        require(&ty, &Ty::Bool)?;
                        Ok(Ty::Bool)
                    }
                    "-" | "~" => {
                        if matches!(ty, Ty::Number(_) | Ty::IntegerConstant(_)) {
                            Ok(match ty {
                                Ty::IntegerConstant(value) => {
                                    let next = if operator == "-" {
                                        value.checked_neg()
                                    } else {
                                        Some(!value)
                                    };
                                    int_fact(next, self.evaluator.layout)
                                }
                                other => other,
                            })
                        } else {
                            Err(Failure::Diagnostic(
                                "E0301",
                                "numeric unary operand required".into(),
                            ))
                        }
                    }
                    _ => Err(Failure::Unsupported("static unary typing".into())),
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "??" {
                    return self.coalescing_type(left, right, env, expected, result_context);
                }
                let numeric_context = if matches!(operator.as_str(), "&&" | "||") {
                    None
                } else {
                    expected
                        .filter(|ty| numeric_type(ty).is_some())
                        .cloned()
                        .or_else(|| self.rigid_numeric_peer(left, env))
                        .or_else(|| self.rigid_numeric_peer(right, env))
                };
                let a = self.expr_expected(left, env, numeric_context.as_ref())?;
                let left_truth = loops::known_bool(left);
                let skipped = matches!(
                    (operator.as_str(), left_truth),
                    ("&&", Some(false)) | ("||", Some(true))
                );
                let reachable = self.reachable.get() && a != Ty::Never && !skipped;
                let b = self.with_reachability(reachable, || {
                    self.expr_expected(
                        right,
                        env,
                        if matches!(operator.as_str(), "<<" | ">>") {
                            None
                        } else {
                            numeric_context.as_ref()
                        },
                    )
                })?;
                if matches!(operator.as_str(), "&&" | "||") {
                    require(&a, &Ty::Bool)?;
                    require(&b, &Ty::Bool)?;
                    return Ok(
                        if a == Ty::Never || (b == Ty::Never && !skipped && left_truth.is_some()) {
                            Ty::Never
                        } else {
                            Ty::Bool
                        },
                    );
                }
                if a == Ty::Never || b == Ty::Never {
                    return Ok(Ty::Never);
                }
                if matches!(operator.as_str(), "<<" | ">>") {
                    let integer = |ty: &Ty| {
                        matches!(ty, Ty::IntegerConstant(_))
                            || matches!(ty, Ty::Number(name) if matches!(name.as_str(), "int" | "bigint" | "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64"))
                    };
                    if !integer(&a) || !integer(&b) {
                        return Err(Failure::Diagnostic(
                            "E0327",
                            "shift operands must be integers".into(),
                        ));
                    }
                    return Ok(erase_constants(a));
                }
                let _common = join_types(&a, &b)?;
                if matches!(operator.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") {
                    if contains_callable_type(&a) {
                        return Err(Failure::Diagnostic(
                            "E0305",
                            "callable values do not admit equality".into(),
                        ));
                    }
                    if !matches!(operator.as_str(), "==" | "!=")
                        && !matches!(a, Ty::Number(_) | Ty::IntegerConstant(_) | Ty::String)
                    {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "ordered scalar operands required".into(),
                        ));
                    }
                    return Ok(Ty::Bool);
                }
                if matches!(a, Ty::Number(_) | Ty::IntegerConstant(_)) {
                    Ok(
                        if let (Ty::IntegerConstant(left), Ty::IntegerConstant(right)) = (&a, &b) {
                            let value = match operator.as_str() {
                                "+" => left.checked_add(*right),
                                "-" => left.checked_sub(*right),
                                "*" => left.checked_mul(*right),
                                "/" => left.checked_div(*right),
                                "%" => left.checked_rem(*right),
                                "&" => Some(left & right),
                                "|" => Some(left | right),
                                "^" => Some(left ^ right),
                                _ => None,
                            };
                            int_fact(value, self.evaluator.layout)
                        } else {
                            erase_constants(a)
                        },
                    )
                } else {
                    Err(Failure::Diagnostic(
                        "E0301",
                        "static arithmetic requires numeric operands".into(),
                    ))
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_ty = self.expr(condition, env)?;
                require(&condition_ty, &Ty::Bool)?;
                let entry_reachable = self.reachable.get();
                let condition_value = loops::known_bool(condition);
                let a = self.with_reachability(
                    entry_reachable && condition_ty != Ty::Never && condition_value != Some(false),
                    || {
                        self.expr_result_expected(
                            then_branch,
                            &mut env.clone(),
                            expected,
                            result_context,
                        )
                    },
                )?;
                let b = else_branch.as_ref().map_or(Ok(Ty::Unit), |branch| {
                    self.with_reachability(
                        entry_reachable
                            && condition_ty != Ty::Never
                            && condition_value != Some(true),
                        || {
                            self.expr_result_expected(
                                branch,
                                &mut env.clone(),
                                expected,
                                result_context,
                            )
                        },
                    )
                })?;
                if condition_ty == Ty::Never {
                    Ok(Ty::Never)
                } else {
                    join_types(&a, &b)
                }
            }
            ExprKind::Block(block) => {
                self.block_result_expected(block, &mut env.clone(), expected, result_context)
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                let actual = self.expr(value, env)?;
                let default_scope = bounds::BoundEnvironment::default();
                let schema = self.expression_source_schema(
                    value,
                    &actual,
                    env,
                    self.bound_environment.as_deref().unwrap_or(&default_scope),
                    0,
                )?;
                let a = self.with_const_shadow_scope(|| {
                    let mut child = env.clone();
                    self.bind(pattern, actual.clone(), &mut child)?;
                    self.bind_source_schema(pattern, schema)?;
                    self.with_reachability(self.reachable.get() && actual != Ty::Never, || {
                        self.expr_result_expected(then_branch, &mut child, expected, result_context)
                    })
                })?;
                let b = else_branch.as_ref().map_or(Ok(Ty::Unit), |branch| {
                    self.expr_result_expected(branch, &mut env.clone(), expected, result_context)
                })?;
                if actual == Ty::Never {
                    Ok(Ty::Never)
                } else {
                    join_types(&a, &b).map_err(|failure| match failure {
                        Failure::Diagnostic("E0301", why) => Failure::Diagnostic("E0351", why),
                        other => other,
                    })
                }
            }
            ExprKind::Loop(body) => self.loop_type(body, env, expected, result_context),
            ExprKind::While { condition, body } => self.while_type(condition, body, env),
            ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => self.while_let_type(pattern, value, body, env),
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => self.for_type(iterable, pattern, body, env),
            ExprKind::Control {
                operation: operation @ (ControlOperation::Next | ControlOperation::Last),
                value,
            } => self.loop_transfer_type(*operation, value.as_deref(), env),
            ExprKind::Is { value, pattern } => {
                let actual = self.expr(value, env)?;
                self.value_test(pattern, &actual, env)?;
                Ok(Ty::Bool)
            }
            ExprKind::Match { value, arms, .. } => {
                let value = self.expr(value, env)?;
                let mut result = Ty::Never;
                for arm in arms {
                    let next = self.with_const_shadow_scope(|| {
                        let mut child = env.clone();
                        self.bind(&arm.pattern, value.clone(), &mut child)?;
                        if let Some(guard) = &arm.guard {
                            require(&self.expr(guard, &mut child)?, &Ty::Bool)?;
                        }
                        self.expr_result_expected(&arm.body, &mut child, expected, result_context)
                    })?;
                    if result == Ty::Never {
                        result = next;
                    } else {
                        result = join_types(&next, &result)?;
                    }
                }
                Ok(result)
            }
            ExprKind::KeyOf(ty) => {
                self.type_names(ty, env)?;
                Ok(Ty::Array(
                    Box::new(if matches!(ty.kind, TypeKind::Tuple(_)) {
                        Ty::Number("int".into())
                    } else {
                        Ty::String
                    }),
                    None,
                ))
            }
            ExprKind::Call { callee, arguments } => {
                self.call(callee, arguments, env, expected, result_context)
            }
            ExprKind::Field { base, field, safe } => {
                let receiver = self.expr(base, env)?;
                let receiver = if *safe {
                    if let Ty::Optional(inner) = receiver {
                        *inner
                    } else {
                        return Err(Failure::Diagnostic(
                            "E0715",
                            "safe field projection requires an optional receiver".into(),
                        ));
                    }
                } else {
                    receiver
                };
                let projected = match receiver {
                    Ty::Record(fields) => {
                        fields.get(field).map(|(_, ty)| ty.clone()).ok_or_else(|| {
                            Failure::Diagnostic("E0336", "static record field absent".into())
                        })
                    }
                    Ty::Tuple(items) => field
                        .parse::<usize>()
                        .ok()
                        .and_then(|index| items.get(index).cloned())
                        .ok_or_else(|| {
                            Failure::Diagnostic("E0312", "static tuple index invalid".into())
                        }),
                    Ty::Array(..) | Ty::Map(..) => Err(Failure::Diagnostic(
                        "E0337",
                        "collections expose no product fields".into(),
                    )),
                    Ty::Optional(_) => Err(Failure::Diagnostic(
                        "E0310",
                        "optional field projection requires a Some proof".into(),
                    )),
                    generic @ Ty::Generic(_) if self.bound_environment.is_some() => self
                        .bound_projection(
                            &generic,
                            field,
                            self.bound_environment.as_ref().unwrap(),
                        ),
                    _ => Err(Failure::Unsupported(
                        "static projected signature typing".into(),
                    )),
                }?;
                Ok(if *safe && !matches!(projected, Ty::Optional(_)) {
                    Ty::Optional(Box::new(projected))
                } else {
                    projected
                })
            }
            ExprKind::Index { base, index, safe } => {
                let base = self.expr(base, env)?;
                match base {
                    Ty::Array(element, _) => {
                        require(&self.expr(index, env)?, &Ty::Number("int".into()))?;
                        Ok(if *safe {
                            Ty::Optional(element)
                        } else {
                            *element
                        })
                    }
                    Ty::Map(key, value) => {
                        let actual = self.expr_expected(index, env, Some(&key))?;
                        require(&actual, &key)?;
                        Ok(Ty::Optional(value))
                    }
                    _ => Err(Failure::Unsupported("static index signature typing".into())),
                }
            }
            ExprKind::Control {
                operation: ControlOperation::Return,
                value,
            } => {
                let actual = value.as_ref().map_or(Ok(Ty::Unit), |value| {
                    self.expr_result_expected(
                        value,
                        env,
                        self.return_type.as_ref(),
                        self.return_context.as_ref(),
                    )
                })?;
                let Some(expected) = &self.return_type else {
                    return Err(Failure::Unsupported(
                        "return has no enclosing static callable".into(),
                    ));
                };
                if contains_meta_type(&actual) && *expected != Ty::Meta {
                    return Err(Failure::Diagnostic(
                        "E0812",
                        "meta functions cannot return type values".into(),
                    ));
                }
                require(&actual, expected)?;
                self.returns.borrow_mut().push(actual);
                Ok(Ty::Never)
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } => {
                let binder = self.child(None);
                if !annotations.is_empty() {
                    return Err(Failure::Unsupported(
                        "static lambda invocation obligations".into(),
                    ));
                }
                let mut child = env.clone();
                let inputs = parameters
                    .iter()
                    .map(|parameter| {
                        parameter.ty.as_ref().map_or(
                            Err(Failure::Unsupported(
                                "uncontextualized static lambda parameter".into(),
                            )),
                            |ty| self.ty(ty, env),
                        )
                    })
                    .collect::<Result<Vec<_>>>()?;
                for (parameter, ty) in parameters.iter().zip(&inputs) {
                    binder.bind(&parameter.pattern, ty.clone(), &mut child)?;
                }
                let expected = return_type
                    .as_ref()
                    .map_or(Ok(Ty::Infer), |expected| self.ty(expected, env))?;
                let mut checker = binder.child(Some(expected.clone()));
                checker.return_context = return_type
                    .as_ref()
                    .map(|syntax| checker.context_for_syntax(syntax, env))
                    .transpose()?;
                checker.verify_defaults(parameters, env)?;
                let actual = checker.callable_result(checker.expr_result_expected(
                    body,
                    &mut child,
                    Some(&expected),
                    checker.return_context.as_ref(),
                )?)?;
                if let Some(expected) = return_type {
                    require(&actual, &self.ty(expected, env)?)?;
                }
                Ok(Ty::Callable(
                    inputs,
                    Box::new(actual),
                    vec![
                        parameters
                            .iter()
                            .map(application::ParameterSpec::from)
                            .collect(),
                    ],
                ))
            }
            _ => Err(Failure::Unsupported(
                "ordinary static expression typing proof".into(),
            )),
        }
    }
    fn function_ty(&self, name: &str, env: &Env) -> Result<Ty> {
        let function = &self.evaluator.functions[name];
        if !function.is_meta && !self.unevaluated {
            return Err(Failure::Diagnostic(
                "E0810",
                "ordinary callable used in static family".into(),
            ));
        }
        if self.unevaluated
            && (function
                .parameters
                .iter()
                .any(|parameter| parameter.mode != ParameterMode::Read)
                || !function.annotations.is_empty())
        {
            return Err(Failure::Unsupported(
                "unevaluated callable access and writable parameter proof".into(),
            ));
        }
        // A named callable's signature belongs to its definition, including
        // genuine generic IDs. Merely adding TypeParameter spellings to the
        // caller's value environment leaves alias arguments without identities.
        let captured = self
            .function_contexts
            .get(name)
            .cloned()
            .unwrap_or_else(|| bounds::BoundEnvironment::captured(env.clone()));
        let scope = self.function_generic_environment(function, &captured)?;
        let mut checker = self.child(None);
        checker.bound_environment = Some(std::sync::Arc::new(scope.clone()));
        checker.const_shadows.borrow_mut().clear();
        checker.schema_bindings.borrow_mut().clear();
        checker
            .schema_bindings
            .borrow_mut()
            .extend(scope.values.keys().map(|name| (name.clone(), None)));
        Ok(Ty::Callable(
            function
                .parameters
                .iter()
                .map(|parameter| {
                    parameter.ty.as_ref().map_or(
                        Err(Failure::Unsupported("static formal inference".into())),
                        |ty| checker.bound_type(ty, &scope),
                    )
                })
                .collect::<Result<_>>()?,
            Box::new(
                function
                    .return_type
                    .as_ref()
                    .map_or(Ok(Ty::Unit), |ty| checker.bound_type(ty, &scope))?,
            ),
            vec![
                function
                    .parameters
                    .iter()
                    .map(application::ParameterSpec::from)
                    .collect(),
            ],
        ))
    }
    fn call(
        &self,
        callee: &Expr,
        arguments: &[Argument],
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        if arguments
            .iter()
            .any(|argument| argument.mode != ParameterMode::Read)
        {
            if self.unevaluated {
                return Err(Failure::Unsupported(
                    "unevaluated mutable argument permission proof".into(),
                ));
            }
            return Err(Failure::Diagnostic(
                "E0810",
                "static call cannot acquire ordinary write authority".into(),
            ));
        }
        let name = expression_name(callee).unwrap_or_default();
        if let Some((name, explicit)) = application_sources::named_target(callee)
            && let Some(function) = self.evaluator.functions.get(&name)
        {
            return self.named_application(
                function,
                explicit,
                arguments,
                env,
                expected,
                result_context,
            );
        }
        let normalized = name.strip_prefix("Prelude::").unwrap_or(&name);
        if self.evaluator.declarations.contains_key(&name) {
            return Err(Failure::Unsupported(
                "static declared constructor invocation typing proof".into(),
            ));
        }
        if self.evaluator.functions.contains_key(&name)
            || env.contains_key(&name)
            || expression_name(callee).is_none()
        {
            let callable = self.expr(callee, env)?;
            if callable == Ty::Never {
                // The callee expression can return from this callable. Its
                // unreachable arguments still undergo ordinary static checks.
                for argument in arguments {
                    self.expr(&argument.value, env)?;
                }
                return Ok(Ty::Never);
            }
            let Ty::Callable(parameters, result, signatures) = callable else {
                return Err(Failure::Diagnostic(
                    "E0338",
                    "static callee is not callable".into(),
                ));
            };
            let mut inferred = BTreeMap::new();
            if signatures.is_empty() {
                return Err(Failure::Unsupported(
                    "static application has no callable interface witness".into(),
                ));
            }
            if expected.is_some_and(|ty| numeric_type(ty).is_some())
                && contains_generic_type(&result)
                && arguments
                    .iter()
                    .any(|argument| self.rigid_numeric_peer(&argument.value, env).is_none())
            {
                return Err(Failure::Unsupported(
                    "static generic result context requires complete application preparation"
                        .into(),
                ));
            }
            let plans = signatures
                .iter()
                .map(|signature| {
                    application::StaticApplicationPlan::new(
                        signature,
                        arguments.iter().map(|argument| argument.label.clone()),
                    )
                })
                .collect::<Result<Vec<_>>>()?;
            let mut contexts = vec![None; arguments.len()];
            for plan in &plans {
                for (parameter, slot) in parameters.iter().zip(&plan.slots) {
                    if let application::ArgumentSlot::Explicit(index) = slot {
                        if let Some(prior) = contexts[*index] {
                            require(parameter, prior)?;
                        } else {
                            contexts[*index] = Some(parameter);
                        }
                    }
                }
            }
            let actual = arguments
                .iter()
                .zip(contexts)
                .map(|(argument, expected)| self.expr_expected(&argument.value, env, expected))
                .collect::<Result<Vec<_>>>()?;
            for plan in plans {
                for (parameter, slot) in parameters.iter().zip(plan.slots) {
                    if let application::ArgumentSlot::Explicit(index) = slot {
                        unify(parameter, &actual[index], &mut inferred)?;
                    }
                    // An omitted default already has its declaration-wide
                    // proof at this formal type. It cannot invent an otherwise
                    // undetermined generic argument from a caller's names.
                }
            }
            return Ok(if actual.contains(&Ty::Never) {
                Ty::Never
            } else {
                substitute(*result, &inferred)
            });
        }
        if arguments.iter().any(|argument| argument.label.is_some()) {
            return Err(Failure::Unsupported(
                "static builtin labelled application requires its listed signature".into(),
            ));
        }
        if normalized == "assert" {
            if arguments.is_empty() || arguments.len() > 2 {
                return Err(Failure::Diagnostic(
                    "E0314",
                    "assert takes a condition and optional message".into(),
                ));
            }
            let Some(argument) = arguments.first() else {
                return Err(Failure::Diagnostic(
                    "E0314",
                    "assert needs a condition".into(),
                ));
            };
            require(&self.expr(&argument.value, env)?, &Ty::Bool)?;
            if let Some(message) = arguments.get(1) {
                require(&self.expr(&message.value, env)?, &Ty::String)?;
            }
            return Ok(Ty::Unit);
        }
        if normalized == "byte_size" {
            if arguments.len() != 1 {
                return Err(Failure::Diagnostic(
                    "E0314",
                    "byte_size needs one type value".into(),
                ));
            }
            require(&self.expr(&arguments[0].value, env)?, &Ty::Meta)?;
            return Ok(Ty::Number("int".into()));
        }
        if normalized == "len" {
            if arguments.len() != 1 {
                return Err(Failure::Diagnostic("E0314", "len needs one value".into()));
            }
            let actual = self.expr(&arguments[0].value, env)?;
            if !matches!(actual, Ty::String | Ty::Bytes | Ty::Array(..) | Ty::Map(..)) {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "len requires a collection".into(),
                ));
            }
            return Ok(if let Ty::Array(_, Some(length)) = actual {
                Ty::IntegerConstant(length as i128)
            } else {
                Ty::Number("int".into())
            });
        }
        if matches!(normalized, "Some" | "Ok" | "Err") {
            let payload_source = self.child_result_context(
                result_context,
                match normalized {
                    "Some" => applications::ResultProjection::OptionalPayload,
                    "Ok" => applications::ResultProjection::ResultOk,
                    _ => applications::ResultProjection::ResultError,
                },
            )?;
            let payload_context = expected.and_then(|ty| match (normalized, ty) {
                ("Some", Ty::Optional(inner)) => Some(inner.as_ref()),
                ("Ok", Ty::Result(ok, _)) => Some(ok.as_ref()),
                ("Err", Ty::Result(_, error)) => Some(error.as_ref()),
                _ => None,
            });
            let payload = match arguments {
                [] => Ty::Unit,
                [argument] => self.expr_result_expected(
                    &argument.value,
                    env,
                    payload_context,
                    payload_source.as_ref(),
                )?,
                arguments => Ty::Tuple(
                    arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| {
                            let source = self.child_result_context(
                                payload_source.as_ref(),
                                applications::ResultProjection::Tuple(index),
                            )?;
                            self.expr_result_expected(
                                &argument.value,
                                env,
                                payload_context.and_then(|ty| {
                                    if let Ty::Tuple(items) = ty {
                                        items.get(index)
                                    } else {
                                        None
                                    }
                                }),
                                source.as_ref(),
                            )
                        })
                        .collect::<Result<_>>()?,
                ),
            };
            return Ok(match normalized {
                "Some" => Ty::Optional(Box::new(payload)),
                "Ok" => Ty::Result(Box::new(payload), Box::new(Ty::Infer)),
                _ => Ty::Result(Box::new(Ty::Infer), Box::new(payload)),
            });
        }
        self.builtin(normalized, arguments, env)
    }
    fn callback(&self, expression: &Expr, inputs: &[Ty], env: &mut Env) -> Result<Ty> {
        if let ExprKind::Accessor(path) = &expression.kind {
            return self.callback(
                &transform::accessor_lambda(path, expression.span),
                inputs,
                env,
            );
        }
        if let ExprKind::Lambda {
            parameters,
            return_type,
            annotations,
            body,
        } = &expression.kind
        {
            let binder = self.child(None);
            if !annotations.is_empty()
                || parameters.iter().any(|parameter| {
                    parameter.mode != ParameterMode::Read || parameter.default.is_some()
                })
            {
                return Err(Failure::Unsupported(
                    "static callback invocation obligations".into(),
                ));
            }
            if parameters.len() != inputs.len() {
                return Err(Failure::Diagnostic(
                    "E0314",
                    "static callback arity mismatch".into(),
                ));
            }
            let mut child = env.clone();
            for (parameter, actual) in parameters.iter().zip(inputs) {
                if let Some(expected) = &parameter.ty {
                    require(actual, &self.ty(expected, env)?)?;
                }
                binder.bind(&parameter.pattern, actual.clone(), &mut child)?;
            }
            let expected = return_type
                .as_ref()
                .map_or(Ok(Ty::Infer), |expected| self.ty(expected, env))?;
            let mut checker = binder.child(Some(expected.clone()));
            checker.return_context = return_type
                .as_ref()
                .map(|syntax| checker.context_for_syntax(syntax, env))
                .transpose()?;
            let actual = checker.callable_result(checker.expr_result_expected(
                body,
                &mut child,
                Some(&expected),
                checker.return_context.as_ref(),
            )?)?;
            if let Some(expected) = return_type {
                require(&actual, &self.ty(expected, env)?)?;
            }
            return Ok(actual);
        }
        let Ty::Callable(parameters, result, _) = self.expr(expression, env)? else {
            return Err(Failure::Diagnostic(
                "E0338",
                "static callback is not callable".into(),
            ));
        };
        if parameters.len() != inputs.len() {
            return Err(Failure::Diagnostic(
                "E0314",
                "static callback arity mismatch".into(),
            ));
        }
        let mut inferred = BTreeMap::new();
        for (expected, actual) in parameters.iter().zip(inputs) {
            unify(expected, actual, &mut inferred)?;
        }
        Ok(substitute(*result, &inferred))
    }
    fn builtin(&self, name: &str, args: &[Argument], env: &mut Env) -> Result<Ty> {
        let arity = match name {
            "Array::first" | "Array::reverse" | "Map::keys" | "Map::values" | "Map::entries"
            | "Map::from" | "String::trim" | "String::lines" | "String::scalars"
            | "String::utf8" | "String::byte_len" => 1,
            "Array::fold" | "String::replace" | "String::slice" => 3,
            name if builtins::static_builtin(name) => 2,
            _ => {
                return Err(Failure::Unsupported(format!(
                    "static builtin signature proof {name}"
                )));
            }
        };
        if args.len() != arity {
            return Err(Failure::Diagnostic(
                "E0314",
                format!("{name} requires {arity} arguments"),
            ));
        }
        let first = self.expr(&args[0].value, env)?;
        if name.starts_with("Array::") {
            let Ty::Array(element, length) = first else {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "array operation requires array data".into(),
                ));
            };
            return Ok(match name {
                "Array::first" => Ty::Optional(element),
                "Array::get" => {
                    require(&self.expr(&args[1].value, env)?, &Ty::Number("int".into()))?;
                    Ty::Optional(element)
                }
                "Array::contains" => {
                    require(&self.expr(&args[1].value, env)?, &element)?;
                    if contains_callable_type(&element) {
                        return Err(Failure::Diagnostic(
                            "E0305",
                            "Array::contains requires equality".into(),
                        ));
                    }
                    Ty::Bool
                }
                "Array::reverse" => Ty::Array(element, length),
                "Array::concat" => {
                    let other = self.expr(&args[1].value, env)?;
                    require(&other, &Ty::Array(element.clone(), None))?;
                    let Ty::Array(_, other_length) = other else {
                        unreachable!()
                    };
                    Ty::Array(
                        element,
                        length.zip(other_length).and_then(|(a, b)| a.checked_add(b)),
                    )
                }
                "Array::map" => Ty::Array(
                    Box::new(erase_constants(self.callback(
                        &args[1].value,
                        &[*element],
                        env,
                    )?)),
                    length,
                ),
                "Array::filter" | "Array::find" | "Array::any" | "Array::all" => {
                    require(
                        &self.callback(&args[1].value, &[(*element).clone()], env)?,
                        &Ty::Bool,
                    )?;
                    match name {
                        "Array::filter" => Ty::Array(element, (length == Some(0)).then_some(0)),
                        "Array::find" => Ty::Optional(element),
                        _ => Ty::Bool,
                    }
                }
                "Array::for_each" => {
                    require(&self.callback(&args[1].value, &[*element], env)?, &Ty::Unit)?;
                    Ty::Unit
                }
                "Array::fold" => {
                    let initial = self.expr(&args[1].value, env)?;
                    require(
                        &self.callback(&args[2].value, &[initial.clone(), *element], env)?,
                        &initial,
                    )?;
                    initial
                }
                _ => {
                    return Err(Failure::Unsupported(format!(
                        "static array signature {name}"
                    )));
                }
            });
        }
        if name == "Map::from" {
            let Ty::Array(pair, _) = first else {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "Map::from requires array pairs".into(),
                ));
            };
            let Ty::Tuple(items) = *pair else {
                return Err(Failure::Unsupported(
                    "static empty Map::from inference".into(),
                ));
            };
            if items.len() != 2 {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "Map::from requires pairs".into(),
                ));
            }
            if contains_callable_type(&items[0]) {
                return Err(Failure::Diagnostic(
                    "E0305",
                    "map keys require equality".into(),
                ));
            }
            return Ok(Ty::Map(
                Box::new(items[0].clone()),
                Box::new(items[1].clone()),
            ));
        }
        if name.starts_with("Map::") {
            let Ty::Map(key, value) = first else {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "map operation requires map data".into(),
                ));
            };
            return Ok(match name {
                "Map::get" | "Map::contains" => {
                    require(&self.expr(&args[1].value, env)?, &key)?;
                    if name == "Map::get" {
                        Ty::Optional(value)
                    } else {
                        Ty::Bool
                    }
                }
                "Map::keys" => Ty::Array(key, None),
                "Map::values" => Ty::Array(value, None),
                "Map::entries" => Ty::Array(Box::new(Ty::Tuple(vec![*key, *value])), None),
                _ => return Err(Failure::Unsupported(format!("static map signature {name}"))),
            });
        }
        if name == "String::join" {
            require(&first, &Ty::Array(Box::new(Ty::String), None))?;
            require(&self.expr(&args[1].value, env)?, &Ty::String)?;
            return Ok(Ty::String);
        }
        if name.starts_with("String::") {
            require(&first, &Ty::String)?;
            for argument in &args[1..] {
                require(
                    &self.expr(&argument.value, env)?,
                    &if matches!(
                        name,
                        "String::slice"
                            | "String::scalar_at"
                            | "String::byte_offset"
                            | "String::scalar_offset"
                    ) {
                        Ty::Number("int".into())
                    } else {
                        Ty::String
                    },
                )?;
            }
            return Ok(match name {
                "String::contains" | "String::starts_with" | "String::ends_with" => Ty::Bool,
                "String::trim" | "String::replace" | "String::concat" => Ty::String,
                "String::split" | "String::lines" => Ty::Array(Box::new(Ty::String), None),
                "String::find" | "String::byte_offset" | "String::scalar_offset" => {
                    Ty::Optional(Box::new(Ty::Number("int".into())))
                }
                "String::slice" => Ty::Optional(Box::new(Ty::String)),
                "String::scalar_at" => Ty::Optional(Box::new(Ty::Number("u32".into()))),
                "String::scalars" => Ty::Array(Box::new(Ty::Number("u32".into())), None),
                "String::utf8" => Ty::Bytes,
                "String::byte_len" => Ty::Number("int".into()),
                _ => {
                    return Err(Failure::Unsupported(format!(
                        "static string signature {name}"
                    )));
                }
            });
        }
        Err(Failure::Unsupported(format!(
            "static builtin signature proof {name}"
        )))
    }
    fn type_names(&self, ty: &TypeExpr, env: &Env) -> Result<()> {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                let joined = path.join("::");
                let name = joined.strip_prefix("Prelude::").unwrap_or(&joined);
                if ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(name).is_some()
                    && !arguments.is_empty()
                {
                    return Err(Failure::Diagnostic(
                        "E0340",
                        "intrinsic atomic type has no generic arguments".into(),
                    ));
                }
                if let Some(Ty::Constructor(arity)) = env.get(name)
                    && arguments.len() != *arity
                {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "type constructor is not applied at its required kind arity".into(),
                    ));
                }
                if path.len() == 1 && path[0].starts_with("let ") {
                    return Ok(());
                }
                if !primitive_type(name)
                    && ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(name)
                        .is_none()
                    && !matches!(
                        name,
                        "Option"
                            | "Result"
                            | "Set"
                            | "Immut"
                            | "type"
                            | "Type"
                            | "Array::Elem"
                            | "Map::Key"
                            | "Map::Value"
                            | "Set::Elem"
                    )
                    && !self.evaluator.declarations.contains_key(&joined)
                    && !env.contains_key(name)
                {
                    return Err(Failure::Diagnostic(
                        "E0204",
                        format!("unknown static type {name}"),
                    ));
                }
                let parameters = self.evaluator.declarations.get(&joined).map(|declaration| {
                    if let Some(TypeExpr {
                        kind: TypeKind::TypeFunction { parameters, .. },
                        ..
                    }) = &declaration.value
                    {
                        parameters.as_slice()
                    } else {
                        declaration.generics.as_slice()
                    }
                });
                for (index, argument) in arguments.iter().enumerate() {
                    if !parameters
                        .and_then(|parameters| parameters.get(index))
                        .is_some_and(|parameter| {
                            static_value_parameter(parameter)
                                || matches!(
                                    parameter.bound.as_ref().map(|bound| &bound.kind),
                                    Some(TypeKind::KindArrow { .. })
                                )
                        })
                    {
                        self.type_names(argument, env)?;
                    }
                }
                if let Some(parameters) = parameters {
                    self.static_arguments(parameters, arguments, env)?;
                }
            }
            TypeKind::Optional(inner) | TypeKind::Rest(inner) | TypeKind::KeyOf(inner) => {
                self.type_names(inner, env)?
            }
            TypeKind::Array { element, length } => {
                self.type_names(element, env)?;
                if let Some(length) = length {
                    require(
                        &self.expr(length, &mut env.clone())?,
                        &Ty::Number("int".into()),
                    )?;
                }
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.type_names(item, env)?;
                }
            }
            TypeKind::Map { key, value } => {
                self.type_names(key, env)?;
                self.type_names(value, env)?;
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.type_names(&field.ty, env)?;
                }
                if let Some(row) = row {
                    self.type_names(row, env)?;
                }
            }
            TypeKind::Projection { base, .. } => self.type_names(base, env)?,
            TypeKind::ComputedProjection { base, key } => {
                self.type_names(base, env)?;
                self.expr(key, &mut env.clone())?;
            }
            TypeKind::Mapped { binder, value, .. } => {
                let mut child = env.clone();
                child.insert(binder.clone(), Ty::String);
                self.type_names(value, &child)?;
            }
            TypeKind::Computation(value) => {
                if let ExprKind::Unary { operator, operand } = &value.kind
                    && operator == "typeof"
                {
                    let mut checker = self.child(None);
                    checker.unevaluated = true;
                    checker.expr(operand, &mut env.clone())?;
                } else {
                    self.expr(value, &mut env.clone())?;
                }
            }
            TypeKind::KindArrow { parameter, result } => {
                self.type_names(parameter, env)?;
                self.type_names(result, env)?;
            }
            _ => {}
        }
        Ok(())
    }
    fn static_arguments(
        &self,
        parameters: &[GenericParameter],
        arguments: &[TypeExpr],
        env: &Env,
    ) -> Result<()> {
        if arguments.len() > parameters.len()
            || arguments.len()
                < parameters
                    .iter()
                    .filter(|parameter| parameter.default.is_none())
                    .count()
        {
            return Err(Failure::Diagnostic(
                "E0340",
                "static callable argument arity differs from its declaration".into(),
            ));
        }
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let value_sort = static_value_parameter(parameter);
            if value_sort {
                let actual = self.value_argument_type(argument, env)?;
                if let Some(bound) = &parameter.bound {
                    if matches!(bound.kind, TypeKind::KeyOf(_)) {
                        return Err(Failure::Unsupported(
                            "symbolic static-key membership proof".into(),
                        ));
                    }
                    let expected = self.ty(bound, env)?;
                    if let Err(failure) = require(&actual, &expected) {
                        return Err(match failure {
                            Failure::Diagnostic(_, message) => {
                                Failure::Diagnostic("E0323", message)
                            }
                            other => other,
                        });
                    }
                }
            } else if matches!(
                parameter.bound.as_ref().map(|bound| &bound.kind),
                Some(TypeKind::KindArrow { .. })
            ) {
                let TypeKind::Name { path, arguments } = &argument.kind else {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "higher-kinded parameter requires an unapplied constructor".into(),
                    ));
                };
                if !arguments.is_empty() {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "higher-kinded parameter requires an unapplied constructor".into(),
                    ));
                }
                let joined = path.join("::");
                let name = joined.strip_prefix("Prelude::").unwrap_or(&joined);
                let actual = match env.get(name) { Some(Ty::Constructor(arity)) => Some(*arity), Some(_) => None, None => match name { "Option" | "Set" | "Immut" | "Array::Elem" | "Map::Key" | "Map::Value" | "Set::Elem" => Some(1), "Result" => Some(2), _ => self.evaluator.declarations.get(&joined).and_then(|declaration| { let parameters = if let Some(TypeExpr { kind: TypeKind::TypeFunction { parameters, .. }, .. }) = &declaration.value { parameters } else { &declaration.generics }; parameters.iter().all(|parameter| parameter.name.chars().next().is_some_and(char::is_uppercase) && parameter.bound.as_ref().is_none_or(|bound| matches!(&bound.kind, TypeKind::Name { path, arguments } if path == &["Type"] && arguments.is_empty()))).then_some(parameters.len()) }) } };
                if actual != Some(types::kind_arity(parameter.bound.as_ref().unwrap())) {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "higher-kinded argument has a different constructor kind".into(),
                    ));
                }
            } else if matches!(argument.kind, TypeKind::Computation(_))
                || matches!(&argument.kind, TypeKind::Name { path, arguments } if arguments.is_empty() && env.get(&path.join("::")).is_some_and(|ty| !matches!(ty, Ty::TypeParameter)))
            {
                return Err(Failure::Diagnostic(
                    "E0323",
                    "static type parameter requires a type argument".into(),
                ));
            } else if let Some(bound) = &parameter.bound {
                self.check_argument_bound(argument, bound, env)?;
            }
        }
        Ok(())
    }
    fn value_argument_type(&self, argument: &TypeExpr, env: &Env) -> Result<Ty> {
        match &argument.kind {
            TypeKind::Computation(value) => self.expr(value, &mut env.clone()),
            TypeKind::Tuple(items) if items.is_empty() => Ok(Ty::Unit),
            TypeKind::Tuple(items) => Ok(Ty::Tuple(
                items
                    .iter()
                    .map(|item| self.value_argument_type(item, env))
                    .collect::<Result<_>>()?,
            )),
            TypeKind::Name { path, arguments } if arguments.is_empty() => {
                let name = path.join("::");
                env.get(&name)
                    .cloned()
                    .or_else(|| {
                        (name == "Prelude::None"
                            || (name == "None"
                                && !self.evaluator.declarations.contains_key(&name)
                                && !self.evaluator.functions.contains_key(&name)))
                        .then(|| Ty::Optional(Box::new(Ty::Infer)))
                    })
                    .ok_or_else(|| {
                        Failure::Unsupported("static argument value lookup proof".into())
                    })
            }
            _ => Err(Failure::Diagnostic(
                "E0323",
                "type syntax supplied to a static value parameter".into(),
            )),
        }
    }
    fn check_argument_bound(&self, argument: &TypeExpr, bound: &TypeExpr, env: &Env) -> Result<()> {
        if matches!(&bound.kind,TypeKind::Name { path,arguments } if path == &["Type"] && arguments.is_empty())
        {
            return Ok(());
        }
        if contains_mutable_field(argument, self.evaluator, &mut BTreeSet::new())
            || contains_mutable_field(bound, self.evaluator, &mut BTreeSet::new())
        {
            return Err(Failure::Unsupported(
                "symbolic bounded field mutability proof".into(),
            ));
        }
        let actual = self.ty(argument, env)?;
        if contains_generic_type(&actual) {
            return Err(Failure::Unsupported(
                "symbolic type bound implication proof".into(),
            ));
        }
        if let TypeKind::Record {
            fields,
            row: Some(row),
        } = &bound.kind
        {
            let Ty::Record(actual) = actual else {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "type argument does not admit a required record bound".into(),
                ));
            };
            let mut remainder = actual.clone();
            for field in fields {
                let Some(value) = remainder.remove(&field.name) else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "type argument is missing a required bounded field".into(),
                    ));
                };
                require_field_mode(value.0, field.mutable)?;
                require(&value.1, &self.ty(&field.ty, env)?)?;
            }
            if matches!(&row.kind,TypeKind::Name { path,arguments } if path.len()==1 && arguments.is_empty() && env.get(&path[0]) == Some(&Ty::TypeParameter))
            {
                return Ok(());
            }
            return require(&Ty::Record(remainder), &self.ty(row, env)?);
        }
        require(&actual, &self.ty(bound, env)?)
    }
}
fn contains_generic_type(ty: &Ty) -> bool {
    match ty {
        Ty::Generic(_) | Ty::TypeParameter | Ty::Constructor(_) | Ty::Unknown => true,
        Ty::Array(inner, _) | Ty::Optional(inner) => contains_generic_type(inner),
        Ty::Map(a, b) | Ty::Result(a, b) => contains_generic_type(a) || contains_generic_type(b),
        Ty::Tuple(items) => items.iter().any(contains_generic_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_generic_type(ty)),
        Ty::Callable(inputs, result, _) => {
            inputs.iter().any(contains_generic_type) || contains_generic_type(result)
        }
        _ => false,
    }
}
fn contains_mutable_field(
    ty: &TypeExpr,
    evaluator: &Evaluator,
    seen: &mut BTreeSet<String>,
) -> bool {
    match &ty.kind {
        TypeKind::Record { fields, row } => {
            fields.iter().any(|field| {
                field.mutable || contains_mutable_field(&field.ty, evaluator, &mut seen.clone())
            }) || row
                .as_ref()
                .is_some_and(|row| contains_mutable_field(row, evaluator, &mut seen.clone()))
        }
        TypeKind::Name { path, arguments } => {
            arguments
                .iter()
                .any(|argument| contains_mutable_field(argument, evaluator, &mut seen.clone()))
                || (seen.insert(path.join("::"))
                    && evaluator
                        .declarations
                        .get(&path.join("::"))
                        .and_then(|declaration| declaration.value.as_ref())
                        .is_some_and(|value| contains_mutable_field(value, evaluator, seen)))
        }
        TypeKind::Tuple(arguments) => arguments
            .iter()
            .any(|argument| contains_mutable_field(argument, evaluator, &mut seen.clone())),
        TypeKind::Optional(inner)
        | TypeKind::Array { element: inner, .. }
        | TypeKind::Rest(inner) => contains_mutable_field(inner, evaluator, seen),
        TypeKind::Map { key, value } => {
            contains_mutable_field(key, evaluator, &mut seen.clone())
                || contains_mutable_field(value, evaluator, &mut seen.clone())
        }
        _ => false,
    }
}
fn static_value_parameter(parameter: &GenericParameter) -> bool {
    parameter
        .name
        .chars()
        .next()
        .is_some_and(char::is_lowercase)
        || matches!(
            parameter.bound.as_ref().map(|bound| &bound.kind),
            Some(TypeKind::KeyOf(_))
        )
}
fn bind_row_types(ty: &TypeExpr, env: &mut Env, evaluator: &Evaluator) {
    if let TypeKind::Record { row: Some(row), .. } = &ty.kind
        && let TypeKind::Name { path, arguments } = &row.kind
        && path.len() == 1
        && arguments.is_empty()
        && !evaluator.declarations.contains_key(&path[0])
    {
        env.entry(path[0].clone()).or_insert(Ty::TypeParameter);
    }
}
fn require_static_key(ty: &Ty) -> Result<()> {
    match ty {
        Ty::Unit | Ty::Bool | Ty::String | Ty::Bytes | Ty::Infer | Ty::IntegerConstant(_) => Ok(()),
        Ty::Number(name) if !matches!(name.as_str(), "f32" | "f64") => Ok(()),
        Ty::Generic(_) | Ty::Unknown => Err(Failure::Unsupported(
            "static map key representation proof".into(),
        )),
        _ => Err(Failure::Diagnostic(
            "E0328",
            "map keys require admitted scalar value representations".into(),
        )),
    }
}
fn contains_callable_type(ty: &Ty) -> bool {
    match ty {
        Ty::Callable(..) => true,
        Ty::Array(inner, _) | Ty::Optional(inner) => contains_callable_type(inner),
        Ty::Map(a, b) | Ty::Result(a, b) => contains_callable_type(a) || contains_callable_type(b),
        Ty::Tuple(items) => items.iter().any(contains_callable_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_callable_type(ty)),
        _ => false,
    }
}
fn unify(expected: &Ty, actual: &Ty, inferred: &mut Env) -> Result<()> {
    match (expected, actual) {
        (Ty::Generic(name), actual) => {
            if let Some(old) = inferred.get(name) {
                require(actual, old)
            } else {
                inferred.insert(name.clone(), erase_constants(actual.clone()));
                Ok(())
            }
        }
        (Ty::Array(a, expected_length), Ty::Array(b, actual_length)) => {
            require_length(*actual_length, *expected_length)?;
            unify(a, b, inferred)
        }
        (Ty::Optional(a), Ty::Optional(b)) => unify(a, b, inferred),
        (Ty::Map(a, b), Ty::Map(c, d)) | (Ty::Result(a, b), Ty::Result(c, d)) => {
            unify(a, c, inferred)?;
            unify(b, d, inferred)
        }
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
            for (a, b) in a.iter().zip(b) {
                unify(a, b, inferred)?;
            }
            Ok(())
        }
        (Ty::Record(a), Ty::Record(b)) if a.keys().eq(b.keys()) => {
            for (name, (mode, a)) in a {
                require_field_mode(b[name].0, *mode)?;
                unify(a, &b[name].1, inferred)?;
                if *mode {
                    require_invariant(&b[name].1, &substitute(a.clone(), inferred))?;
                }
            }
            Ok(())
        }
        _ => require(actual, expected),
    }
}
fn substitute(ty: Ty, inferred: &Env) -> Ty {
    match ty {
        Ty::Generic(name) => inferred.get(&name).cloned().unwrap_or(Ty::Unknown),
        Ty::Array(inner, length) => Ty::Array(Box::new(substitute(*inner, inferred)), length),
        Ty::Optional(inner) => Ty::Optional(Box::new(substitute(*inner, inferred))),
        Ty::Map(a, b) => Ty::Map(
            Box::new(substitute(*a, inferred)),
            Box::new(substitute(*b, inferred)),
        ),
        Ty::Result(a, b) => Ty::Result(
            Box::new(substitute(*a, inferred)),
            Box::new(substitute(*b, inferred)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .into_iter()
                .map(|ty| substitute(ty, inferred))
                .collect(),
        ),
        Ty::Record(fields) => Ty::Record(
            fields
                .into_iter()
                .map(|(name, (mode, ty))| (name, (mode, substitute(ty, inferred))))
                .collect(),
        ),
        Ty::Callable(inputs, result, signatures) => Ty::Callable(
            inputs
                .into_iter()
                .map(|ty| substitute(ty, inferred))
                .collect(),
            Box::new(substitute(*result, inferred)),
            signatures,
        ),
        ty => ty,
    }
}
fn require(actual: &Ty, expected: &Ty) -> Result<()> {
    if *actual == Ty::Unknown || *expected == Ty::Unknown {
        return Err(Failure::Unsupported(
            "static ordinary typing remains unresolved".into(),
        ));
    }
    if actual == expected || *actual == Ty::Never || *actual == Ty::Infer || *expected == Ty::Infer
    {
        return Ok(());
    }
    match (actual, expected) {
        (Ty::IntegerConstant(_), Ty::IntegerConstant(_)) => Ok(()),
        (Ty::IntegerConstant(_), Ty::Number(name)) | (Ty::Number(name), Ty::IntegerConstant(_))
            if name == "int" =>
        {
            Ok(())
        }
        (Ty::Optional(a), Ty::Optional(b)) => require(a, b),
        (Ty::Array(a, actual_length), Ty::Array(b, expected_length)) => {
            require_length(*actual_length, *expected_length)?;
            require(a, b)
        }
        (Ty::Map(a, b), Ty::Map(c, d)) | (Ty::Result(a, b), Ty::Result(c, d)) => {
            require(a, c)?;
            require(b, d)
        }
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
            for (a, b) in a.iter().zip(b) {
                require(a, b)?;
            }
            Ok(())
        }
        (Ty::Record(a), Ty::Record(b)) if a.keys().eq(b.keys()) => {
            for (name, (mode, a)) in a {
                require_field_mode(*mode, b[name].0)?;
                if *mode {
                    require_invariant(a, &b[name].1)?;
                } else {
                    require(a, &b[name].1)?;
                }
            }
            Ok(())
        }
        (Ty::Callable(a, result, _), Ty::Callable(b, expected_result, _))
            if a.len() == b.len()
                && a.iter().zip(b).all(|(a, b)| {
                    erase_interfaces(erase_constants(a.clone()))
                        == erase_interfaces(erase_constants(b.clone()))
                }) =>
        {
            require(result, expected_result)
        }
        _ => Err(Failure::Diagnostic(
            "E0301",
            format!("static definition expected {expected:?}, found {actual:?}"),
        )),
    }
}
fn require_field_mode(actual: bool, expected: bool) -> Result<()> {
    if actual == expected {
        Ok(())
    } else {
        // A construction context can choose slot modes, but a value comparison
        // alone cannot establish that the expression is that construction.
        Err(Failure::Unsupported(
            "static record slot-mode conversion requires its construction or view witness".into(),
        ))
    }
}
fn require_invariant(actual: &Ty, expected: &Ty) -> Result<()> {
    let actual = erase_constants(actual.clone());
    let expected = erase_constants(expected.clone());
    if actual == expected || actual == Ty::Infer || expected == Ty::Infer {
        Ok(())
    } else {
        require(&actual, &expected)?;
        require(&expected, &actual)
    }
}
fn require_length(actual: Option<usize>, expected: Option<usize>) -> Result<()> {
    if expected.is_none() || actual == expected {
        Ok(())
    } else {
        Err(Failure::Diagnostic(
            "E0301",
            "static array length does not satisfy its required type".into(),
        ))
    }
}

/// Branches retain only facts true on every normal path. In particular, neither
/// a selected integer value nor one branch's array length can leak out of a join.
fn join_types(a: &Ty, b: &Ty) -> Result<Ty> {
    if a == b {
        return Ok(a.clone());
    }
    if *a == Ty::Never || *a == Ty::Infer {
        return Ok(b.clone());
    }
    if *b == Ty::Never || *b == Ty::Infer {
        return Ok(a.clone());
    }
    Ok(match (a, b) {
        (Ty::IntegerConstant(_), Ty::IntegerConstant(_)) => Ty::Number("int".into()),
        (Ty::IntegerConstant(_), Ty::Number(name)) | (Ty::Number(name), Ty::IntegerConstant(_))
            if name == "int" =>
        {
            Ty::Number("int".into())
        }
        (Ty::Array(a, al), Ty::Array(b, bl)) => Ty::Array(
            Box::new(join_types(a, b)?),
            if al == bl { *al } else { None },
        ),
        (Ty::Optional(a), Ty::Optional(b)) => Ty::Optional(Box::new(join_types(a, b)?)),
        (Ty::Map(a, b), Ty::Map(c, d)) => {
            Ty::Map(Box::new(join_types(a, c)?), Box::new(join_types(b, d)?))
        }
        (Ty::Result(a, b), Ty::Result(c, d)) => {
            Ty::Result(Box::new(join_types(a, c)?), Box::new(join_types(b, d)?))
        }
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => Ty::Tuple(
            a.iter()
                .zip(b)
                .map(|(a, b)| join_types(a, b))
                .collect::<Result<_>>()?,
        ),
        (Ty::Record(a), Ty::Record(b)) if a.keys().eq(b.keys()) => Ty::Record(
            a.iter()
                .map(|(name, (mode, a))| {
                    require_field_mode(*mode, b[name].0)?;
                    if *mode {
                        require_invariant(a, &b[name].1)?;
                    }
                    Ok((name.clone(), (*mode, join_types(a, &b[name].1)?)))
                })
                .collect::<Result<_>>()?,
        ),
        (Ty::Callable(inputs, result, left), Ty::Callable(other_inputs, other_result, right)) => {
            require(
                &Ty::Callable(inputs.clone(), result.clone(), left.clone()),
                &Ty::Callable(other_inputs.clone(), other_result.clone(), right.clone()),
            )?;
            let mut signatures = left.clone();
            for signature in right {
                if !signatures.contains(signature) {
                    signatures.push(signature.clone());
                }
            }
            Ty::Callable(
                inputs.clone(),
                Box::new(join_types(result, other_result)?),
                signatures,
            )
        }
        _ => {
            require(a, b)?;
            erase_constants(a.clone())
        }
    })
}

fn erase_constants(ty: Ty) -> Ty {
    match ty {
        Ty::IntegerConstant(_) => Ty::Number("int".into()),
        Ty::Array(inner, length) => Ty::Array(Box::new(erase_constants(*inner)), length),
        Ty::Optional(inner) => Ty::Optional(Box::new(erase_constants(*inner))),
        Ty::Map(a, b) => Ty::Map(Box::new(erase_constants(*a)), Box::new(erase_constants(*b))),
        Ty::Result(a, b) => {
            Ty::Result(Box::new(erase_constants(*a)), Box::new(erase_constants(*b)))
        }
        Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(erase_constants).collect()),
        Ty::Record(fields) => Ty::Record(
            fields
                .into_iter()
                .map(|(name, (mode, ty))| (name, (mode, erase_constants(ty))))
                .collect(),
        ),
        Ty::Callable(inputs, result, signatures) => Ty::Callable(
            inputs.into_iter().map(erase_constants).collect(),
            Box::new(erase_constants(*result)),
            signatures,
        ),
        other => other,
    }
}

fn erase_interfaces(mut ty: Ty) -> Ty {
    fn visit(ty: &mut Ty) {
        match ty {
            Ty::Array(inner, _) | Ty::Optional(inner) => visit(inner),
            Ty::Map(a, b) | Ty::Result(a, b) => {
                visit(a);
                visit(b);
            }
            Ty::Tuple(items) => {
                for item in items {
                    visit(item);
                }
            }
            Ty::Record(fields) => {
                for (_, value) in fields.values_mut() {
                    visit(value);
                }
            }
            Ty::Callable(inputs, result, signatures) => {
                signatures.clear();
                for input in inputs {
                    visit(input);
                }
                visit(result);
            }
            _ => {}
        }
    }
    visit(&mut ty);
    ty
}

fn with_interfaces(actual: Ty, expected: &Ty) -> Ty {
    match (actual, expected) {
        (Ty::Infer, expected) => expected.clone(),
        (Ty::Callable(..), Ty::Callable(..)) => expected.clone(),
        (Ty::Array(inner, length), Ty::Array(expected, _)) => {
            Ty::Array(Box::new(with_interfaces(*inner, expected)), length)
        }
        (Ty::Optional(inner), Ty::Optional(expected)) => {
            Ty::Optional(Box::new(with_interfaces(*inner, expected)))
        }
        (Ty::Tuple(items), Ty::Tuple(expected)) if items.len() == expected.len() => Ty::Tuple(
            items
                .into_iter()
                .zip(expected)
                .map(|(actual, expected)| with_interfaces(actual, expected))
                .collect(),
        ),
        (Ty::Record(mut fields), Ty::Record(expected)) => {
            for (name, (_, value)) in &mut fields {
                if let Some((_, expected)) = expected.get(name) {
                    *value = with_interfaces(value.clone(), expected);
                }
            }
            Ty::Record(fields)
        }
        (Ty::Map(key, value), Ty::Map(ek, ev)) => Ty::Map(
            Box::new(with_interfaces(*key, ek)),
            Box::new(with_interfaces(*value, ev)),
        ),
        (Ty::Result(ok, error), Ty::Result(eo, ee)) => Ty::Result(
            Box::new(with_interfaces(*ok, eo)),
            Box::new(with_interfaces(*error, ee)),
        ),
        (actual, _) => actual,
    }
}

fn int_fact(value: Option<i128>, layout: TargetLayout) -> Ty {
    let limit = 1i128 << (layout.pointer_bits - 1);
    value
        .filter(|value| *value >= -limit && *value < limit)
        .map_or(Ty::Number("int".into()), Ty::IntegerConstant)
}
fn contains_result_type(ty: &Ty) -> bool {
    match ty {
        Ty::Result(..) => true,
        Ty::Array(inner, _) | Ty::Optional(inner) => contains_result_type(inner),
        Ty::Map(key, value) => contains_result_type(key) || contains_result_type(value),
        Ty::Tuple(items) => items.iter().any(contains_result_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_result_type(ty)),
        Ty::Callable(parameters, result, _) => {
            parameters.iter().any(contains_result_type) || contains_result_type(result)
        }
        _ => false,
    }
}
fn contains_meta_type(ty: &Ty) -> bool {
    match ty {
        Ty::Meta | Ty::TypeParameter | Ty::Constructor(_) => true,
        Ty::Array(inner, _) | Ty::Optional(inner) => contains_meta_type(inner),
        Ty::Map(key, value) | Ty::Result(key, value) => {
            contains_meta_type(key) || contains_meta_type(value)
        }
        Ty::Tuple(items) => items.iter().any(contains_meta_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_meta_type(ty)),
        _ => false,
    }
}
fn value_ty(value: &StaticValue) -> Ty {
    match value {
        StaticValue::Result(produced) => {
            if produced.success {
                Ty::Result(Box::new(value_ty(&produced.payload)), Box::new(Ty::Infer))
            } else {
                Ty::Result(Box::new(Ty::Infer), Box::new(value_ty(&produced.payload)))
            }
        }
        StaticValue::Integer(value) => Ty::IntegerConstant(*value),
        StaticValue::TypedInteger(_, bits, signed) => {
            Ty::Number(format!("{}{bits}", if *signed { 'i' } else { 'u' }))
        }
        StaticValue::Float(_, narrow) => Ty::Number(if *narrow { "f32" } else { "f64" }.into()),
        StaticValue::BigInteger(_) => Ty::Number("bigint".into()),
        StaticValue::Bool(_) => Ty::Bool,
        StaticValue::String(_) => Ty::String,
        StaticValue::Bytes(_) => Ty::Bytes,
        StaticValue::Unit => Ty::Unit,
        StaticValue::Type(_) => Ty::Meta,
        StaticValue::Array(values) => Ty::Array(
            Box::new(erase_constants(values.first().map_or(Ty::Infer, value_ty))),
            Some(values.len()),
        ),
        StaticValue::ArrayWindow(values) => Ty::Array(
            Box::new(erase_constants(values.first().map_or(Ty::Infer, value_ty))),
            values
                .source_type
                .as_ref()
                .is_some_and(|source| {
                    matches!(
                        source.syntax.kind,
                        TypeKind::Array {
                            length: Some(_),
                            ..
                        }
                    )
                })
                .then_some(values.len),
        ),
        StaticValue::Tuple(values) => Ty::Tuple(values.iter().map(value_ty).collect()),
        StaticValue::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(name, value)| {
                    (
                        name.clone(),
                        (fields.mutable_fields.contains(name), value_ty(value)),
                    )
                })
                .collect(),
        ),
        StaticValue::Variant(name, values, _) => {
            let value = values.first().map_or(Ty::Unit, value_ty);
            match name.rsplit("::").next().unwrap_or(name) {
                "None" => Ty::Optional(Box::new(Ty::Infer)),
                "Some" => Ty::Optional(Box::new(value)),
                "Ok" => Ty::Result(Box::new(value), Box::new(Ty::Infer)),
                _ => Ty::Result(Box::new(Ty::Infer), Box::new(value)),
            }
        }
        StaticValue::Map(values) => values.first().map_or(
            Ty::Map(Box::new(Ty::Infer), Box::new(Ty::Infer)),
            |(key, value)| Ty::Map(Box::new(value_ty(key)), Box::new(value_ty(value))),
        ),
        _ => Ty::Unknown,
    }
}
fn bind_type_pattern(ty: &TypeExpr, env: &mut Env) -> Result<()> {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            if path.len() == 1 && path[0].starts_with("let ") {
                if !arguments.is_empty() {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "type pattern constructor head must be rigid".into(),
                    ));
                }
                if &path[0][4..] != "_" {
                    env.insert(path[0][4..].into(), Ty::TypeParameter);
                }
            }
            for argument in arguments {
                bind_type_pattern(argument, env)?;
            }
        }
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Array { element: inner, .. } => bind_type_pattern(inner, env)?,
        TypeKind::Map { key, value } => {
            bind_type_pattern(key, env)?;
            bind_type_pattern(value, env)?;
        }
        TypeKind::Tuple(items) => {
            for item in items {
                bind_type_pattern(item, env)?;
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                bind_type_pattern(&field.ty, env)?;
            }
            if let Some(row) = row {
                bind_type_pattern(row, env)?;
            }
        }
        _ => {}
    }
    Ok(())
}
