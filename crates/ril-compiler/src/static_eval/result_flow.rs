//! Universal normal-path Result proof for the immutable static subset.
//! Abstract paths never obtain a tag or inspection from actual evaluation.
use super::*;
use std::rc::Rc;
use std::sync::Arc;
#[path = "result_flow_consts.rs"]
mod consts;
#[path = "result_flow_fallback.rs"]
mod fallback;
#[path = "result_flow_loops.rs"]
mod loops;
#[path = "result_flow_maps.rs"]
mod maps;
#[path = "result_flow_receiving.rs"]
mod receiving;
#[path = "result_flow_contexts.rs"]
mod result_contexts;
#[path = "result_flow_sources.rs"]
mod sources;

type Paths = std::result::Result<Vec<Path>, Problem>;
type EnvValues = BTreeMap<String, Value>;
type Operands = (Vec<(State, Vec<Value>)>, Vec<Path>);
type BoundScope = Arc<bounds::BoundEnvironment>;
type Caller = (u32, EnvValues, BoundScope);
type ResultContext = applications::ResultContext;
use result_contexts::CallContext;

struct Problem {
    failure: Box<Failure>,
    span: Span,
    producer: Option<Span>,
}
fn at<T>(result: Result<T>, span: Span) -> std::result::Result<T, Problem> {
    result.map_err(|failure| Problem {
        failure: Box::new(failure),
        span,
        producer: None,
    })
}
fn incomplete(span: Span, why: &str) -> Problem {
    Problem {
        failure: Box::new(Failure::Unsupported(why.into())),
        span,
        producer: None,
    }
}

#[derive(Clone, PartialEq, Eq)]
struct Value {
    source_type: Option<Arc<crate::sema::model::SourceTypeWitness>>,
    ty: Ty,
    shape: Shape,
}
#[derive(Clone, PartialEq, Eq)]
enum Shape {
    Plain,
    Bool(bool),
    BoolSymbol {
        id: u32,
        positive: bool,
    },
    Integer(i128),
    Text(String),
    Tuple(Vec<Value>),
    Array(Vec<Value>),
    Map(Vec<(Value, Value)>),
    Record(BTreeMap<String, Value>),
    /// Only these fields are guaranteed by the declaration. An open tail still
    /// carries an opaque borrowed family; it is never a closed member graph.
    BoundRecord {
        fields: BTreeMap<String, Value>,
        open: bool,
    },
    Optional {
        tag: Option<bool>,
        choice: Option<u32>,
        payload: Box<Value>,
    },
    Result {
        id: u32,
        tag: Option<bool>,
        ok: Box<Value>,
        error: Box<Value>,
    },
    Callable(Rc<Callable>),
    Unknown,
}
#[derive(Clone, PartialEq, Eq)]
enum Callable {
    Named {
        name: String,
        explicit: Vec<TypeExpr>,
        /// Closed arguments are frozen immediately. Symbolic arguments may
        /// only be used in the lexical scope that supplied their identities.
        explicit_scope: Option<BoundScope>,
    },
    Builtin(String),
    Lambda {
        parameters: Vec<Parameter>,
        body: Box<Expr>,
        captured: EnvValues,
        bound_scope: BoundScope,
        return_type: Option<TypeExpr>,
        output: Ty,
    },
    View {
        target: Rc<Callable>,
        parameters: Vec<application::ParameterSpec>,
        output: Box<Ty>,
    },
    Unknown,
}
impl Value {
    fn unit() -> Self {
        Self {
            source_type: None,
            ty: Ty::Unit,
            shape: Shape::Plain,
        }
    }
    fn boolean(value: bool) -> Self {
        Self {
            source_type: None,
            ty: Ty::Bool,
            shape: Shape::Bool(value),
        }
    }
    fn with_type(mut self, ty: &Ty) -> Self {
        if self.ty != *ty {
            self.source_type = None;
        }
        match (&mut self.shape, ty) {
            (Shape::Result { ok, error, .. }, Ty::Result(ok_ty, error_ty)) => {
                **ok = ok.clone().with_type(ok_ty);
                **error = error.clone().with_type(error_ty);
            }
            (Shape::Optional { payload, .. }, Ty::Optional(inner)) => {
                **payload = payload.clone().with_type(inner)
            }
            (Shape::Tuple(items), Ty::Tuple(types)) => {
                for (item, ty) in items.iter_mut().zip(types) {
                    *item = item.clone().with_type(ty);
                }
            }
            (Shape::Array(items), Ty::Array(inner, _)) => {
                for item in items {
                    *item = item.clone().with_type(inner);
                }
            }
            (Shape::Map(items), Ty::Map(key, value)) => {
                for (item_key, item_value) in items {
                    *item_key = item_key.clone().with_type(key);
                    *item_value = item_value.clone().with_type(value);
                }
            }
            (Shape::Record(fields) | Shape::BoundRecord { fields, .. }, Ty::Record(types)) => {
                for (name, value) in fields {
                    if let Some((_, ty)) = types.get(name) {
                        *value = value.clone().with_type(ty);
                    }
                }
            }
            (Shape::Callable(target), Ty::Callable(_, output, interfaces))
                if interfaces.len() == 1 =>
            {
                *target = Rc::new(Callable::View {
                    target: target.clone(),
                    parameters: interfaces[0].clone(),
                    output: output.clone(),
                })
            }
            (Shape::Integer(_), Ty::Number(name)) if matches!(name.as_str(), "f32" | "f64") => {
                // The source integer may be an inference hole selected as a
                // float by this context. Its unrounded mathematical value is
                // not evidence about the committed IEEE value.
                self.shape = Shape::Plain;
            }
            _ => {}
        }
        self.ty = ty.clone();
        self
    }
}
#[derive(Clone, PartialEq, Eq)]
struct Duty {
    owner: u32,
    span: Span,
    inspected: bool,
}
#[derive(Clone, PartialEq, Eq)]
struct State {
    env: EnvValues,
    globals: EnvValues,
    bound_scope: BoundScope,
    duties: BTreeMap<u32, Duty>,
    tags: BTreeMap<u32, bool>,
    booleans: BTreeMap<u32, bool>,
    owner: u32,
    unproved_path: bool,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Exit {
    Normal,
    Return,
    Next(u32),
    Last(u32),
    Abnormal,
}
struct Path {
    state: State,
    value: Value,
    exit: Exit,
}
impl Path {
    fn normal(state: State, value: Value) -> Self {
        Self {
            state,
            value,
            exit: Exit::Normal,
        }
    }
}

struct Engine<'a> {
    evaluator: &'a Evaluator,
    contexts: Arc<BTreeMap<String, bounds::BoundEnvironment>>,
    global_functions: BTreeSet<String>,
    next_producer: u32,
    next_owner: u32,
    next_boolean: u32,
    work: u32,
    stack: Vec<String>,
    loop_targets: Vec<(u32, Option<ResultContext>)>,
    next_loop: u32,
    depth: u32,
    return_context: Option<ResultContext>,
}

pub(super) fn verify(evaluator: &Evaluator, program: &Program, output: &mut Evaluation) -> bool {
    if !relevant(program) {
        if evaluator.results.has_producers() {
            if let Some(statement) = program.statements.first() {
                report(
                    incomplete(
                        statement.span,
                        "actual static Result production lacks a universal source-flow certificate",
                    ),
                    output,
                );
            }
            return false;
        }
        return true;
    }
    let module_span = program.statements.last().unwrap().span;
    let contexts = contexts::collect(evaluator, program);
    let globals = program
        .statements
        .iter()
        .filter_map(|statement| {
            if let StmtKind::Function(function) = &statement.kind {
                Some(function.name.clone())
            } else {
                None
            }
        })
        .collect();
    let mut engine = Engine {
        evaluator,
        contexts: Arc::new(contexts.clone()),
        global_functions: globals,
        next_producer: 0,
        next_owner: 1,
        next_boolean: 0,
        work: 0,
        stack: vec![],
        loop_targets: vec![],
        next_loop: 0,
        depth: 0,
        return_context: None,
    };
    let initial = State {
        env: BTreeMap::new(),
        globals: BTreeMap::new(),
        bound_scope: Arc::default(),
        duties: BTreeMap::new(),
        tags: BTreeMap::new(),
        booleans: BTreeMap::new(),
        owner: 0,
        unproved_path: false,
    };
    let mut valid = true;
    for statement in &program.statements {
        if statement_type_computation_relevant(statement) {
            valid = false;
            report(
                incomplete(
                    statement.span,
                    "Result production in a static annotation requires an annotation-exit proof",
                ),
                output,
            );
        }
        match &statement.kind {
            StmtKind::Type(TypeDeclaration {
                value:
                    Some(TypeExpr {
                        kind: TypeKind::TypeFunction { .. },
                        ..
                    }),
                ..
            }) => {
                valid = false;
                report(
                    incomplete(
                        statement.span,
                        "static Result type-function flow requires its own producer exit certificate",
                    ),
                    output,
                );
            }
            StmtKind::Function(function)
                if !function.is_meta
                    && function.body.as_ref().is_some_and(runtime_meta_relevant) =>
            {
                valid = false;
                report(
                    incomplete(
                        statement.span,
                        "local meta Result publication in an ordinary callable requires a separate receipt scope",
                    ),
                    output,
                );
            }
            _ => {}
        }
    }
    for function in evaluator
        .functions
        .values()
        .filter(|function| function.is_meta)
    {
        let result = (|| {
            let mut state = initial.clone();
            let captured = contexts.get(&function.name).cloned().unwrap_or_default();
            let scope = at(
                Typer::new(evaluator, None).function_generic_environment(function, &captured),
                function.span,
            )?;
            state.bound_scope = Arc::new(scope);
            if let Some(context) = contexts.get(&function.name) {
                for (name, ty) in &context.values {
                    let mut value = engine.seed(ty, &mut state, function.span, u32::MAX)?;
                    if let Some(actual) = evaluator.global_values.get(name) {
                        known_global(&mut value, actual);
                    }
                    state.env.insert(name.clone(), value);
                }
            }
            // Own const binders mask a captured same-spelled ordinary value.
            // The universal scope contains their genuine unknown int roles.
            engine.seed_const_bindings(&mut state, function.span)?;
            state.globals = state.env.clone();
            let types = Engine::types(&state);
            state.owner = engine.owner(function.span)?;
            let Some(body) = &function.body else {
                return Err(incomplete(
                    function.span,
                    "static Result definition lacks a body",
                ));
            };
            let context = engine.callable_return_context(
                function.return_type.as_ref(),
                &function.parameters,
                &state,
            )?;
            engine.with_return_context(context.clone(), |engine| {
                for path in engine.universal_parameters(&function.parameters, state, types)? {
                    let paths = if path.exit == Exit::Normal {
                        engine.block_expected(body, path.state, context.as_ref())?
                    } else {
                        vec![path]
                    };
                    for path in paths {
                        engine.finish(path, function.span, None)?;
                    }
                }
                Ok(())
            })?;
            Ok(())
        })();
        if let Err(problem) = result {
            valid = false;
            report(problem, output);
        }
    }
    let result = (|| {
        let mut states = vec![initial];
        for statement in &program.statements {
            let StmtKind::Binding(binding) = &statement.kind else {
                continue;
            };
            if !binding.is_meta {
                continue;
            }
            let mut next = vec![];
            for state in states {
                let context = engine.annotation_context(binding.ty.as_ref(), &state)?;
                for path in engine.expr_expected(&binding.value, state, context.as_ref())? {
                    if path.exit == Exit::Abnormal {
                        continue;
                    }
                    if path.exit != Exit::Normal {
                        return Err(incomplete(
                            statement.span,
                            "static module Result flow has a callable-only exit",
                        ));
                    }
                    let mut state = path.state;
                    let mut value = path.value;
                    if let Some(context) = &context {
                        value = engine.receive_annotation(value, context.written(), &state)?;
                    }
                    engine.bind_simple(&binding.pattern, value, &mut state)?;
                    state.globals = state.env.clone();
                    next.push(state);
                }
            }
            states = next;
        }
        for state in states {
            let pending = state
                .duties
                .values()
                .any(|duty| duty.owner == 0 && !duty.inspected);
            if !pending {
                continue;
            }
            let mut published = BTreeSet::new();
            for value in state.globals.values() {
                engine.roots(value, &mut published, module_span)?;
            }
            for (&id, duty) in &state.duties {
                if duty.owner != 0 || duty.inspected {
                    continue;
                }
                if published.contains(&id) {
                    return Err(incomplete(
                        duty.span,
                        "pending static Result publication requires a runtime inspection receipt",
                    ));
                }
                if state.unproved_path {
                    return Err(incomplete(
                        duty.span,
                        "static Result duty remains on a path whose feasibility is not established",
                    ));
                }
                return Err(unhandled(duty.span, module_span));
            }
        }
        Ok(())
    })();
    if let Err(problem) = result {
        valid = false;
        report(problem, output);
    }
    valid
}

fn unhandled(producer: Span, span: Span) -> Problem {
    Problem {
        failure: Box::new(Failure::Diagnostic(
            "E0720",
            "a static Result producer is neither inspected nor transferred on this normal exit"
                .into(),
        )),
        span,
        producer: Some(producer),
    }
}
fn report(problem: Problem, output: &mut Evaluation) {
    let index = output.diagnostics.len();
    output.failure(*problem.failure, problem.span);
    if let Some(producer) = problem.producer
        && let Some(diagnostic) = output.diagnostics.get_mut(index)
    {
        use ril_compiler_core::diagnostic::{Cause, CauseId};
        diagnostic.causes = vec![
            Cause {
                id: CauseId(0),
                span: Some(producer),
                description: "static Result producer created on this path".into(),
                parents: vec![],
            },
            Cause {
                id: CauseId(1),
                span: Some(problem.span),
                description:
                    "normal exit has no reached tag inspection or returned alias for this producer"
                        .into(),
                parents: vec![CauseId(0)],
            },
        ];
    }
}

impl Engine<'_> {
    fn descend<T>(
        &mut self,
        span: Span,
        action: impl FnOnce(&mut Self) -> std::result::Result<T, Problem>,
    ) -> std::result::Result<T, Problem> {
        if self.depth == 128 {
            return Err(incomplete(
                span,
                "static Result proof exceeds its traversal stack allowance",
            ));
        }
        self.depth += 1;
        let result = action(self);
        self.depth -= 1;
        result
    }
    fn step(&mut self, span: Span) -> std::result::Result<(), Problem> {
        self.work = self
            .work
            .checked_add(1)
            .ok_or_else(|| incomplete(span, "static Result proof work limit"))?;
        if self.work > 20_000 {
            return Err(incomplete(span, "static Result proof path allowance"));
        }
        Ok(())
    }
    fn owner(&mut self, span: Span) -> std::result::Result<u32, Problem> {
        let id = self.next_owner;
        self.next_owner = id
            .checked_add(1)
            .ok_or_else(|| incomplete(span, "static Result scope identity limit"))?;
        Ok(id)
    }
    fn boolean(&mut self, span: Span) -> std::result::Result<u32, Problem> {
        let id = self.next_boolean;
        self.next_boolean = id
            .checked_add(1)
            .ok_or_else(|| incomplete(span, "static Result predicate identity limit"))?;
        Ok(id)
    }
    fn producer(
        &mut self,
        state: &mut State,
        span: Span,
        owner: u32,
    ) -> std::result::Result<u32, Problem> {
        let id = self.next_producer;
        self.next_producer = id
            .checked_add(1)
            .ok_or_else(|| incomplete(span, "static Result producer identity limit"))?;
        state.duties.insert(
            id,
            Duty {
                owner,
                span,
                inspected: false,
            },
        );
        Ok(id)
    }
    fn types(state: &State) -> Env {
        let mut types = state.bound_scope.values.clone();
        types.extend(
            state
                .env
                .iter()
                .map(|(name, value)| (name.clone(), value.ty.clone())),
        );
        types
    }
    fn typer<'e>(evaluator: &'e Evaluator, state: &State) -> Typer<'e> {
        Typer::with_bound_environment(evaluator, None, state.bound_scope.clone())
    }
    fn ty(&self, expr: &Expr, state: &State) -> std::result::Result<Ty, Problem> {
        self.ty_expected(expr, state, None)
    }
    fn ty_expected(
        &self,
        expr: &Expr,
        state: &State,
        context: Option<&ResultContext>,
    ) -> std::result::Result<Ty, Problem> {
        at(
            self.metadata_typer(state).expr_result_expected(
                expr,
                &mut Self::types(state),
                context.map(ResultContext::ordinary),
                context,
            ),
            expr.span,
        )
    }
    fn seed(
        &mut self,
        ty: &Ty,
        state: &mut State,
        span: Span,
        owner: u32,
    ) -> std::result::Result<Value, Problem> {
        let shape = match ty {
            Ty::Bool => Shape::BoolSymbol {
                id: self.boolean(span)?,
                positive: true,
            },
            Ty::Result(ok, error) => Shape::Result {
                id: self.producer(state, span, owner)?,
                tag: None,
                ok: Box::new(self.seed(ok, state, span, owner)?),
                error: Box::new(self.seed(error, state, span, owner)?),
            },
            Ty::Tuple(items) => Shape::Tuple(
                items
                    .iter()
                    .map(|ty| self.seed(ty, state, span, owner))
                    .collect::<std::result::Result<_, _>>()?,
            ),
            Ty::Record(fields) => Shape::Record(
                fields
                    .iter()
                    .map(|(name, (_, ty))| Ok((name.clone(), self.seed(ty, state, span, owner)?)))
                    .collect::<std::result::Result<_, Problem>>()?,
            ),
            Ty::Optional(inner) => Shape::Optional {
                tag: None,
                choice: Some(self.boolean(span)?),
                payload: Box::new(self.seed(inner, state, span, owner)?),
            },
            Ty::Array(inner, Some(length)) if *length <= 64 => Shape::Array(
                (0..*length)
                    .map(|_| self.seed(inner, state, span, owner))
                    .collect::<std::result::Result<_, _>>()?,
            ),
            Ty::Array(inner, _) if contains_result_type(inner) => {
                return Err(incomplete(
                    span,
                    "static Result collection parameter requires quantified member coverage",
                ));
            }
            Ty::Callable(..) => Shape::Callable(Rc::new(Callable::Unknown)),
            Ty::Generic(_) => {
                let view = Self::typer(self.evaluator, state)
                    .bound_view(ty, &state.bound_scope)
                    .cloned();
                if let Some(view) = view {
                    self.descend(span, |engine| {
                        let fields = view
                            .fields
                            .iter()
                            .map(|(name, field)| {
                                Ok((name.clone(), engine.seed(&field.ty, state, span, owner)?))
                            })
                            .collect::<std::result::Result<_, Problem>>()?;
                        Ok(Shape::BoundRecord {
                            fields,
                            open: view.row.is_some(),
                        })
                    })?
                } else {
                    Shape::Unknown
                }
            }
            Ty::Unknown | Ty::Infer => Shape::Unknown,
            _ => Shape::Plain,
        };
        Ok(Value {
            source_type: None,
            ty: ty.clone(),
            shape,
        })
    }
    fn roots(
        &self,
        value: &Value,
        output: &mut BTreeSet<u32>,
        span: Span,
    ) -> std::result::Result<(), Problem> {
        match &value.shape {
            Shape::Result { id, ok, error, .. } => {
                output.insert(*id);
                self.roots(ok, output, span)?;
                self.roots(error, output, span)?;
            }
            Shape::Tuple(items) | Shape::Array(items) => {
                for item in items {
                    self.roots(item, output, span)?;
                }
            }
            Shape::Map(items) => {
                for (key, value) in items {
                    self.roots(key, output, span)?;
                    self.roots(value, output, span)?;
                }
            }
            Shape::BoundRecord { open: true, .. } => {
                return Err(incomplete(
                    span,
                    "static Result transport of an open bound requires its opaque row family",
                ));
            }
            Shape::Record(fields)
            | Shape::BoundRecord {
                fields,
                open: false,
            } => {
                for value in fields.values() {
                    self.roots(value, output, span)?;
                }
            }
            Shape::Optional { payload, .. } => self.roots(payload, output, span)?,
            Shape::Callable(callable) => self.callable_roots(callable, span)?,
            Shape::Unknown
                if contains_result_type(&value.ty)
                    || contains_generic_type(&value.ty)
                    || matches!(value.ty, Ty::Unknown) =>
            {
                return Err(incomplete(
                    span,
                    "static Result transport has an unresolved member shape",
                ));
            }
            _ => {}
        }
        Ok(())
    }
    fn callable_roots(&self, callable: &Callable, span: Span) -> std::result::Result<(), Problem> {
        match callable {
            Callable::Lambda { captured, .. }
                if captured.values().any(|value| {
                    !matches!(
                        value.shape,
                        Shape::Plain
                            | Shape::Bool(_)
                            | Shape::BoolSymbol { .. }
                            | Shape::Integer(_)
                            | Shape::Text(_)
                    )
                }) =>
            {
                Err(incomplete(
                    span,
                    "escaping static callable requires an exact Result capture graph",
                ))
            }
            Callable::View { target, .. } => self.callable_roots(target, span),
            _ => Ok(()),
        }
    }
    fn finish(
        &self,
        mut path: Path,
        span: Span,
        caller: Option<Caller>,
    ) -> std::result::Result<Path, Problem> {
        if path.exit == Exit::Abnormal {
            return Ok(path);
        }
        if matches!(path.exit, Exit::Next(_) | Exit::Last(_)) {
            return Err(loops::invalid_transfer(span));
        }
        let owner = path.state.owner;
        let pending = path
            .state
            .duties
            .values()
            .any(|duty| duty.owner == owner && !duty.inspected);
        let mut returned = BTreeSet::new();
        if pending {
            self.roots(&path.value, &mut returned, span)?;
        }
        for (&id, duty) in &path.state.duties {
            if duty.owner == owner && !duty.inspected && !returned.contains(&id) {
                if path.state.unproved_path {
                    return Err(incomplete(
                        duty.span,
                        "static Result duty remains on a path whose feasibility is not established",
                    ));
                }
                return Err(unhandled(duty.span, span));
            }
        }
        if let Some((parent, env, bound_scope)) = caller {
            for id in returned {
                let duty = path.state.duties.get_mut(&id).unwrap();
                if duty.owner == owner {
                    duty.owner = parent;
                }
            }
            path.state.owner = parent;
            path.state.env = env;
            path.state.bound_scope = bound_scope;
            path.exit = Exit::Normal;
        }
        Ok(path)
    }
    fn bind_simple(
        &self,
        pattern: &Pattern,
        value: Value,
        state: &mut State,
    ) -> std::result::Result<(), Problem> {
        let open_record = matches!(&value.shape, Shape::BoundRecord { open: true, .. });
        match (&pattern.kind, value.shape.clone()) {
            (PatternKind::Name(name), _) => {
                self.mask_const_bindings(state, &BTreeSet::from([name.clone()]), pattern.span)?;
                state.env.insert(name.clone(), value);
            }
            (PatternKind::Wildcard, _) => {}
            (PatternKind::Tuple(patterns), Shape::Tuple(items))
                if patterns.len() == items.len() =>
            {
                for (pattern, value) in patterns.iter().zip(items) {
                    self.bind_simple(pattern, value, state)?;
                }
            }
            (
                PatternKind::Record {
                    fields,
                    rest_binding,
                    ..
                },
                Shape::Record(mut values)
                | Shape::BoundRecord {
                    fields: mut values, ..
                },
            ) => {
                if open_record && rest_binding.is_some() {
                    return Err(incomplete(
                        pattern.span,
                        "static Result row binding requires an opaque remainder family",
                    ));
                }
                for field in fields {
                    let value = values.remove(&field.name).ok_or_else(|| {
                        incomplete(pattern.span, "static Result binding field absent")
                    })?;
                    self.bind_simple(&field.pattern, value, state)?;
                }
                if let Some(name) = rest_binding {
                    self.mask_const_bindings(state, &BTreeSet::from([name.clone()]), pattern.span)?;
                    state.env.insert(
                        name.clone(),
                        Value {
                            source_type: None,
                            ty: Ty::Record(
                                values
                                    .iter()
                                    .map(|(name, value)| (name.clone(), (false, value.ty.clone())))
                                    .collect(),
                            ),
                            shape: Shape::Record(values),
                        },
                    );
                }
            }
            _ => {
                return Err(incomplete(
                    pattern.span,
                    "static Result binding requires a proved product pattern",
                ));
            }
        }
        Ok(())
    }
    fn block(&mut self, block: &Block, state: State) -> Paths {
        self.block_expected(block, state, None)
    }
    fn block_expected(
        &mut self,
        block: &Block,
        state: State,
        context: Option<&ResultContext>,
    ) -> Paths {
        let mut paths = vec![Path::normal(state, Value::unit())];
        for (index, statement) in block.statements.iter().enumerate() {
            let mut next = vec![];
            for path in paths {
                if path.exit != Exit::Normal {
                    next.push(path);
                    continue;
                }
                match &statement.kind {
                    StmtKind::Binding(binding) => {
                        let binding_context =
                            self.annotation_context(binding.ty.as_ref(), &path.state)?;
                        for mut path in self.expr_expected(
                            &binding.value,
                            path.state,
                            binding_context.as_ref(),
                        )? {
                            if path.exit == Exit::Normal {
                                if let Some(ty) = &binding.ty {
                                    path.value =
                                        self.receive_annotation(path.value, ty, &path.state)?;
                                }
                                self.bind_simple(&binding.pattern, path.value, &mut path.state)?;
                                path.value = Value::unit();
                            }
                            next.push(path);
                        }
                    }
                    StmtKind::Expr {
                        expression,
                        terminated,
                    } => {
                        let context = if !terminated && index + 1 == block.statements.len() {
                            context
                        } else {
                            None
                        };
                        for mut path in self.expr_expected(expression, path.state, context)? {
                            if path.exit == Exit::Normal
                                && (*terminated || index + 1 != block.statements.len())
                            {
                                path.value = Value::unit();
                            }
                            next.push(path);
                        }
                    }
                    StmtKind::Function(_) | StmtKind::Type(_) => next.push(path),
                    _ => {
                        return Err(incomplete(
                            statement.span,
                            "static Result statement transfer is unavailable",
                        ));
                    }
                }
            }
            paths = next;
        }
        Ok(paths)
    }

    fn expr(&mut self, expr: &Expr, state: State) -> Paths {
        self.expr_expected(expr, state, None)
    }
    fn expr_expected(
        &mut self,
        expr: &Expr,
        state: State,
        context: Option<&ResultContext>,
    ) -> Paths {
        self.descend(expr.span, |engine| {
            let mut paths = engine.expr_inner(expr, state, context)?;
            for path in &mut paths {
                if path.exit == Exit::Normal {
                    path.value.source_type =
                        engine.expression_source(expr, &path.value, &path.state, context)?;
                }
            }
            Ok(paths)
        })
    }
    fn expr_inner(&mut self, expr: &Expr, state: State, context: Option<&ResultContext>) -> Paths {
        self.step(expr.span)?;
        match &expr.kind {
            ExprKind::Literal(Literal::Bool(value)) => {
                Ok(vec![Path::normal(state, Value::boolean(*value))])
            }
            ExprKind::Literal(Literal::Integer(text)) => Ok(vec![Path::normal(
                state,
                self.integer_literal(text, false, expr.span)?,
            )]),
            ExprKind::Literal(Literal::String(text)) => {
                let value = crate::lower::decode_text(&text[1..text.len() - 1])
                    .map_err(|_| incomplete(expr.span, "static Result proof string decoding"))?;
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty: Ty::String,
                        shape: Shape::Text(value),
                    },
                )])
            }
            ExprKind::Literal(_) | ExprKind::TypeValue(_) | ExprKind::KeyOf(_) => {
                let ty = self.ty(expr, &state)?;
                let shape = if let Ty::IntegerConstant(value) = ty {
                    Shape::Integer(value)
                } else {
                    Shape::Plain
                };
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape,
                    },
                )])
            }
            ExprKind::Name(_) | ExprKind::Path(_) => {
                let name = expression_name(expr).unwrap();
                if let Some(value) = state.env.get(&name).cloned() {
                    return Ok(vec![Path::normal(state, value)]);
                }
                let normalized = name.strip_prefix("Prelude::").unwrap_or(&name);
                if normalized == "None" {
                    return Ok(vec![Path::normal(
                        state,
                        Value {
                            source_type: None,
                            ty: Ty::Optional(Box::new(Ty::Infer)),
                            shape: Shape::Optional {
                                tag: Some(false),
                                choice: None,
                                payload: Box::new(Value::unit()),
                            },
                        },
                    )]);
                }
                let ty = if self.evaluator.functions.contains_key(&name) {
                    self.ty(expr, &state)?
                } else {
                    Ty::Unknown
                };
                let callable = if self.evaluator.functions.contains_key(&name) {
                    Callable::Named {
                        name,
                        explicit: vec![],
                        explicit_scope: None,
                    }
                } else {
                    Callable::Builtin(normalized.into())
                };
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Callable(Rc::new(callable)),
                    },
                )])
            }
            ExprKind::Generic { base, arguments } => {
                let name = expression_name(base).ok_or_else(|| {
                    incomplete(
                        expr.span,
                        "static generic callable requires its named declaration",
                    )
                })?;
                let function = self.evaluator.functions.get(&name).ok_or_else(|| {
                    incomplete(expr.span, "static generic callable declaration absent")
                })?;
                if arguments.len() > function.generics.len() {
                    return at(
                        Err(Failure::Diagnostic(
                            "E0340",
                            "too many explicit static arguments for the callable".into(),
                        )),
                        expr.span,
                    );
                }
                let typer = self.metadata_typer(&state);
                let mut explicit = Vec::with_capacity(arguments.len());
                let mut symbolic = false;
                for (syntax, parameter) in arguments.iter().zip(&function.generics) {
                    if at(const_int::parameter_sort(parameter), syntax.span)?
                        == bounds::StaticParameterSort::ConstInt
                    {
                        // A const argument is a value application, not Type
                        // syntax. Freeze its pure value/ID at creation so an
                        // ordinary same-spelled shadow cannot change it later.
                        let mut lexical = state.bound_scope.as_ref().clone();
                        lexical.values = Self::types(&state);
                        let selected =
                            at(typer.const_argument_source(syntax, &lexical), syntax.span)?;
                        symbolic |= selected.rigid;
                        explicit.push(selected.syntax);
                        continue;
                    }
                    if let Some(witness) = at(
                        typer.complete_source_syntax(syntax, &state.bound_scope),
                        syntax.span,
                    )? {
                        explicit.push(witness.syntax.clone());
                    } else {
                        symbolic = true;
                        explicit.push(syntax.clone());
                    }
                }
                let explicit_scope = symbolic.then(|| state.bound_scope.clone());
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty: Ty::Unknown,
                        shape: Shape::Callable(Rc::new(Callable::Named {
                            name,
                            explicit,
                            explicit_scope,
                        })),
                    },
                )])
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let contexts = items
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        let projection = if matches!(expr.kind, ExprKind::Tuple(_)) {
                            applications::ResultProjection::Tuple(index)
                        } else {
                            applications::ResultProjection::ArrayElement
                        };
                        self.project_context(context, projection, &state, expr.span)
                    })
                    .collect::<std::result::Result<Vec<_>, Problem>>()?;
                let (normal, mut exits) =
                    self.operands_expected(items.iter().collect(), state, &contexts)?;
                for (state, values) in normal {
                    let tuple = matches!(expr.kind, ExprKind::Tuple(_));
                    let ty = if tuple {
                        Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect())
                    } else {
                        Ty::Array(
                            Box::new(values.first().map_or(Ty::Infer, |value| value.ty.clone())),
                            Some(values.len()),
                        )
                    };
                    exits.push(Path::normal(
                        state,
                        Value {
                            source_type: None,
                            ty,
                            shape: if tuple {
                                Shape::Tuple(values)
                            } else {
                                Shape::Array(values)
                            },
                        },
                    ));
                }
                Ok(exits)
            }
            ExprKind::Map(items) => self.map_expression(items, state, expr.span, context),
            ExprKind::Record { members, .. } => {
                let declared = if let ExprKind::Record { ty, .. } = &expr.kind {
                    self.annotation_context(ty.as_ref(), &state)?
                } else {
                    None
                };
                let receiving = declared.as_ref().or(context);
                let contexts = members
                    .iter()
                    .map(|member| match member {
                        RecordMember::Field(field) => self.project_context(
                            receiving,
                            applications::ResultProjection::Record(field.name.clone()),
                            &state,
                            field.value.span,
                        ),
                        RecordMember::Spread(_) => Ok(None),
                    })
                    .collect::<std::result::Result<Vec<_>, Problem>>()?;
                let expressions = members
                    .iter()
                    .map(|member| match member {
                        RecordMember::Field(field) => &field.value,
                        RecordMember::Spread(value) => value,
                    })
                    .collect();
                let (normal, mut exits) = self.operands_expected(expressions, state, &contexts)?;
                for (state, values) in normal {
                    let mut fields = BTreeMap::new();
                    let mut explicit = BTreeMap::new();
                    for (member, value) in members.iter().zip(values) {
                        match member {
                            RecordMember::Field(field) => {
                                explicit.insert(field.name.clone(), value);
                            }
                            RecordMember::Spread(value_expr) => {
                                let Shape::Record(values) = value.shape else {
                                    return Err(incomplete(
                                        value_expr.span,
                                        "static Result spread requires an exact member graph",
                                    ));
                                };
                                fields.extend(values);
                            }
                        }
                    }
                    fields.extend(explicit);
                    let ty = Ty::Record(
                        fields
                            .iter()
                            .map(|(name, value)| (name.clone(), (false, value.ty.clone())))
                            .collect(),
                    );
                    let mut value = Value {
                        source_type: None,
                        ty,
                        shape: Shape::Record(fields),
                    };
                    if let ExprKind::Record {
                        ty: Some(syntax), ..
                    } = &expr.kind
                    {
                        value = self.receive_annotation(value, syntax, &state)?;
                    }
                    exits.push(Path::normal(state, value));
                }
                Ok(exits)
            }
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let mut output = vec![];
                for path in self.expr(base, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    let value = match path.value.shape {
                        Shape::Record(mut fields) | Shape::BoundRecord { mut fields, .. } => {
                            fields.remove(field)
                        }
                        Shape::Tuple(items) => field
                            .parse::<usize>()
                            .ok()
                            .and_then(|index| items.get(index).cloned()),
                        _ => None,
                    }
                    .ok_or_else(|| {
                        incomplete(
                            expr.span,
                            "static Result projection lacks an exact member graph",
                        )
                    })?;
                    output.push(Path::normal(path.state, value));
                }
                Ok(output)
            }
            ExprKind::Index { base, index, safe } => {
                let (normal, mut output) = self.operands(vec![base, index], state)?;
                for (state, values) in normal {
                    let [base, index] = values.as_slice() else {
                        unreachable!()
                    };
                    if matches!(&base.shape, Shape::Map(_)) {
                        let value = self.map_index(base, index, expr.span)?;
                        output.push(Path::normal(state, value));
                        continue;
                    }
                    let Shape::Array(items) = &base.shape else {
                        return Err(incomplete(
                            expr.span,
                            "static Result index requires a finite exact collection",
                        ));
                    };
                    let Shape::Integer(index) = index.shape else {
                        return Err(incomplete(
                            expr.span,
                            "static Result index requires an exact coordinate",
                        ));
                    };
                    let selected = usize::try_from(index)
                        .ok()
                        .and_then(|index| items.get(index))
                        .cloned();
                    if *safe {
                        let ty = Ty::Optional(Box::new(
                            selected
                                .as_ref()
                                .map_or(Ty::Infer, |value| value.ty.clone()),
                        ));
                        output.push(Path::normal(
                            state,
                            Value {
                                source_type: None,
                                ty,
                                shape: Shape::Optional {
                                    tag: Some(selected.is_some()),
                                    choice: None,
                                    payload: Box::new(selected.unwrap_or_else(Value::unit)),
                                },
                            },
                        ));
                    } else if let Some(value) = selected {
                        output.push(Path::normal(state, value));
                    } else {
                        output.push(Path {
                            state,
                            value: Value::unit(),
                            exit: Exit::Abnormal,
                        });
                    }
                }
                Ok(output)
            }
            ExprKind::Block(block) => {
                let env = state.env.clone();
                let scope = state.bound_scope.clone();
                let mut paths = self.block_expected(block, state, context)?;
                for path in &mut paths {
                    path.state.env = env.clone();
                    path.state.bound_scope = scope.clone();
                }
                Ok(paths)
            }
            ExprKind::Loop(body) => self.loop_flow(None, body, state, expr.span, context),
            ExprKind::While { condition, body } => {
                self.loop_flow(Some(condition), body, state, expr.span, None)
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => self.for_flow(iterable, pattern, body, state, expr.span),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut output = vec![];
                for path in self.expr(condition, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    for (state, truth) in truth_paths(path) {
                        if truth {
                            output.extend(self.expr_expected(then_branch, state, context)?);
                        } else if let Some(branch) = else_branch {
                            output.extend(self.expr_expected(branch, state, context)?);
                        } else {
                            output.push(Path::normal(state, Value::unit()));
                        }
                    }
                }
                Ok(output)
            }
            ExprKind::Is { value, pattern } => {
                let mut output = vec![];
                for path in self.expr(value, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    let env = path.state.env.clone();
                    let scope = path.state.bound_scope.clone();
                    for (mut state, truth) in self.pattern(pattern, &path.value, path.state)? {
                        state.env = env.clone();
                        state.bound_scope = scope.clone();
                        output.push(Path::normal(state, Value::boolean(truth)));
                    }
                }
                Ok(output)
            }
            ExprKind::Match { value, arms, .. } => {
                let mut output = vec![];
                for path in self.expr(value, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    let env = path.state.env.clone();
                    let scope = path.state.bound_scope.clone();
                    let subject = path.value;
                    let mut pending = vec![path.state];
                    for arm in arms {
                        let mut next = vec![];
                        for state in pending {
                            for (mut state, matched) in
                                self.pattern(&arm.pattern, &subject, state)?
                            {
                                if !matched {
                                    state.env = env.clone();
                                    state.bound_scope = scope.clone();
                                    next.push(state);
                                    continue;
                                }
                                let guarded = if let Some(guard) = &arm.guard {
                                    self.expr(guard, state)?
                                } else {
                                    vec![Path::normal(state, Value::boolean(true))]
                                };
                                for path in guarded {
                                    if path.exit != Exit::Normal {
                                        output.push(path);
                                        continue;
                                    }
                                    for (mut state, selected) in truth_paths(path) {
                                        if selected {
                                            for mut path in
                                                self.expr_expected(&arm.body, state, context)?
                                            {
                                                path.state.env = env.clone();
                                                path.state.bound_scope = scope.clone();
                                                output.push(path);
                                            }
                                        } else {
                                            state.env = env.clone();
                                            state.bound_scope = scope.clone();
                                            next.push(state);
                                        }
                                    }
                                }
                            }
                        }
                        pending = next;
                    }
                    if !pending.is_empty() {
                        return Err(incomplete(
                            expr.span,
                            "static Result match requires complete per-tag normal path coverage",
                        ));
                    }
                }
                Ok(output)
            }
            ExprKind::Unary { operator, operand } if operator == "!" => {
                let mut paths = self.expr(operand, state)?;
                for path in &mut paths {
                    if path.exit == Exit::Normal {
                        path.value = match path.value.shape {
                            Shape::Bool(value) => Value::boolean(!value),
                            Shape::BoolSymbol { id, positive } => Value {
                                source_type: None,
                                ty: Ty::Bool,
                                shape: Shape::BoolSymbol {
                                    id,
                                    positive: !positive,
                                },
                            },
                            _ => Value {
                                source_type: None,
                                ty: Ty::Bool,
                                shape: Shape::Plain,
                            },
                        };
                    }
                }
                Ok(paths)
            }
            ExprKind::Unary { operator, .. } if operator == "typeof" => Ok(vec![Path::normal(
                state,
                Value {
                    source_type: None,
                    ty: Ty::Meta,
                    shape: Shape::Plain,
                },
            )]),
            ExprKind::Unary { operator, operand }
                if operator == "-"
                    && matches!(operand.kind, ExprKind::Literal(Literal::Integer(_))) =>
            {
                let ExprKind::Literal(Literal::Integer(text)) = &operand.kind else {
                    unreachable!()
                };
                Ok(vec![Path::normal(
                    state,
                    self.integer_literal(text, true, expr.span)?,
                )])
            }
            ExprKind::Unary { operand, .. } => {
                let mut paths = self.expr(operand, state)?;
                for path in &mut paths {
                    if path.exit == Exit::Normal {
                        path.state.unproved_path = true;
                        path.value.shape = Shape::Plain;
                    }
                }
                Ok(paths)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "??" {
                    return self.optional_fallback(left, right, state, expr.span, context);
                }
                let mut output = vec![];
                for path in self.expr(left, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    if matches!(operator.as_str(), "&&" | "||") {
                        for (state, left) in truth_paths(path) {
                            if (operator == "&&" && !left) || (operator == "||" && left) {
                                output.push(Path::normal(state, Value::boolean(left)));
                            } else {
                                output.extend(self.expr(right, state)?);
                            }
                        }
                    } else {
                        let ty =
                            if matches!(operator.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") {
                                Ty::Bool
                            } else {
                                path.value.ty.clone()
                            };
                        let left = path.value;
                        for mut path in self.expr(right, path.state)? {
                            if path.exit == Exit::Normal {
                                let shape = if matches!(operator.as_str(), "==" | "!=") {
                                    comparison(&left, &path.value, operator == "!=")
                                } else {
                                    Shape::Plain
                                };
                                if ty != Ty::Bool {
                                    path.state.unproved_path = true;
                                }
                                path.value = Value {
                                    source_type: None,
                                    ty: ty.clone(),
                                    shape,
                                };
                            }
                            output.push(path);
                        }
                    }
                }
                Ok(output)
            }
            ExprKind::Lambda {
                parameters,
                body,
                return_type,
                ..
            } => {
                self.check_lambda(parameters, body, return_type.as_ref(), &state)?;
                let ty = self.ty_expected(expr, &state, context)?;
                let output = match &ty {
                    Ty::Callable(_, output, _) => output.as_ref().clone(),
                    _ => Ty::Unknown,
                };
                let captured = state.env.clone();
                let bound_scope = state.bound_scope.clone();
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Callable(Rc::new(Callable::Lambda {
                            parameters: parameters.clone(),
                            body: body.clone(),
                            captured,
                            bound_scope,
                            return_type: return_type.clone(),
                            output,
                        })),
                    },
                )])
            }
            ExprKind::Call { callee, arguments } => {
                let mut output = vec![];
                for path in self.expr(callee, state)? {
                    if path.exit != Exit::Normal {
                        output.push(path);
                        continue;
                    }
                    let Shape::Callable(callable) = path.value.shape else {
                        return Err(incomplete(
                            callee.span,
                            "static Result application has no selected callable",
                        ));
                    };
                    let prepared = self.prepare_contextual_call(
                        &callable,
                        arguments,
                        &path.state,
                        context,
                        expr.span,
                    )?;
                    let argument_contexts = self.argument_contexts(
                        &callable,
                        arguments,
                        &path.state,
                        prepared.as_ref(),
                        context,
                        expr.span,
                    )?;
                    let (normal, exits) = self.operands_expected(
                        arguments.iter().map(|argument| &argument.value).collect(),
                        path.state,
                        &argument_contexts,
                    )?;
                    output.extend(exits);
                    for (state, values) in normal {
                        output.extend(self.invoke_expected(
                            &callable,
                            arguments,
                            values,
                            state,
                            expr.span,
                            CallContext {
                                result: context,
                                prepared: prepared.as_ref(),
                            },
                        )?);
                    }
                }
                Ok(output)
            }
            ExprKind::Control {
                operation: ControlOperation::Return,
                value,
            } => {
                let return_context = self.return_context.clone();
                let mut paths = if let Some(value) = value {
                    self.expr_expected(value, state, return_context.as_ref())?
                } else {
                    vec![Path::normal(state, Value::unit())]
                };
                for path in &mut paths {
                    if path.exit == Exit::Normal {
                        path.exit = Exit::Return;
                    }
                }
                Ok(paths)
            }
            ExprKind::Control { operation, value }
                if matches!(operation, ControlOperation::Last | ControlOperation::Next) =>
            {
                self.loop_transfer(*operation, value.as_deref(), state, expr.span)
            }
            _ => Err(incomplete(
                expr.span,
                "static Result expression requires a separate complete transfer proof",
            )),
        }
    }

    fn operands(
        &mut self,
        expressions: Vec<&Expr>,
        state: State,
    ) -> std::result::Result<Operands, Problem> {
        let contexts = vec![None; expressions.len()];
        self.operands_expected(expressions, state, &contexts)
    }
    fn operands_expected(
        &mut self,
        expressions: Vec<&Expr>,
        state: State,
        contexts: &[Option<ResultContext>],
    ) -> std::result::Result<Operands, Problem> {
        let mut normal = vec![(state, vec![])];
        let mut exits = vec![];
        for (index, expression) in expressions.into_iter().enumerate() {
            let context = contexts.get(index).ok_or_else(|| {
                incomplete(
                    expression.span,
                    "static Result operand lacks its contextual position",
                )
            })?;
            let mut next = vec![];
            for (state, values) in normal {
                for path in self.expr_expected(expression, state, context.as_ref())? {
                    if path.exit == Exit::Normal {
                        let mut values = values.clone();
                        values.push(path.value);
                        next.push((path.state, values));
                    } else {
                        exits.push(path);
                    }
                }
            }
            normal = next;
        }
        Ok((normal, exits))
    }

    fn pattern(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        state: State,
    ) -> std::result::Result<Vec<(State, bool)>, Problem> {
        self.descend(pattern.span, |engine| {
            engine.pattern_inner(pattern, value, state)
        })
    }
    fn pattern_inner(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        mut state: State,
    ) -> std::result::Result<Vec<(State, bool)>, Problem> {
        self.step(pattern.span)?;
        match &pattern.kind {
            PatternKind::Wildcard => Ok(vec![(state, true)]),
            PatternKind::Name(name) => {
                self.mask_const_bindings(
                    &mut state,
                    &BTreeSet::from([name.clone()]),
                    pattern.span,
                )?;
                state.env.insert(name.clone(), value.clone());
                Ok(vec![(state, true)])
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                let tag = path.join("::");
                let tag = tag.strip_prefix("Prelude::").unwrap_or(&tag);
                let (known, wanted, payload) = match &value.shape {
                    Shape::Result {
                        id,
                        tag: known,
                        ok,
                        error,
                    } => {
                        let wanted = super::super::results::tag(path).ok_or_else(|| {
                            incomplete(
                                pattern.span,
                                "static Result tag has no canonical constructor",
                            )
                        })?;
                        state
                            .duties
                            .get_mut(id)
                            .ok_or_else(|| {
                                incomplete(pattern.span, "static Result tag test has no producer")
                            })?
                            .inspected = true;
                        (
                            state.tags.get(id).copied().or(*known),
                            wanted,
                            if wanted { ok.as_ref() } else { error.as_ref() },
                        )
                    }
                    Shape::Optional {
                        tag: known,
                        choice,
                        payload,
                    } if matches!(tag, "Some" | "None") => (
                        choice
                            .and_then(|id| state.booleans.get(&id).copied())
                            .or(*known),
                        tag == "Some",
                        payload.as_ref(),
                    ),
                    _ => {
                        return Err(incomplete(
                            pattern.span,
                            "static Result pattern needs a complete variant member graph",
                        ));
                    }
                };
                let mut output = vec![];
                if known != Some(wanted) {
                    let mut failed = state.clone();
                    match value.shape {
                        Shape::Result { id, .. } => {
                            failed.tags.insert(id, !wanted);
                        }
                        Shape::Optional {
                            choice: Some(id), ..
                        } => {
                            failed.booleans.insert(id, !wanted);
                        }
                        _ => {}
                    }
                    output.push((failed, false));
                }
                if known == Some(!wanted) {
                    return Ok(output);
                }
                if let Shape::Result { id, .. } = value.shape {
                    state.tags.insert(id, wanted);
                }
                if let Shape::Optional {
                    choice: Some(id), ..
                } = value.shape
                {
                    state.booleans.insert(id, wanted);
                }
                if arguments.is_empty() {
                    output.push((state, true));
                } else if arguments.len() == 1 {
                    output.extend(self.pattern(&arguments[0], payload, state)?);
                } else if let Shape::Tuple(items) = &payload.shape {
                    output.extend(
                        self.pattern_members(arguments.iter().zip(items).collect(), state)?,
                    );
                } else {
                    return Err(incomplete(
                        pattern.span,
                        "static Result pattern payload arity proof",
                    ));
                }
                Ok(output)
            }
            PatternKind::Tuple(patterns) => {
                if let Shape::Tuple(items) = &value.shape {
                    self.pattern_members(patterns.iter().zip(items).collect(), state)
                } else {
                    Err(incomplete(
                        pattern.span,
                        "static Result tuple pattern member graph",
                    ))
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                let values = match &value.shape {
                    Shape::Record(values) => values,
                    Shape::BoundRecord { fields, open } => {
                        if *open && rest_binding.is_some() {
                            return Err(incomplete(
                                pattern.span,
                                "static Result row pattern requires an opaque remainder family",
                            ));
                        }
                        fields
                    }
                    _ => {
                        return Err(incomplete(
                            pattern.span,
                            "static Result record pattern member graph",
                        ));
                    }
                };
                let members = fields
                    .iter()
                    .map(|field| {
                        values
                            .get(&field.name)
                            .map(|value| (&field.pattern, value))
                            .ok_or_else(|| {
                                incomplete(field.span, "static Result record member absent")
                            })
                    })
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                let mut paths = self.pattern_members(members, state)?;
                if let Some(name) = rest_binding {
                    for (state, matched) in &mut paths {
                        if *matched {
                            self.mask_const_bindings(
                                state,
                                &BTreeSet::from([name.clone()]),
                                pattern.span,
                            )?;
                            let values = values
                                .iter()
                                .filter(|(name, _)| {
                                    !fields.iter().any(|field| &field.name == *name)
                                })
                                .map(|(name, value)| (name.clone(), value.clone()))
                                .collect::<BTreeMap<_, _>>();
                            state.env.insert(
                                name.clone(),
                                Value {
                                    source_type: None,
                                    ty: Ty::Record(
                                        values
                                            .iter()
                                            .map(|(name, value)| {
                                                (name.clone(), (false, value.ty.clone()))
                                            })
                                            .collect(),
                                    ),
                                    shape: Shape::Record(values),
                                },
                            );
                        }
                    }
                }
                Ok(paths)
            }
            PatternKind::Alternative(patterns) => {
                let mut pending = vec![state];
                let mut output = vec![];
                for pattern in patterns {
                    let mut next = vec![];
                    for state in pending {
                        for (state, matched) in self.pattern(pattern, value, state)? {
                            if matched {
                                output.push((state, true));
                            } else {
                                next.push(state);
                            }
                        }
                    }
                    pending = next;
                }
                output.extend(pending.into_iter().map(|state| (state, false)));
                Ok(output)
            }
            PatternKind::Literal(Literal::Bool(expected)) => {
                Ok(truth_paths(Path::normal(state, value.clone()))
                    .into_iter()
                    .map(|(state, value)| (state, value == *expected))
                    .collect())
            }
            PatternKind::Literal(literal) => self.pattern(
                &Pattern {
                    kind: PatternKind::Value(Box::new(Expr {
                        kind: ExprKind::Literal(literal.clone()),
                        span: pattern.span,
                    })),
                    span: pattern.span,
                },
                value,
                state,
            ),
            PatternKind::Value(expected) => {
                let mut output = vec![];
                for path in self.expr(expected, state)? {
                    if path.exit != Exit::Normal {
                        return Err(incomplete(
                            pattern.span,
                            "static Result expected-value test with control exit requires an exit-aware pattern certificate",
                        ));
                    }
                    let shape = comparison(value, &path.value, false);
                    output.extend(truth_paths(Path::normal(
                        path.state,
                        Value {
                            source_type: None,
                            ty: Ty::Bool,
                            shape,
                        },
                    )));
                }
                Ok(output)
            }
            _ => Err(incomplete(
                pattern.span,
                "static Result pattern inspection rule is unavailable",
            )),
        }
    }
    fn pattern_members(
        &mut self,
        members: Vec<(&Pattern, &Value)>,
        state: State,
    ) -> std::result::Result<Vec<(State, bool)>, Problem> {
        let mut paths = vec![(state, true)];
        for (pattern, value) in members {
            let mut next = vec![];
            for (state, matched) in paths {
                if matched {
                    next.extend(self.pattern(pattern, value, state)?);
                } else {
                    next.push((state, false));
                }
            }
            paths = next;
        }
        Ok(paths)
    }

    fn invoke(
        &mut self,
        callable: &Callable,
        syntax: &[Argument],
        values: Vec<Value>,
        state: State,
        span: Span,
    ) -> Paths {
        self.invoke_expected(
            callable,
            syntax,
            values,
            state,
            span,
            CallContext::default(),
        )
    }
    fn invoke_expected(
        &mut self,
        callable: &Callable,
        syntax: &[Argument],
        values: Vec<Value>,
        state: State,
        span: Span,
        context: CallContext<'_>,
    ) -> Paths {
        self.descend(span, |engine| {
            engine.without_loop_targets(|engine| {
                engine.invoke_inner(callable, syntax, values, state, span, context)
            })
        })
    }
    fn invoke_inner(
        &mut self,
        callable: &Callable,
        syntax: &[Argument],
        values: Vec<Value>,
        mut state: State,
        span: Span,
        context: CallContext<'_>,
    ) -> Paths {
        match callable {
            Callable::View {
                target,
                parameters,
                output,
            } => {
                let plan = at(
                    application::StaticApplicationPlan::new(
                        parameters,
                        syntax.iter().map(|argument| argument.label.clone()),
                    ),
                    span,
                )?;
                let mut arranged = vec![];
                let mut positional = vec![];
                for slot in plan.slots {
                    let application::ArgumentSlot::Explicit(index) = slot else {
                        return Err(incomplete(
                            span,
                            "a static callable interface cannot recover source defaults",
                        ));
                    };
                    arranged.push(values[index].clone());
                    let mut argument = syntax[index].clone();
                    argument.label = None;
                    positional.push(argument);
                }
                let mut paths = self.invoke(target, &positional, arranged, state, span)?;
                for path in &mut paths {
                    if path.exit == Exit::Normal {
                        path.value = path.value.clone().with_type(output);
                    }
                }
                Ok(paths)
            }
            Callable::Builtin(name) => self.builtin(name, values, state, span),
            Callable::Unknown => Err(incomplete(
                span,
                "static Result callback requires an actual callable transfer contract",
            )),
            Callable::Named {
                name,
                explicit,
                explicit_scope,
            } => {
                if !self.global_functions.contains(name) {
                    return Err(incomplete(
                        span,
                        "static Result local named capture requires its lexical group transfer proof",
                    ));
                }
                if self.stack.contains(name) {
                    return Err(incomplete(
                        span,
                        "recursive static Result invocation requires a composable producer summary",
                    ));
                }
                let function =
                    self.evaluator.functions.get(name).cloned().ok_or_else(|| {
                        incomplete(span, "static Result named declaration absent")
                    })?;
                if explicit_scope
                    .as_ref()
                    .is_some_and(|scope| !Arc::ptr_eq(scope, &state.bound_scope))
                {
                    return Err(incomplete(
                        span,
                        "escaping symbolic static type arguments require their captured binder substitution",
                    ));
                }
                let caller = (state.owner, state.env.clone(), state.bound_scope.clone());
                let (owner, scope, contextual_types) = if let Some(prepared) = context.prepared {
                    if prepared.name != *name || !Arc::ptr_eq(&prepared.caller, &state.bound_scope)
                    {
                        return Err(incomplete(
                            span,
                            "static Result prepared invocation changed its lexical source",
                        ));
                    }
                    (
                        prepared.owner,
                        prepared.scope.clone(),
                        prepared.contextual_types.clone(),
                    )
                } else {
                    let owner = self.owner(span)?;
                    let (scope, contextual_types) = at(
                        self.metadata_typer(&state).named_application_scope_at(
                            &function,
                            explicit,
                            syntax,
                            &mut Self::types(&state),
                            applications::ExpectedResult {
                                ordinary: context.result.map(ResultContext::ordinary),
                                source: context.result,
                            },
                            u64::from(owner),
                        ),
                        span,
                    )?;
                    (owner, Arc::new(scope), contextual_types)
                };
                if values.len() != contextual_types.len() {
                    return Err(incomplete(
                        span,
                        "static Result prepared argument type arity changed",
                    ));
                }
                let values = values
                    .into_iter()
                    .zip(contextual_types)
                    .map(|(value, ty)| {
                        if value.ty == ty {
                            Ok(value)
                        } else {
                            value.contextual_type(&ty, span)
                        }
                    })
                    .collect::<std::result::Result<Vec<_>, Problem>>()?;
                state.bound_scope = scope;
                state.env = state.globals.clone();
                self.seed_const_bindings(&mut state, function.span)?;
                state.owner = owner;
                self.stack.push(name.clone());
                let result = (|| {
                    let return_context = self.callable_return_context(
                        function.return_type.as_ref(),
                        &function.parameters,
                        &state,
                    )?;
                    self.with_return_context(return_context.clone(), |engine| {
                        let bound =
                            engine.parameters(&function.parameters, syntax, values, state, span)?;
                        let mut output = vec![];
                        for path in bound {
                            let paths = if path.exit == Exit::Normal {
                                let Some(body) = &function.body else {
                                    return Err(incomplete(
                                        span,
                                        "static Result callable body absent",
                                    ));
                                };
                                engine.block_expected(body, path.state, return_context.as_ref())?
                            } else {
                                vec![path]
                            };
                            for mut path in paths {
                                if let Some(syntax) = &function.return_type {
                                    path.value = engine.receive_annotation(
                                        path.value,
                                        syntax,
                                        &path.state,
                                    )?;
                                }
                                output.push(engine.finish(
                                    path,
                                    function.span,
                                    Some(caller.clone()),
                                )?);
                            }
                        }
                        Ok(output)
                    })
                })();
                self.stack.pop();
                result
            }
            Callable::Lambda {
                parameters,
                body,
                captured,
                bound_scope,
                return_type,
                output: expected,
            } => {
                let caller = (state.owner, state.env.clone(), state.bound_scope.clone());
                state.env = captured.clone();
                state.bound_scope = bound_scope.clone();
                state.owner = self.owner(span)?;
                let return_context =
                    self.callable_return_context(return_type.as_ref(), parameters, &state)?;
                self.with_return_context(return_context.clone(), |engine| {
                    let bound = engine.parameters(parameters, syntax, values, state, span)?;
                    let mut output = vec![];
                    for path in bound {
                        let paths = if path.exit == Exit::Normal {
                            engine.expr_expected(body, path.state, return_context.as_ref())?
                        } else {
                            vec![path]
                        };
                        for mut path in paths {
                            if let Some(syntax) = return_type {
                                path.value =
                                    engine.receive_annotation(path.value, syntax, &path.state)?;
                            } else if path.value.ty != *expected {
                                path.value = path.value.with_type(expected);
                            }
                            output.push(engine.finish(path, span, Some(caller.clone()))?);
                        }
                    }
                    Ok(output)
                })
            }
        }
    }
    fn parameters(
        &mut self,
        parameters: &[Parameter],
        syntax: &[Argument],
        values: Vec<Value>,
        mut state: State,
        span: Span,
    ) -> Paths {
        let specs = parameters
            .iter()
            .map(application::ParameterSpec::from)
            .collect::<Vec<_>>();
        let plan = at(
            application::StaticApplicationPlan::new(
                &specs,
                syntax.iter().map(|argument| argument.label.clone()),
            ),
            span,
        )?;
        for parameter in parameters {
            let mut names = BTreeSet::new();
            application::binding_names(&parameter.pattern, &mut names);
            for name in names {
                state.env.remove(&name);
            }
        }
        let mut paths = vec![Path::normal(state, Value::unit())];
        for (parameter, slot) in parameters.iter().zip(plan.slots) {
            let mut next = vec![];
            for path in paths {
                if path.exit != Exit::Normal {
                    next.push(path);
                    continue;
                }
                let inputs = match slot {
                    application::ArgumentSlot::Explicit(index) => {
                        vec![Path::normal(path.state, values[index].clone())]
                    }
                    application::ArgumentSlot::Default => {
                        let context =
                            self.annotation_context(parameter.ty.as_ref(), &path.state)?;
                        self.expr_expected(
                            parameter.default.as_ref().unwrap(),
                            path.state,
                            context.as_ref(),
                        )?
                    }
                };
                for mut path in inputs {
                    if path.exit == Exit::Normal {
                        if let Some(syntax) = &parameter.ty {
                            path.value =
                                self.receive_annotation(path.value, syntax, &path.state)?;
                        }
                        self.bind_simple(&parameter.pattern, path.value, &mut path.state)?;
                        path.value = Value::unit();
                    }
                    next.push(path);
                }
            }
            paths = next;
        }
        Ok(paths)
    }
    fn check_lambda(
        &mut self,
        parameters: &[Parameter],
        body: &Expr,
        return_type: Option<&TypeExpr>,
        state: &State,
    ) -> std::result::Result<(), Problem> {
        self.descend(body.span, |engine| {
            engine.without_loop_targets(|engine| {
                engine.check_lambda_inner(parameters, body, return_type, state)
            })
        })
    }
    fn check_lambda_inner(
        &mut self,
        parameters: &[Parameter],
        body: &Expr,
        return_type: Option<&TypeExpr>,
        state: &State,
    ) -> std::result::Result<(), Problem> {
        let mut state = state.clone();
        state.owner = self.owner(body.span)?;
        let types = Self::types(&state);
        let context = self.callable_return_context(return_type, parameters, &state)?;
        self.with_return_context(context.clone(), |engine| {
            for path in engine.universal_parameters(parameters, state, types)? {
                let paths = if path.exit == Exit::Normal {
                    engine.expr_expected(body, path.state, context.as_ref())?
                } else {
                    vec![path]
                };
                for path in paths {
                    engine.finish(path, body.span, None)?;
                }
            }
            Ok(())
        })
    }
    fn universal_parameters(
        &mut self,
        parameters: &[Parameter],
        mut state: State,
        mut types: Env,
    ) -> Paths {
        let typer = Self::typer(self.evaluator, &state);
        for parameter in parameters {
            let mut names = BTreeSet::new();
            application::binding_names(&parameter.pattern, &mut names);
            for name in names {
                state.env.remove(&name);
            }
        }
        let mut paths = vec![Path::normal(state, Value::unit())];
        for parameter in parameters {
            let ty = at(
                parameter
                    .ty
                    .as_ref()
                    .map_or(Ok(Ty::Unknown), |ty| typer.ty(ty, &types)),
                parameter.span,
            )?;
            at(
                typer.bind(&parameter.pattern, ty.clone(), &mut types),
                parameter.span,
            )?;
            let mut next = vec![];
            for path in paths {
                if path.exit != Exit::Normal {
                    next.push(path);
                    continue;
                }
                let mut provided = path.state.clone();
                let mut value = self.seed(&ty, &mut provided, parameter.span, u32::MAX)?;
                if let Some(syntax) = &parameter.ty {
                    value = self.receive_annotation(value, syntax, &provided)?;
                }
                self.bind_simple(&parameter.pattern, value, &mut provided)?;
                next.push(Path::normal(provided, Value::unit()));
                if let Some(default) = &parameter.default {
                    let context = self.annotation_context(parameter.ty.as_ref(), &path.state)?;
                    for mut path in self.expr_expected(default, path.state, context.as_ref())? {
                        if path.exit == Exit::Normal {
                            self.bind_simple(&parameter.pattern, path.value, &mut path.state)?;
                            path.value = Value::unit();
                        }
                        next.push(path);
                    }
                }
            }
            paths = next;
        }
        Ok(paths)
    }
    fn builtin(&mut self, name: &str, values: Vec<Value>, mut state: State, span: Span) -> Paths {
        match name {
            "Ok" | "Err" => {
                let payload = match values.len() {
                    0 => Value::unit(),
                    1 => values.into_iter().next().unwrap(),
                    _ => Value {
                        source_type: None,
                        ty: Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect()),
                        shape: Shape::Tuple(values),
                    },
                };
                let success = name == "Ok";
                let owner = state.owner;
                let id = self.producer(&mut state, span, owner)?;
                let (ok, error) = if success {
                    (payload, Value::unit())
                } else {
                    (Value::unit(), payload)
                };
                let ty = Ty::Result(Box::new(ok.ty.clone()), Box::new(error.ty.clone()));
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Result {
                            id,
                            tag: Some(success),
                            ok: Box::new(ok),
                            error: Box::new(error),
                        },
                    },
                )])
            }
            "Some" => {
                let payload = match values.len() {
                    0 => Value::unit(),
                    1 => values.into_iter().next().unwrap(),
                    _ => Value {
                        source_type: None,
                        ty: Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect()),
                        shape: Shape::Tuple(values),
                    },
                };
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty: Ty::Optional(Box::new(payload.ty.clone())),
                        shape: Shape::Optional {
                            tag: Some(true),
                            choice: None,
                            payload: Box::new(payload),
                        },
                    },
                )])
            }
            "assert" => {
                let value = values
                    .into_iter()
                    .next()
                    .ok_or_else(|| incomplete(span, "static Result assertion lacks a condition"))?;
                Ok(truth_paths(Path::normal(state, value))
                    .into_iter()
                    .map(|(state, truth)| Path {
                        state,
                        value: Value::unit(),
                        exit: if truth { Exit::Normal } else { Exit::Abnormal },
                    })
                    .collect())
            }
            "len" => {
                let [value] = values.as_slice() else {
                    return Err(incomplete(
                        span,
                        "static Result length query has no single source",
                    ));
                };
                // This is the scalar value of an actual language query on a
                // finite graph. It does not change its array type, produce a
                // fixed-dimension witness, or inspect any member's Result.
                let count = match &value.shape {
                    Shape::Array(items) => Some(items.len()),
                    Shape::Map(items) => Some(items.len()),
                    _ => None,
                };
                let shape = if let Some(count) = count {
                    let count = i128::try_from(count)
                        .map_err(|_| incomplete(span, "static Result length exceeds target int"))?;
                    let maximum = if self.evaluator.layout.pointer_bits == 32 {
                        i128::from(i32::MAX)
                    } else {
                        i128::from(i64::MAX)
                    };
                    if count > maximum {
                        return Err(incomplete(span, "static Result length exceeds target int"));
                    }
                    Shape::Integer(count)
                } else {
                    Shape::Plain
                };
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty: Ty::Number("int".into()),
                        shape,
                    },
                )])
            }
            "String::byte_len" | "byte_size" => Ok(vec![Path::normal(
                state,
                Value {
                    source_type: None,
                    ty: Ty::Number("int".into()),
                    shape: Shape::Plain,
                },
            )]),
            "Array::reverse" => {
                let Some(Value {
                    shape: Shape::Array(mut items),
                    ty,
                    ..
                }) = values.into_iter().next()
                else {
                    return Err(incomplete(
                        span,
                        "static Result reverse requires an exact collection",
                    ));
                };
                items.reverse();
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Array(items),
                    },
                )])
            }
            "Array::concat" => {
                let mut iter = values.into_iter();
                let Some(Value {
                    shape: Shape::Array(mut left),
                    ..
                }) = iter.next()
                else {
                    return Err(incomplete(
                        span,
                        "static Result concat needs exact collections",
                    ));
                };
                let Some(Value {
                    shape: Shape::Array(right),
                    ..
                }) = iter.next()
                else {
                    return Err(incomplete(
                        span,
                        "static Result concat needs exact collections",
                    ));
                };
                left.extend(right);
                let ty = Ty::Array(
                    Box::new(left.first().map_or(Ty::Infer, |value| value.ty.clone())),
                    Some(left.len()),
                );
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Array(left),
                    },
                )])
            }
            "Array::first" | "Array::get" => {
                let index = if name == "Array::first" {
                    0
                } else {
                    let Some(Value {
                        shape: Shape::Integer(index),
                        ..
                    }) = values.get(1)
                    else {
                        return Err(incomplete(
                            span,
                            "static Result Array::get requires an exact index",
                        ));
                    };
                    *index
                };
                let Some(Value {
                    shape: Shape::Array(items),
                    ..
                }) = values.first()
                else {
                    return Err(incomplete(
                        span,
                        "static Result Array::get requires an exact collection",
                    ));
                };
                let value = usize::try_from(index)
                    .ok()
                    .and_then(|index| items.get(index))
                    .cloned();
                let ty = Ty::Optional(Box::new(
                    value.as_ref().map_or(Ty::Infer, |value| value.ty.clone()),
                ));
                Ok(vec![Path::normal(
                    state,
                    Value {
                        source_type: None,
                        ty,
                        shape: Shape::Optional {
                            tag: Some(value.is_some()),
                            choice: None,
                            payload: Box::new(value.unwrap_or_else(Value::unit)),
                        },
                    },
                )])
            }
            name if name.starts_with("String::") => {
                // Listed String operations have ordinary non-Result output.
                if !builtins::static_builtin(name) {
                    return Err(incomplete(
                        span,
                        "static Result builtin contract is unavailable",
                    ));
                }
                let ty = match name {
                    "String::contains" | "String::starts_with" | "String::ends_with" => Ty::Bool,
                    "String::split" | "String::lines" => Ty::Array(Box::new(Ty::String), None),
                    "String::scalars" => Ty::Array(Box::new(Ty::Number("u32".into())), None),
                    "String::utf8" => Ty::Bytes,
                    "String::find" | "String::byte_offset" | "String::scalar_offset" => {
                        Ty::Optional(Box::new(Ty::Number("int".into())))
                    }
                    "String::scalar_at" => Ty::Optional(Box::new(Ty::Number("u32".into()))),
                    "String::slice" => Ty::Optional(Box::new(Ty::String)),
                    _ => Ty::String,
                };
                state.unproved_path = true;
                let value = self.seed(&ty, &mut state, span, u32::MAX)?;
                Ok(vec![Path::normal(state, value)])
            }
            _ => Err(incomplete(
                span,
                "static Result builtin lacks a complete producer/member transfer contract",
            )),
        }
    }
}

fn truth_paths(mut path: Path) -> Vec<(State, bool)> {
    match path.value.shape {
        Shape::Bool(value) => vec![(path.state, value)],
        Shape::BoolSymbol { id, positive } => {
            if let Some(value) = path.state.booleans.get(&id).copied() {
                return vec![(path.state, value == positive)];
            }
            let mut yes = path.state.clone();
            yes.booleans.insert(id, positive);
            path.state.booleans.insert(id, !positive);
            vec![(yes, true), (path.state, false)]
        }
        _ => {
            path.state.unproved_path = true;
            vec![(path.state.clone(), true), (path.state, false)]
        }
    }
}
fn comparison(left: &Value, right: &Value, negated: bool) -> Shape {
    match (&left.shape, &right.shape) {
        (Shape::BoolSymbol { id, positive }, Shape::Bool(value))
        | (Shape::Bool(value), Shape::BoolSymbol { id, positive }) => Shape::BoolSymbol {
            id: *id,
            positive: (*positive == *value) != negated,
        },
        (
            Shape::BoolSymbol {
                id: a,
                positive: ap,
            },
            Shape::BoolSymbol {
                id: b,
                positive: bp,
            },
        ) if a == b => Shape::Bool((ap == bp) != negated),
        _ => equal_values(left, right).map_or(Shape::Plain, |equal| Shape::Bool(equal != negated)),
    }
}
fn equal_values(left: &Value, right: &Value) -> Option<bool> {
    match (&left.shape, &right.shape) {
        (Shape::Bool(a), Shape::Bool(b)) => Some(a == b),
        (Shape::Integer(a), Shape::Integer(b)) => Some(a == b),
        (Shape::Text(a), Shape::Text(b)) => Some(a == b),
        (Shape::Plain, Shape::Plain) if left.ty == Ty::Unit && right.ty == Ty::Unit => Some(true),
        (
            Shape::Result {
                tag: Some(a),
                ok: ao,
                error: ae,
                ..
            },
            Shape::Result {
                tag: Some(b),
                ok: bo,
                error: be,
                ..
            },
        ) => {
            if a != b {
                Some(false)
            } else if *a {
                equal_values(ao, bo)
            } else {
                equal_values(ae, be)
            }
        }
        (
            Shape::Optional {
                tag: Some(a),
                payload: av,
                ..
            },
            Shape::Optional {
                tag: Some(b),
                payload: bv,
                ..
            },
        ) => {
            if a != b {
                Some(false)
            } else if !a {
                Some(true)
            } else {
                equal_values(av, bv)
            }
        }
        (Shape::Tuple(a), Shape::Tuple(b)) | (Shape::Array(a), Shape::Array(b)) => {
            if a.len() != b.len() {
                return Some(false);
            }
            let mut result = true;
            for (a, b) in a.iter().zip(b) {
                result &= equal_values(a, b)?;
            }
            Some(result)
        }
        _ => None,
    }
}
fn known_global(value: &mut Value, actual: &StaticValue) {
    match (&mut value.shape, actual) {
        (shape, StaticValue::Bool(value)) => *shape = Shape::Bool(*value),
        (shape, StaticValue::Integer(value) | StaticValue::TypedInteger(value, ..)) => {
            *shape = Shape::Integer(*value)
        }
        (shape, StaticValue::BigInteger(value)) => {
            if let Some(value) = num_traits::ToPrimitive::to_i128(value) {
                *shape = Shape::Integer(value);
            }
        }
        (shape, StaticValue::String(value)) => *shape = Shape::Text(value.clone()),
        (Shape::Result { tag, ok, error, .. }, StaticValue::Result(produced)) => {
            *tag = Some(produced.success);
            known_global(if produced.success { ok } else { error }, &produced.payload);
        }
        (Shape::Optional { tag, payload, .. }, StaticValue::Variant(name, items, _)) => {
            *tag = Some(name.ends_with("::Some"));
            if let Some(item) = items.first() {
                known_global(payload, item);
            }
        }
        (Shape::Tuple(values), StaticValue::Tuple(items))
        | (Shape::Array(values), StaticValue::Array(items)) => {
            for (value, actual) in values.iter_mut().zip(items.iter()) {
                known_global(value, actual);
            }
        }
        (
            Shape::Record(values) | Shape::BoundRecord { fields: values, .. },
            StaticValue::Record(items),
        ) => {
            for (name, value) in values {
                if let Some(actual) = items.get(name) {
                    known_global(value, actual);
                }
            }
        }
        (Shape::Map(values), StaticValue::Map(items)) => {
            for ((key, value), (actual_key, actual_value)) in values.iter_mut().zip(items.iter()) {
                known_global(key, actual_key);
                known_global(value, actual_value);
            }
        }
        _ => {}
    }
}

fn relevant(program: &Program) -> bool {
    program
        .statements
        .iter()
        .any(|statement| match &statement.kind {
            StmtKind::Binding(binding) if binding.is_meta => expr_relevant(&binding.value),
            StmtKind::Function(function) if function.is_meta => function_relevant(function),
            StmtKind::Function(function) => {
                function.body.as_ref().is_some_and(runtime_meta_relevant)
            }
            StmtKind::Type(TypeDeclaration {
                value:
                    Some(TypeExpr {
                        kind: TypeKind::TypeFunction { body, .. },
                        ..
                    }),
                ..
            }) => expr_relevant(body),
            _ => statement_type_computation_relevant(statement),
        })
}
fn function_relevant(function: &Function) -> bool {
    function.return_type.as_ref().is_some_and(type_relevant)
        || function.parameters.iter().any(|parameter| {
            parameter.ty.as_ref().is_some_and(type_relevant)
                || parameter.default.as_ref().is_some_and(expr_relevant)
        })
        || function.body.as_ref().is_some_and(block_relevant)
}
fn runtime_meta_relevant(block: &Block) -> bool {
    block
        .statements
        .iter()
        .chain(&block.where_items)
        .any(|statement| match &statement.kind {
            StmtKind::Binding(binding) if binding.is_meta => expr_relevant(&binding.value),
            StmtKind::Function(function) if function.is_meta => function_relevant(function),
            StmtKind::Binding(binding) => {
                nested_meta(&binding.value)
                    || binding.fallback.as_ref().is_some_and(nested_meta)
                    || statement_type_computation_relevant(statement)
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                nested_meta(expression)
            }
            _ => statement_type_computation_relevant(statement),
        })
}
fn block_relevant(block: &Block) -> bool {
    block
        .statements
        .iter()
        .chain(&block.where_items)
        .any(|statement| match &statement.kind {
            StmtKind::Binding(binding) => {
                expr_relevant(&binding.value)
                    || binding.ty.as_ref().is_some_and(type_relevant)
                    || binding.fallback.as_ref().is_some_and(expr_relevant)
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                expr_relevant(expression)
            }
            StmtKind::Function(function) => function_relevant(function),
            StmtKind::Assignment { target, value, .. } => {
                expr_relevant(target) || expr_relevant(value)
            }
            StmtKind::Handler(arms) => arms
                .iter()
                .any(|arm| expr_relevant(&arm.operation) || expr_relevant(&arm.body)),
            _ => statement_type_computation_relevant(statement),
        })
}
fn type_relevant(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            path.last().is_some_and(|name| name == "Result") || arguments.iter().any(type_relevant)
        }
        TypeKind::Array { element, .. } | TypeKind::Optional(element) => type_relevant(element),
        TypeKind::Map { key, value } => type_relevant(key) || type_relevant(value),
        TypeKind::Tuple(items) => items.iter().any(type_relevant),
        TypeKind::Record { fields, row } => {
            fields.iter().any(|field| type_relevant(&field.ty))
                || row.as_ref().is_some_and(|row| type_relevant(row))
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .any(|parameter| parameter.ty.as_ref().is_some_and(type_relevant))
                || result.as_ref().is_some_and(|result| type_relevant(result))
        }
        _ => false,
    }
}
fn pattern_relevant(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Constructor {
            path, arguments, ..
        } => super::super::results::tag(path).is_some() || arguments.iter().any(pattern_relevant),
        PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
            items.iter().any(pattern_relevant)
        }
        PatternKind::Record { fields, .. } => {
            fields.iter().any(|field| pattern_relevant(&field.pattern))
        }
        PatternKind::Mode { pattern, .. } => pattern_relevant(pattern),
        PatternKind::Value(value) => expr_relevant(value),
        _ => false,
    }
}
fn expr_relevant(expr: &Expr) -> bool {
    match &expr.kind{
    ExprKind::Name(name)=>matches!(name.as_str(),"Ok"|"Err"|"Prelude::Ok"|"Prelude::Err"),
    ExprKind::Path(path)=>super::super::results::tag(path).is_some(),
    ExprKind::Tuple(items)|ExprKind::Array(items)=>items.iter().any(expr_relevant),
    ExprKind::Map(items)=>items.iter().any(|(key,value)|expr_relevant(key)||expr_relevant(value)),
    ExprKind::Record{ty,members,..}=>ty.as_ref().is_some_and(type_computation_relevant)||members.iter().any(|member|match member{RecordMember::Field(field)=>expr_relevant(&field.value),RecordMember::Spread(value)=>expr_relevant(value)}),
    ExprKind::Call{callee,arguments}=>expr_relevant(callee)||arguments.iter().any(|argument|expr_relevant(&argument.value)),
    ExprKind::If{condition,then_branch,else_branch}=>expr_relevant(condition)||expr_relevant(then_branch)||else_branch.as_ref().is_some_and(|branch|expr_relevant(branch)),
    ExprKind::Match{value,arms,..}=>expr_relevant(value)||arms.iter().any(|arm|pattern_relevant(&arm.pattern)||arm.guard.as_ref().is_some_and(expr_relevant)||expr_relevant(&arm.body)),
    ExprKind::Is{value,pattern}=>expr_relevant(value)||pattern_relevant(pattern),
    ExprKind::Binary{left,right,..}=>expr_relevant(left)||expr_relevant(right),
    ExprKind::Unary{operator,operand}=>operator!="typeof"&&expr_relevant(operand),
    ExprKind::Block(block)|ExprKind::Loop(block)=>block_relevant(block),
    ExprKind::While{condition,body}=>expr_relevant(condition)||block_relevant(body),
    ExprKind::For{iterable,pattern,body}=>expr_relevant(iterable)||pattern_relevant(pattern)||block_relevant(body),
    ExprKind::Lambda{parameters,body,return_type,..}=>parameters.iter().any(|parameter|parameter.ty.as_ref().is_some_and(type_relevant)||parameter.default.as_ref().is_some_and(expr_relevant))||return_type.as_ref().is_some_and(type_relevant)||expr_relevant(body),
    ExprKind::Control{value,..}=>value.as_ref().is_some_and(|value|expr_relevant(value)),
    ExprKind::Field{base,..}=>expr_relevant(base),
    ExprKind::ComputedField{base,key}=>expr_relevant(base)||expr_relevant(key),
    ExprKind::Index{base,index,..}=>expr_relevant(base)||expr_relevant(index),
    ExprKind::Interpolated(parts)=>parts.iter().any(|part|matches!(part,StringPart::Interpolation{expression,..}if expr_relevant(expression))),
    ExprKind::Generic{base,arguments}=>expr_relevant(base)||arguments.iter().any(type_computation_relevant),
    ExprKind::TypeValue(ty)|ExprKind::KeyOf(ty)=>type_computation_relevant(ty),
    ExprKind::Derive{base,recipe}=>base.as_ref().is_some_and(|value|expr_relevant(value))||expr_relevant(recipe),
    ExprKind::Range{start,end,..}=>start.as_ref().is_some_and(|value|expr_relevant(value))||end.as_ref().is_some_and(|value|expr_relevant(value)),
    ExprKind::Literal(_)|ExprKind::Accessor(_)|ExprKind::Ambient|ExprKind::Error=>false,
}
}

fn statement_type_computation_relevant(statement: &Stmt) -> bool {
    match &statement.kind {
        StmtKind::Binding(binding) => binding.ty.as_ref().is_some_and(type_computation_relevant),
        StmtKind::Type(declaration) => declaration
            .value
            .as_ref()
            .is_some_and(type_computation_relevant),
        StmtKind::Function(function) => {
            function
                .return_type
                .as_ref()
                .is_some_and(type_computation_relevant)
                || function
                    .parameters
                    .iter()
                    .any(|parameter| parameter.ty.as_ref().is_some_and(type_computation_relevant))
        }
        _ => false,
    }
}
fn type_computation_relevant(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
            arguments.iter().any(type_computation_relevant)
        }
        TypeKind::Optional(inner)
        | TypeKind::KeyOf(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Projection { base: inner, .. } => type_computation_relevant(inner),
        TypeKind::Array { length, element } => {
            length.as_ref().is_some_and(|value| expr_relevant(value))
                || type_computation_relevant(element)
        }
        TypeKind::Map { key, value }
        | TypeKind::KindArrow {
            parameter: key,
            result: value,
        } => type_computation_relevant(key) || type_computation_relevant(value),
        TypeKind::Record { fields, row } => {
            fields
                .iter()
                .any(|field| type_computation_relevant(&field.ty))
                || row
                    .as_ref()
                    .is_some_and(|row| type_computation_relevant(row))
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(|parameter| {
                parameter.ty.as_ref().is_some_and(type_computation_relevant)
                    || parameter.default.as_ref().is_some_and(expr_relevant)
            }) || result
                .as_ref()
                .is_some_and(|result| type_computation_relevant(result))
        }
        TypeKind::TypeFunction { body, .. } | TypeKind::Computation(body) => expr_relevant(body),
        TypeKind::ComputedProjection { base, key } => {
            type_computation_relevant(base) || expr_relevant(key)
        }
        TypeKind::Mapped { keys, value, .. } => {
            expr_relevant(keys) || type_computation_relevant(value)
        }
        TypeKind::Error => false,
    }
}
fn nested_meta(expr: &Expr) -> bool {
    match &expr.kind{
    ExprKind::Block(block)|ExprKind::Loop(block)=>runtime_meta_relevant(block),
    ExprKind::If{condition,then_branch,else_branch}=>nested_meta(condition)||nested_meta(then_branch)||else_branch.as_ref().is_some_and(|branch|nested_meta(branch)),
    ExprKind::Match{value,arms,..}=>nested_meta(value)||arms.iter().any(|arm|arm.guard.as_ref().is_some_and(nested_meta)||nested_meta(&arm.body)),
    ExprKind::Call{callee,arguments}=>nested_meta(callee)||arguments.iter().any(|argument|nested_meta(&argument.value)),
    ExprKind::Tuple(items)|ExprKind::Array(items)=>items.iter().any(nested_meta),
    ExprKind::Map(items)=>items.iter().any(|(key,value)|nested_meta(key)||nested_meta(value)),
    ExprKind::Record{members,..}=>members.iter().any(|member|match member{RecordMember::Field(field)=>nested_meta(&field.value),RecordMember::Spread(value)=>nested_meta(value)}),
    ExprKind::Binary{left,right,..}=>nested_meta(left)||nested_meta(right),
    ExprKind::Unary{operand,..}|ExprKind::Field{base:operand,..}=>nested_meta(operand),
    ExprKind::ComputedField{base,key}=>nested_meta(base)||nested_meta(key),
    ExprKind::Index{base,index,..}=>nested_meta(base)||nested_meta(index),
    ExprKind::While{condition,body}=>nested_meta(condition)||runtime_meta_relevant(body),
    ExprKind::For{iterable,body,..}=>nested_meta(iterable)||runtime_meta_relevant(body),
    ExprKind::Lambda{body,..}=>nested_meta(body),
    ExprKind::Control{value,..}=>value.as_ref().is_some_and(|value|nested_meta(value)),
    ExprKind::Interpolated(parts)=>parts.iter().any(|part|matches!(part,StringPart::Interpolation{expression,..}if nested_meta(expression))),
    _=>false,
}
}
