//! Pure compile-time evaluation. Unknown computations stay incomplete, and the
//! evaluation allowance is independent of run-time Div boundaries.
use ril_compiler_core::{
    diagnostic::{Diagnostic, Label, Severity},
    source::Span,
    target::TargetLayout,
};
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
mod recovery;

pub(crate) fn constructor_parameter_recoverable(
    syntax: &TypeExpr,
    parameter: &str,
    declarations: &BTreeMap<String, TypeDeclaration>,
) -> bool {
    recovery::recoverable_parameter(syntax, parameter, declarations, &mut BTreeSet::new(), 0)
}

mod alias_cycles;
mod budget;
pub use budget::DEFAULT_STATIC_BUDGET;
mod application;
mod array_construction;
mod builtins;
mod clone_work;

/// Admit an owned syntax copy using the shared exhaustive syntax visitor.
/// This consumes implementation work only, without entering a static root or
/// charging any language event.
pub(crate) fn charge_type_syntax_clone(syntax: &TypeExpr, work: &mut usize) -> Option<()> {
    let budget = budget::Budget::with_work(u64::try_from(*work).ok()?);
    let result = clone_work::type_syntax(&budget, syntax);
    *work = usize::try_from(budget.work_remaining()).ok()?;
    result.ok()
}
pub(crate) fn charge_parameter_syntax_clone(syntax: &Parameter, work: &mut usize) -> Option<()> {
    let budget = budget::Budget::with_work(u64::try_from(*work).ok()?);
    let result = clone_work::parameter(&budget, syntax);
    *work = usize::try_from(budget.work_remaining()).ok()?;
    result.ok()
}
pub(crate) mod committed_float;
pub(crate) mod const_nominal;
pub(crate) mod constants;
mod definitions;
pub(crate) mod effects;
mod environments;
pub(crate) mod foreign;
mod formatting;
mod generic_calls;
mod generic_receiving;
mod invocation;
mod loops;
mod numeric;
mod numeric_contexts;
mod phases;
mod publication;
mod record_construction;
mod record_contexts;
pub(crate) mod results;
mod scope_validation;
mod scopes;
mod signatures;
mod source_types;
mod termination;
mod transform;
mod type_invocation;
mod types;
mod typing;

#[derive(Debug, Clone, PartialEq)]
enum StaticValue {
    Integer(i128),
    TypedInteger(i128, u8, bool),
    Bool(bool),
    String(String),
    Unit,
    Type(TypeExpr),
    Float(f64, bool),
    BigInteger(num_bigint::BigInt),
    Bytes(Vec<u8>),
    Array(StaticCollection<Vec<StaticValue>>),
    Tuple(StaticCollection<Vec<StaticValue>>),
    Map(StaticCollection<Vec<(StaticValue, StaticValue)>>),
    Record(StaticRecord),
    Variant(
        String,
        Vec<StaticValue>,
        Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>,
    ),
    Result(Box<results::Produced>),
    Callable(StaticCallable),
}
#[derive(Debug, Clone)]
struct StaticCollection<T> {
    id: u64,
    values: std::sync::Arc<T>,
    source_type: Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>,
}
/// Record slot modes are part of its type, even though every evaluated handle
/// is immutable. They must survive export so a later clone has the same slots.
#[derive(Debug, Clone, PartialEq)]
struct StaticRecord {
    storage: StaticCollection<BTreeMap<String, StaticValue>>,
    mutable_fields: BTreeSet<String>,
}
impl std::ops::Deref for StaticRecord {
    type Target = BTreeMap<String, StaticValue>;
    fn deref(&self) -> &Self::Target {
        &self.storage
    }
}
impl IntoIterator for StaticRecord {
    type Item = (String, StaticValue);
    type IntoIter = std::collections::btree_map::IntoIter<String, StaticValue>;
    fn into_iter(self) -> Self::IntoIter {
        self.storage.into_iter()
    }
}
impl<T: PartialEq> PartialEq for StaticCollection<T> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}
impl<T> std::ops::Deref for StaticCollection<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.values
    }
}
impl<T: IntoIterator + Clone> IntoIterator for StaticCollection<T> {
    type Item = T::Item;
    type IntoIter = T::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        std::sync::Arc::unwrap_or_clone(self.values).into_iter()
    }
}
impl<'a, T> IntoIterator for &'a StaticCollection<T>
where
    &'a T: IntoIterator,
{
    type Item = <&'a T as IntoIterator>::Item;
    type IntoIter = <&'a T as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.values.as_ref().into_iter()
    }
}
impl StaticValue {
    fn collection_id(&self) -> Option<u64> {
        match self {
            Self::Array(value) | Self::Tuple(value) => Some(value.id),
            Self::Map(value) => Some(value.id),
            Self::Record(value) => Some(value.storage.id),
            _ => None,
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
enum StaticCallable {
    Prepared(std::sync::Arc<generic_calls::PreparedNamed>),
    View(Box<application::CallableView>),
    Named {
        name: String,
        captured: Option<environments::EnvironmentId>,
    },
    Builtin(String),
    Lambda {
        parameters: Vec<Parameter>,
        return_type: Option<Box<TypeExpr>>,
        body: Box<Expr>,
        captured: environments::Environment,
    },
}
enum Failure {
    Diagnostic(&'static str, String),
    Unsupported(String),
    Return(Box<StaticValue>),
    TailCall(Box<invocation::TailInvocation>),
    TailType(Box<type_invocation::TailType>),
    Loop(loops::Transfer),
}
type Result<T> = std::result::Result<T, Failure>;
// Every static operation carries this error. Control transfers move their
// values through indirection instead of enlarging every ordinary Result.
const _: () = assert!(std::mem::size_of::<Failure>() <= 128);

pub struct Evaluation {
    pub(crate) constants: constants::ConstantPool,
    pub program: Program,
    pub diagnostics: Vec<Diagnostic>,
    pub unsupported: Vec<crate::sema::UnsupportedFeature>,
    pub static_definitions: Vec<Function>,
    pub type_functions: Vec<TypeDeclaration>,
    pub static_termination: BTreeMap<String, crate::termination::Judgment>,
}
/// This key is for an already normalized static/type argument, not a runtime
/// expression or an authorization to admit an otherwise invalid argument.
pub(crate) fn normalized_argument_key(argument: &TypeExpr) -> String {
    types::type_key(argument)
}
pub(crate) enum ArgumentNormalizationError {
    Diagnostic(&'static str, String),
    Unsupported(String),
}
pub(crate) struct NormalizedConstructorArguments {
    pub arguments: Vec<TypeExpr>,
    pub payloads: BTreeMap<String, Option<TypeExpr>>,
}
/// Constructor instantiation uses the same sort/default rules as type
/// instantiation. Its input has already passed lexical/module resolution.
pub(crate) fn normalize_constructor_arguments(
    declaration: &TypeDeclaration,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
) -> std::result::Result<NormalizedConstructorArguments, ArgumentNormalizationError> {
    let mut work = usize::MAX;
    normalize_constructor_arguments_bounded(declaration, arguments, declarations, layout, &mut work)
}

/// The actual declaration clone, argument binding and payload elaboration
/// share one root. All nested evaluation inherits its remaining allowance.
pub(crate) fn normalize_constructor_arguments_bounded(
    declaration: &TypeDeclaration,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
    work: &mut usize,
) -> std::result::Result<NormalizedConstructorArguments, ArgumentNormalizationError> {
    let mut argument_budget = budget::Budget::default();
    let root = argument_budget.enter_root();
    argument_budget.restrict_work(u64::try_from(*work).unwrap_or(u64::MAX));
    if let Err(failure) = clone_work::type_declarations(&argument_budget, declarations) {
        *work = usize::try_from(argument_budget.work_remaining()).unwrap_or(usize::MAX);
        argument_budget.leave_root(root);
        return Err(match failure {
            Failure::Unsupported(message) => ArgumentNormalizationError::Unsupported(message),
            _ => ArgumentNormalizationError::Unsupported(
                "constructor declaration clone admission failed".into(),
            ),
        });
    }
    let mut evaluator = Evaluator {
        type_environment: Default::default(),
        type_application_sequence: 0,
        layout,
        values: BTreeMap::new(),
        global_values: BTreeMap::new(),
        budget: argument_budget,
        declarations: declarations.clone(),
        effect_declarations: BTreeMap::new(),
        functions: BTreeMap::new(),
        function_environments: BTreeMap::new(),
        environments: vec![],
        alias_instances: BTreeMap::new(),
        static_signatures: BTreeMap::new(),
        active_functions: vec![],
        type_depth: 0,
        call_depth: 0,
        tail_returns: false,
        tail_types: false,
        numeric_return: None,
        results: Default::default(),
        result_site: None,
        expression_depth: 0,
        loop_frames: vec![],
        next_loop_target: 0,
        type_calls: BTreeSet::new(),
        next_collection: 0,
        publications: Default::default(),
        constants: Default::default(),
    };
    let mut normalize = || -> Result<NormalizedConstructorArguments> {
        let arguments =
            evaluator.bind_type_arguments(&declaration.generics, arguments, &declaration.name)?;
        let mut payloads = BTreeMap::new();
        if declaration.nominal {
            let payload = declaration
                .value
                .as_ref()
                .map(|payload| evaluator.resolve_type(payload, &mut vec![]))
                .transpose()?;
            payloads.insert(declaration.name.clone(), payload);
        } else {
            let owner = TypeExpr {
                hir_id: None,
                kind: TypeKind::Name {
                    path: vec![declaration.name.clone()],
                    arguments: arguments.clone(),
                },
                text: declaration.name.clone(),
                span: declaration.span,
            };
            for variant in &declaration.variants {
                // Projection checks the complete result equation and recovers
                // each local type argument before resolving the payload.
                let payload = match evaluator.project_type(
                    &owner,
                    StaticValue::String(variant.name.clone()),
                    variant.span,
                    &mut vec![],
                ) {
                    Ok(payload) => variant.payload.as_ref().map(|_| payload),
                    Err(Failure::Diagnostic("E0301", _)) if variant.result.is_some() => {
                        continue;
                    }
                    Err(failure) => return Err(failure),
                };
                payloads.insert(format!("{}::{}", declaration.name, variant.name), payload);
            }
        }
        Ok(NormalizedConstructorArguments {
            arguments,
            payloads,
        })
    };
    let result = normalize();
    *work = usize::try_from(evaluator.budget.work_remaining()).unwrap_or(usize::MAX);
    evaluator.budget.leave_root(root);
    result.map_err(|failure| match failure {
        Failure::Diagnostic(code, message) => ArgumentNormalizationError::Diagnostic(code, message),
        Failure::Unsupported(message) => ArgumentNormalizationError::Unsupported(message),
        Failure::Return(_) | Failure::TailCall(_) | Failure::TailType(_) | Failure::Loop(_) => {
            ArgumentNormalizationError::Unsupported(
                "constructor type argument cannot return from an enclosing callable".into(),
            )
        }
    })
}

pub fn evaluate(program: &Program, layout: TargetLayout) -> Evaluation {
    evaluate_with_budget(program, layout, DEFAULT_STATIC_BUDGET)
}

pub fn evaluate_with_budget(
    program: &Program,
    layout: TargetLayout,
    allowance: std::num::NonZeroU64,
) -> Evaluation {
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("ril-static".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, || evaluate_inner(program, layout, allowance));
        let incomplete = || Evaluation {
            constants: Default::default(),
            program: Program::default(),
            diagnostics: vec![],
            unsupported: vec![crate::sema::UnsupportedFeature {
                span: program.statements.first().map_or(
                    Span {
                        file: ril_compiler_core::source::FileId(0),
                        start: 0,
                        end: 0,
                    },
                    |statement| statement.span,
                ),
                description: "static evaluation worker is unavailable".into(),
            }],
            static_definitions: vec![],
            type_functions: vec![],
            static_termination: BTreeMap::new(),
        };
        match worker {
            Ok(worker) => worker.join().unwrap_or_else(|_| incomplete()),
            Err(_) => incomplete(),
        }
    })
}
fn evaluate_inner(
    program: &Program,
    layout: TargetLayout,
    allowance: std::num::NonZeroU64,
) -> Evaluation {
    let scope_diagnostics = scope_validation::validate(program);
    let mut normalized = program.clone();
    scopes::normalize(&mut normalized);
    let program = &normalized;
    let collected = definitions::collect(program);
    let mut evaluator = Evaluator {
        type_environment: Default::default(),
        type_application_sequence: 0,
        layout,
        values: BTreeMap::new(),
        global_values: BTreeMap::new(),
        budget: budget::Budget::new(allowance),
        declarations: collected.all_types,
        effect_declarations: collected.all_effects,
        functions: collected.all_functions,
        function_environments: BTreeMap::new(),
        environments: vec![],
        alias_instances: BTreeMap::new(),
        static_signatures: BTreeMap::new(),
        active_functions: vec![],
        type_depth: 0,
        call_depth: 0,
        tail_returns: false,
        tail_types: false,
        numeric_return: None,
        results: Default::default(),
        result_site: None,
        expression_depth: 0,
        loop_frames: vec![],
        next_loop_target: 0,
        type_calls: BTreeSet::new(),
        next_collection: 0,
        publications: Default::default(),
        constants: Default::default(),
    };
    let mut output = Evaluation {
        constants: Default::default(),
        program: program.clone(),
        diagnostics: scope_diagnostics,
        unsupported: vec![],
        static_definitions: collected.functions,
        type_functions: collected.types,
        static_termination: BTreeMap::new(),
    };
    alias_cycles::validate(&evaluator, &mut output);
    termination::verify(&evaluator, &mut output);
    evaluator.transform_program(&mut output);
    scope_validation::confinement(&evaluator, &mut output);
    typing::verify(&evaluator, &mut output, program);
    if typing::verify_result_flows(&evaluator, program, &mut output) {
        evaluator.seal_result_constants(&mut output);
    }
    output.constants = evaluator.constants.into_inner();
    output
}
impl Evaluation {
    fn failure(&mut self, failure: Failure, span: Span) {
        match failure {
            Failure::Diagnostic(code, message) => self.diagnostics.push(Diagnostic {
                code: code.into(),
                severity: Severity::Error,
                message: message.clone(),
                labels: vec![Label { span, message }],
                causes: vec![],
            }),
            Failure::Unsupported(description) => self
                .unsupported
                .push(crate::sema::UnsupportedFeature { span, description }),
            Failure::Return(_) | Failure::TailCall(_) | Failure::TailType(_) | Failure::Loop(_) => {
                self.unsupported.push(crate::sema::UnsupportedFeature {
                    span,
                    description: "return has no enclosing static callable".into(),
                })
            }
        }
    }
}

struct Evaluator {
    type_environment: generic_calls::TypeEnvironment,
    type_application_sequence: u64,
    loop_frames: Vec<loops::Frame>,
    next_loop_target: u64,
    constants: std::cell::RefCell<constants::ConstantPool>,
    layout: TargetLayout,
    values: BTreeMap<String, StaticValue>,
    global_values: BTreeMap<String, StaticValue>,
    budget: budget::Budget,
    declarations: BTreeMap<String, TypeDeclaration>,
    effect_declarations: BTreeMap<String, EffectDeclaration>,
    functions: BTreeMap<String, Function>,
    function_environments: BTreeMap<String, environments::EnvironmentId>,
    environments: Vec<environments::Environment>,
    alias_instances: BTreeMap<types::TypeInstanceKey, TypeExpr>,
    static_signatures: BTreeMap<signatures::SignatureKey, signatures::Signature>,
    active_functions: Vec<environments::ActiveGroup>,
    type_depth: usize,
    call_depth: usize,
    tail_returns: bool,
    tail_types: bool,
    numeric_return: Option<TypeExpr>,
    results: results::Ledger,
    result_site: Option<Span>,
    expression_depth: usize,
    type_calls: BTreeSet<types::TypeInstanceKey>,
    next_collection: u64,
    publications: publication::Bindings,
}
impl Evaluator {
    fn collection<T>(&mut self, values: T) -> StaticCollection<T> {
        let id = self.next_collection;
        self.next_collection += 1;
        StaticCollection {
            id,
            values: std::sync::Arc::new(values),
            source_type: None,
        }
    }
    fn array(&mut self, values: Vec<StaticValue>) -> StaticValue {
        StaticValue::Array(self.collection(values))
    }
    fn tuple(&mut self, values: Vec<StaticValue>) -> StaticValue {
        StaticValue::Tuple(self.collection(values))
    }
    fn map(&mut self, values: Vec<(StaticValue, StaticValue)>) -> StaticValue {
        StaticValue::Map(self.collection(values))
    }
    fn record(
        &mut self,
        values: BTreeMap<String, StaticValue>,
        mutable_fields: BTreeSet<String>,
    ) -> StaticValue {
        StaticValue::Record(StaticRecord {
            storage: self.collection(values),
            mutable_fields,
        })
    }
    fn evaluation_root<T>(&mut self, action: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let owner = self.budget.enter_root();
        let result = action(self);
        self.budget.leave_root(owner);
        result
    }
    fn charge(&mut self) -> Result<()> {
        self.budget.work(1)
    }
    fn expression(&mut self, expression: &Expr) -> Result<StaticValue> {
        self.expression_mode(expression, false)
    }
    fn expression_mode(&mut self, expression: &Expr, tail: bool) -> Result<StaticValue> {
        self.expression_expected(expression, tail, None)
    }
    fn expression_expected(
        &mut self,
        expression: &Expr,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        self.evaluation_root(|evaluator| {
            evaluator.expression_within_root(expression, tail, expected)
        })
    }
    fn expression_within_root(
        &mut self,
        expression: &Expr,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        if self.expression_depth >= 128 {
            return Err(Failure::Unsupported(
                "static evaluator nesting exceeds the available implementation stack budget".into(),
            ));
        }
        self.expression_depth += 1;
        let saved_site = self.result_site.replace(expression.span);
        let result = self
            .expression_inner(expression, tail, expected)
            .and_then(|value| self.infer_source_type(value, expression.span))
            .and_then(|value| {
                if matches!(expression.kind, ExprKind::Array(_)) {
                    self.receive_array_constructor(value, expected)
                } else if matches!(expression.kind, ExprKind::Record { ty: None, .. }) {
                    self.receive_record_constructor(value, expected, expression.span)
                } else {
                    Ok(value)
                }
            });
        self.result_site = saved_site;
        self.expression_depth -= 1;
        result
    }
    fn expression_inner(
        &mut self,
        expression: &Expr,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        self.charge()?;
        match &expression.kind {
            ExprKind::Literal(Literal::Unit) => Ok(StaticValue::Unit),
            ExprKind::Literal(Literal::Bool(value)) => Ok(StaticValue::Bool(*value)),
            ExprKind::Literal(Literal::RawString(value)) => {
                Ok(StaticValue::String(value[1..value.len() - 1].into()))
            }
            ExprKind::Literal(Literal::String(value)) => Ok(StaticValue::String(
                crate::lower::decode_text(&value[1..value.len() - 1])
                    .map_err(|reason| Failure::Unsupported(reason.detail))?,
            )),
            ExprKind::Literal(Literal::Integer(text)) => {
                self.numeric_literal(text, false, false, expected)
            }
            ExprKind::Literal(Literal::Float(text)) => {
                self.numeric_literal(text, true, false, expected)
            }
            ExprKind::Literal(Literal::Bytes(text)) => Ok(StaticValue::Bytes(
                crate::lower::decode_bytes(&text[2..text.len() - 1])
                    .map_err(|reason| Failure::Unsupported(reason.detail))?,
            )),
            ExprKind::Interpolated(parts) => {
                let mut output = String::new();
                for part in parts {
                    match part {
                        StringPart::Text(text) => output.push_str(text),
                        StringPart::Interpolation {
                            expression, format, ..
                        } => {
                            let value = self.expression(expression)?;
                            let text =
                                self.format_static(&value, format.as_deref().unwrap_or(""))?;
                            output.push_str(&text);
                        }
                    }
                }
                Ok(StaticValue::String(output))
            }
            ExprKind::Name(name) => self.static_name(name),
            ExprKind::Path(path) => self.static_name(&path.join("::")),
            ExprKind::Generic { base, arguments } => {
                let name = expression_name(base)
                    .ok_or_else(|| Failure::Unsupported("computed type function callee".into()))?;
                if self.functions.contains_key(&name)
                    || self
                        .values
                        .get(&name)
                        .is_some_and(|value| matches!(value, StaticValue::Callable(_)))
                {
                    return match self.callable(&name)? {
                        StaticCallable::Named { name, captured } => self
                            .prepare_named(&name, captured, arguments)
                            .map(StaticValue::Callable),
                        _ => Err(Failure::Unsupported(
                            "static generic application requires a named declaration".into(),
                        )),
                    };
                }
                let ty = TypeExpr {
                    hir_id: None,
                    text: name.clone(),
                    kind: TypeKind::Name {
                        path: name.split("::").map(str::to_owned).collect(),
                        arguments: arguments.clone(),
                    },
                    span: expression.span,
                };
                if tail && self.tail_types {
                    return Err(Failure::TailType(Box::new(type_invocation::TailType {
                        syntax: ty,
                        environment: self.capture_environment()?,
                    })));
                }
                Ok(StaticValue::Type(self.expand_type(&ty, &mut Vec::new())?))
            }
            ExprKind::Array(items) => {
                let item_context = expected.and_then(|ty| {
                    if let TypeKind::Array { element, .. } = &ty.kind {
                        Some(element.as_ref())
                    } else {
                        None
                    }
                });
                let values = items
                    .iter()
                    .map(|item| self.expression_expected(item, false, item_context))
                    .collect::<Result<_>>()?;
                Ok(self.array(values))
            }
            ExprKind::Tuple(items) => {
                let values = items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| {
                        self.expression_expected(
                            item,
                            false,
                            expected.and_then(|ty| {
                                if let TypeKind::Tuple(types) = &ty.kind {
                                    types.get(index)
                                } else {
                                    None
                                }
                            }),
                        )
                    })
                    .collect::<Result<_>>()?;
                Ok(self.tuple(values))
            }
            ExprKind::Map(entries) => {
                let (key_context, value_context) = expected
                    .and_then(|ty| {
                        if let TypeKind::Map { key, value } = &ty.kind {
                            Some((Some(key.as_ref()), Some(value.as_ref())))
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default();
                let mut map = vec![];
                for (key, value) in entries {
                    let key = self.expression_expected(key, false, key_context)?;
                    let value = self.expression_expected(value, false, value_context)?;
                    if let Some((_, old)) = map.iter_mut().find(|(old, _)| static_equal(old, &key))
                    {
                        *old = value;
                    } else {
                        map.push((key, value));
                    }
                }
                Ok(self.map(map))
            }
            ExprKind::Record { ty, members, .. } => {
                let resolved = ty
                    .as_ref()
                    .map(|ty| self.resolve_type(ty, &mut vec![]))
                    .transpose()?;
                let record_context = resolved.as_ref().or(expected);
                let mut fields = BTreeMap::new();
                let mut mutable_fields = BTreeSet::new();
                let explicit: BTreeSet<_> = members
                    .iter()
                    .filter_map(|member| {
                        if let RecordMember::Field(field) = member {
                            Some(field.name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                let mut explicit_values = BTreeMap::new();
                let mut from_spreads = BTreeSet::new();
                for member in members {
                    match member {
                        RecordMember::Spread(value) => {
                            let StaticValue::Record(record) = self.expression(value)? else {
                                return Err(Failure::Diagnostic(
                                    "E0301",
                                    "static spread requires a record".into(),
                                ));
                            };
                            mutable_fields.extend(record.mutable_fields.iter().cloned());
                            for (name, value) in record {
                                if !from_spreads.insert(name.clone()) && !explicit.contains(&name) {
                                    return Err(Failure::Diagnostic("E0211","multiple spreads provide a field without an explicit override".into()));
                                }
                                fields.insert(name, value);
                            }
                        }
                        RecordMember::Field(field) => {
                            let field_context = record_context.and_then(|ty| {
                                if let TypeKind::Record { fields, .. } = &ty.kind {
                                    fields
                                        .iter()
                                        .find(|candidate| candidate.name == field.name)
                                        .map(|field| &field.ty)
                                } else {
                                    None
                                }
                            });
                            explicit_values.insert(
                                field.name.clone(),
                                self.expression_expected(&field.value, false, field_context)?,
                            );
                        }
                    }
                }
                fields.extend(explicit_values);
                // Explicit fields replace the spread's slot declaration. A
                // typed constructor then supplies all destination slot modes.
                mutable_fields.retain(|name| !explicit.contains(name));
                if let Some(resolved) = &resolved {
                    let TypeKind::Record { fields, row: None } = &resolved.kind else {
                        return Err(Failure::Unsupported(
                            "static record construction requires a closed structural type".into(),
                        ));
                    };
                    mutable_fields = fields
                        .iter()
                        .filter(|field| field.mutable)
                        .map(|field| field.name.clone())
                        .collect();
                }
                let record = self.record(fields, mutable_fields);
                if let Some(resolved_type) = resolved.as_ref() {
                    self.retain_constant_shape(&record, resolved_type)?;
                    return self.ascribe_application_value_from_resolved(
                        record,
                        ty.as_ref().unwrap_or(resolved_type),
                        resolved_type,
                    );
                }
                Ok(record)
            }
            ExprKind::Field { base, field, safe } => {
                let value = self.expression(base)?;
                if *safe {
                    let payload = match value {
                        StaticValue::Variant(name, mut values, _)
                            if name.strip_prefix("Prelude::").unwrap_or(&name) == "Some"
                                && values.len() == 1 =>
                        {
                            values.remove(0)
                        }
                        StaticValue::Variant(name, values, _)
                            if name.strip_prefix("Prelude::").unwrap_or(&name) == "None"
                                && values.is_empty() =>
                        {
                            return Ok(StaticValue::Variant("Prelude::None".into(), vec![], None));
                        }
                        _ => {
                            return Err(Failure::Diagnostic(
                                "E0715",
                                "safe field projection requires an optional receiver".into(),
                            ));
                        }
                    };
                    let projected = self.field_value(payload, field)?;
                    if matches!(&projected,StaticValue::Variant(name,_,_) if matches!(name.strip_prefix("Prelude::").unwrap_or(name),"Some"|"None"))
                    {
                        Ok(projected)
                    } else {
                        Ok(StaticValue::Variant(
                            "Prelude::Some".into(),
                            vec![projected],
                            None,
                        ))
                    }
                } else {
                    self.field_value(value, field)
                }
            }
            ExprKind::Accessor(path) => {
                self.expression(&transform::accessor_lambda(path, expression.span))
            }
            ExprKind::ComputedField { base, key } => {
                let value = self.expression(base)?;
                let key = self.expression(key)?;
                match key {
                    StaticValue::String(key) => self.field_value(value, &key),
                    StaticValue::Integer(index) => self.field_value(value, &index.to_string()),
                    _ => Err(Failure::Diagnostic(
                        "E0324",
                        "computed product key must be static".into(),
                    )),
                }
            }
            ExprKind::Index { base, index, safe } => {
                let value = self.expression(base)?;
                let index = self.expression(index)?;
                self.index_value(value, index, *safe)
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                ..
            } => {
                clone_work::expression(&self.budget, expression)?;
                // Written parameter types are evaluated at creation, in this
                // root and lexical environment. Invocation consumes the type
                // witness without re-running its source computation.
                let mut parameters = parameters.clone();
                for parameter in &mut parameters {
                    if let Some(ty) = &mut parameter.ty {
                        *ty = self.resolve_type(ty, &mut vec![])?;
                    }
                }
                Ok(StaticValue::Callable(StaticCallable::Lambda {
                    parameters,
                    return_type: return_type
                        .as_ref()
                        .map(|ty| self.resolve_type(ty, &mut vec![]).map(Box::new))
                        .transpose()?,
                    body: body.clone(),
                    captured: self.capture_environment()?,
                }))
            }
            ExprKind::KeyOf(ty) => self.keyof(ty),
            ExprKind::Match { value, arms, .. } => {
                let value = self.expression(value)?;
                for arm in arms {
                    let saved = self.snapshot_values()?;
                    self.type_environment.admit_clone(&self.budget)?;
                    let saved_types = self.type_environment.clone();
                    if self.match_pattern(&arm.pattern, &value)?
                        && arm.guard.as_ref().map_or(Ok(true), |guard| {
                            match self.expression(guard)? {
                                StaticValue::Bool(value) => Ok(value),
                                _ => Err(Failure::Diagnostic(
                                    "E0301",
                                    "match guard must be bool".into(),
                                )),
                            }
                        })?
                    {
                        let result = self.expression_expected(&arm.body, tail, expected);
                        self.values = saved;
                        self.type_environment = saved_types;
                        return result;
                    }
                    self.values = saved;
                    self.type_environment = saved_types;
                }
                Err(Failure::Diagnostic(
                    "E0303",
                    "static match has no matching arm".into(),
                ))
            }
            ExprKind::Is { value, pattern } => {
                let value = self.expression(value)?;
                let saved = self.snapshot_values()?;
                self.type_environment.admit_clone(&self.budget)?;
                let saved_types = self.type_environment.clone();
                let result = self.match_pattern(pattern, &value);
                self.values = saved;
                self.type_environment = saved_types;
                result.map(StaticValue::Bool)
            }
            ExprKind::TypeValue(ty) => {
                if tail && self.tail_types {
                    return Err(Failure::TailType(Box::new(type_invocation::TailType {
                        syntax: ty.clone(),
                        environment: self.capture_environment()?,
                    })));
                }
                Ok(StaticValue::Type(self.expand_type(ty, &mut Vec::new())?))
            }
            ExprKind::Unary { operator, operand } => {
                if operator == "-"
                    && let ExprKind::Literal(literal) = &operand.kind
                {
                    match literal {
                        Literal::Integer(text) => {
                            return self.numeric_literal(text, false, true, expected);
                        }
                        Literal::Float(text) => {
                            return self.numeric_literal(text, true, true, expected);
                        }
                        _ => {}
                    }
                }
                let operand = self.expression_expected(
                    operand,
                    false,
                    if operator == "-" { expected } else { None },
                )?;
                match (operator.as_str(), operand) {
                    ("-", StaticValue::Integer(value)) => {
                        let value = value.checked_neg().ok_or_else(|| {
                            Failure::Diagnostic("E0831", "compile-time integer overflow".into())
                        })?;
                        self.check_integer(value, self.layout.pointer_bits, true)?;
                        Ok(StaticValue::Integer(value))
                    }
                    ("-", StaticValue::TypedInteger(value, bits, signed)) => {
                        let value = -value;
                        self.check_integer(value, bits, signed)?;
                        Ok(StaticValue::TypedInteger(value, bits, signed))
                    }
                    ("!", StaticValue::Bool(value)) => Ok(StaticValue::Bool(!value)),
                    ("-", StaticValue::Float(value, narrow)) => {
                        Ok(StaticValue::Float(-value, narrow))
                    }
                    ("-", StaticValue::BigInteger(value)) => Ok(StaticValue::BigInteger(-value)),
                    ("~", StaticValue::Integer(value)) => Ok(StaticValue::Integer(!value)),
                    _ => Err(Failure::Diagnostic(
                        "E0301",
                        "incompatible static unary operand".into(),
                    )),
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "??" {
                    return self.evaluate_coalescing(left, right, tail, expected);
                }
                let numeric_context = if matches!(operator.as_str(), "&&" | "||") {
                    None
                } else {
                    expected
                        .filter(|ty| numeric_contexts::number_type(ty).is_some())
                        .cloned()
                        .or_else(|| self.rigid_numeric_peer(left))
                        .or_else(|| self.rigid_numeric_peer(right))
                };
                let left = self.expression_expected(left, false, numeric_context.as_ref())?;
                if operator == "&&" && left == StaticValue::Bool(false) {
                    return Ok(left);
                }
                if operator == "||" && left == StaticValue::Bool(true) {
                    return Ok(left);
                }
                let right = self.expression_expected(
                    right,
                    false,
                    if matches!(operator.as_str(), "<<" | ">>") {
                        None
                    } else {
                        numeric_context.as_ref()
                    },
                )?;
                self.binary(operator, left, right)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => match self.expression(condition)? {
                StaticValue::Bool(true) => self.expression_expected(then_branch, tail, expected),
                StaticValue::Bool(false) => else_branch
                    .as_ref()
                    .map_or(Ok(StaticValue::Unit), |branch| {
                        self.expression_expected(branch, tail, expected)
                    }),
                _ => Err(Failure::Diagnostic(
                    "E0301",
                    "static condition must be bool".into(),
                )),
            },
            ExprKind::Block(block) => {
                let saved = self.snapshot_values()?;
                self.type_environment.admit_clone(&self.budget)?;
                let saved_types = self.type_environment.clone();
                let result = self.block_expected(block, tail, expected);
                self.values = saved;
                self.type_environment = saved_types;
                result
            }
            ExprKind::Loop(body) => self.evaluate_loop(body, expected),
            ExprKind::While { condition, body } => self.evaluate_while(condition, body),
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => self.evaluate_for(iterable, pattern, body),
            ExprKind::Control {
                operation: operation @ (ControlOperation::Next | ControlOperation::Last),
                value,
            } => self.loop_control(*operation, value.as_deref()),
            ExprKind::Call { callee, arguments } => {
                let callable = if let Some(name) = expression_name(callee) {
                    self.callable(&name)?
                } else {
                    let StaticValue::Callable(callable) = self.expression(callee)? else {
                        return Err(Failure::Diagnostic(
                            "E0338",
                            "static callee is not callable".into(),
                        ));
                    };
                    callable
                };
                let caller = if expected.is_some() {
                    Some(self.capture_environment()?)
                } else {
                    None
                };
                let values = self.numeric_arguments(&callable, arguments, expected)?;
                let callable = self.prepare_named_result_context(
                    callable,
                    &values,
                    expected,
                    caller.as_ref(),
                )?;
                if tail {
                    Err(Failure::TailCall(Box::new(invocation::TailInvocation {
                        callable,
                        arguments: values,
                        site: expression.span,
                    })))
                } else {
                    self.invoke_static(callable, values)
                }
            }
            ExprKind::Control {
                operation: ControlOperation::Return,
                value,
            } => {
                let expected = self.numeric_return.clone();
                let value = value.as_ref().map_or(Ok(StaticValue::Unit), |value| {
                    self.expression_expected(value, self.tail_returns, expected.as_ref())
                })?;
                Err(Failure::Return(Box::new(value)))
            }
            _ => Err(Failure::Unsupported(
                "compile-time expression is not yet implemented".into(),
            )),
        }
    }
    fn block_expected(
        &mut self,
        block: &Block,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        self.enter_block(block)?;
        let result = self.block_inner(block, tail, expected);
        self.exit_block();
        result
    }
    fn block_inner(
        &mut self,
        block: &Block,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        let mut value = StaticValue::Unit;
        for (index, statement) in block.statements.iter().enumerate() {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    if binding.mode != BindingMode::Let {
                        return Err(Failure::Unsupported(
                            "static writable/scoped local authority proof".into(),
                        ));
                    }
                    let binding_type = binding
                        .ty
                        .as_ref()
                        .map(|ty| self.resolve_type(ty, &mut vec![]))
                        .transpose()?;
                    let syntax = record_contexts::expression(&binding.value, binding_type.as_ref());
                    let mut initializer =
                        self.expression_expected(&syntax, false, binding_type.as_ref())?;
                    if let Some(ty) = &binding_type {
                        self.retain_constant_shape(&initializer, ty)?;
                        initializer = self.ascribe_application_value(initializer, ty)?;
                    }
                    let before = self.snapshot_values()?;
                    self.type_environment.admit_clone(&self.budget)?;
                    let before_types = self.type_environment.clone();
                    if !self.match_pattern(&binding.pattern, &initializer)? {
                        self.values = before;
                        self.type_environment = before_types;
                        if let Some(fallback) = &binding.fallback {
                            self.expression(fallback)?;
                            return Err(Failure::Diagnostic(
                                "E0321",
                                "fallible static binding fallback must diverge".into(),
                            ));
                        }
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "static binding pattern does not match".into(),
                        ));
                    }
                    self.refresh_local_functions()?;
                    value = StaticValue::Unit;
                }
                StmtKind::Expr {
                    expression,
                    terminated,
                } => {
                    value = self.expression_expected(
                        expression,
                        tail && index + 1 == block.statements.len() && !terminated,
                        if index + 1 == block.statements.len() && !terminated {
                            expected
                        } else {
                            None
                        },
                    )?;
                    if *terminated {
                        value = StaticValue::Unit;
                    }
                }
                _ => return Err(Failure::Unsupported("static statement".into())),
            }
        }
        Ok(value)
    }
    fn binary(&self, operator: &str, left: StaticValue, right: StaticValue) -> Result<StaticValue> {
        if matches!(operator, "<<" | ">>") {
            return self.shift(left, right, operator == "<<");
        }
        if matches!(operator, "==" | "!=") {
            if contains_callable(&left) || contains_callable(&right) {
                return Err(Failure::Diagnostic(
                    "E0305",
                    "callable values do not admit equality".into(),
                ));
            }
            let equal = match (&left, &right) {
                (StaticValue::Type(left), StaticValue::Type(right)) => {
                    canonical_type(left) == canonical_type(right)
                }
                _ => static_equal(&left, &right),
            };
            return Ok(StaticValue::Bool(if operator == "==" {
                equal
            } else {
                !equal
            }));
        }
        match (left, right) {
            (StaticValue::Float(a, narrow), StaticValue::Float(b, other)) if narrow == other => {
                if matches!(operator, "<" | "<=" | ">" | ">=") {
                    return Ok(StaticValue::Bool(match operator {
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        _ => a >= b,
                    }));
                }
                let value = if narrow {
                    let (a, b) = (a as f32, b as f32);
                    f64::from(match operator {
                        "+" => a + b,
                        "-" => a - b,
                        "*" => a * b,
                        "/" => a / b,
                        "%" => a % b,
                        _ => {
                            return Err(Failure::Diagnostic(
                                "E0301",
                                "invalid float operator".into(),
                            ));
                        }
                    })
                } else {
                    match operator {
                        "+" => a + b,
                        "-" => a - b,
                        "*" => a * b,
                        "/" => a / b,
                        "%" => a % b,
                        _ => {
                            return Err(Failure::Diagnostic(
                                "E0301",
                                "invalid float operator".into(),
                            ));
                        }
                    }
                };
                Ok(StaticValue::Float(
                    if value.is_nan() {
                        f64::from_bits(0x7ff8_0000_0000_0000)
                    } else if narrow {
                        f64::from(value as f32)
                    } else {
                        value
                    },
                    narrow,
                ))
            }
            (StaticValue::BigInteger(a), StaticValue::BigInteger(b)) => {
                if matches!(operator, "<" | "<=" | ">" | ">=") {
                    return Ok(StaticValue::Bool(match operator {
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        _ => a >= b,
                    }));
                }
                let value = match operator {
                    "+" => a + b,
                    "-" => a - b,
                    "*" => a * b,
                    "/" if b != num_bigint::BigInt::from(0) => a / b,
                    "%" if b != num_bigint::BigInt::from(0) => a % b,
                    "&" => a & b,
                    "|" => a | b,
                    "^" => a ^ b,
                    _ => {
                        return Err(Failure::Diagnostic(
                            "E0831",
                            "invalid bigint operation".into(),
                        ));
                    }
                };
                Ok(StaticValue::BigInteger(value))
            }
            (StaticValue::Bool(a), StaticValue::Bool(b)) => Ok(StaticValue::Bool(match operator {
                "&&" => a && b,
                "||" => a || b,
                _ => {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "invalid static bool operator".into(),
                    ));
                }
            })),
            (StaticValue::Integer(a), StaticValue::Integer(b)) => {
                if matches!(operator, "<" | "<=" | ">" | ">=") {
                    return Ok(StaticValue::Bool(match operator {
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        _ => a >= b,
                    }));
                }
                let result = match operator {
                    "+" => a.checked_add(b),
                    "-" => a.checked_sub(b),
                    "*" => a.checked_mul(b),
                    "/" => a.checked_div(b),
                    "%" => a.checked_rem(b),
                    "&" => Some(a & b),
                    "|" => Some(a | b),
                    "^" => Some(a ^ b),
                    _ => return Err(Failure::Unsupported(format!("static operator {operator}"))),
                };
                let value = result.ok_or_else(|| {
                    Failure::Diagnostic("E0831", "invalid static arithmetic".into())
                })?;
                self.check_integer(value, self.layout.pointer_bits, true)?;
                Ok(StaticValue::Integer(value))
            }
            (
                StaticValue::TypedInteger(a, bits, signed),
                StaticValue::TypedInteger(b, other, other_signed),
            ) if bits == other && signed == other_signed => {
                if matches!(operator, "<" | "<=" | ">" | ">=") {
                    return Ok(StaticValue::Bool(match operator {
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        _ => a >= b,
                    }));
                }
                let value = match operator {
                    "+" => a.checked_add(b),
                    "-" => a.checked_sub(b),
                    "*" => a.checked_mul(b),
                    "/" => a.checked_div(b),
                    "%" => a.checked_rem(b),
                    "&" => Some(a & b),
                    "|" => Some(a | b),
                    "^" => Some(a ^ b),
                    _ => {
                        return Err(Failure::Unsupported(format!(
                            "typed static operator {operator}"
                        )));
                    }
                }
                .ok_or_else(|| Failure::Diagnostic("E0831", "invalid static arithmetic".into()))?;
                self.check_integer(value, bits, signed)?;
                Ok(StaticValue::TypedInteger(value, bits, signed))
            }
            _ => Err(Failure::Diagnostic(
                "E0301",
                "incompatible static operands".into(),
            )),
        }
    }
    fn check_integer(&self, value: i128, bits: u8, signed: bool) -> Result<()> {
        let bound = 1i128 << if signed { bits - 1 } else { bits };
        if value < if signed { -bound } else { 0 } || value >= bound {
            Err(Failure::Diagnostic(
                "E0831",
                "compile-time integer overflow".into(),
            ))
        } else {
            Ok(())
        }
    }
    fn expand_type(&mut self, ty: &TypeExpr, seen: &mut Vec<String>) -> Result<TypeExpr> {
        self.resolve_type(ty, seen)
    }
    fn byte_size(&mut self, ty: &TypeExpr) -> Result<i128> {
        let ty = self.expand_type(ty, &mut Vec::new())?;
        let pointer = i128::from(self.layout.pointer_bytes());
        match &ty.kind {
            TypeKind::Tuple(values) if values.is_empty() => Ok(0),
            TypeKind::Name { path, arguments } => Ok(match path.join("::").as_str() {
                "bool" | "u8" | "i8" => 1,
                "u16" | "i16" => 2,
                "u32" | "i32" | "f32" => 4,
                "u64" | "i64" | "f64" => 8,
                "int" | "bigint" => pointer,
                "str" | "bytes" => pointer * 2,
                "never" => 0,
                name => {
                    let Some(identity) =
                        ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(name)
                    else {
                        return Err(Failure::Unsupported(
                            "layout of unresolved named type".into(),
                        ));
                    };
                    if !arguments.is_empty() {
                        return Err(Failure::Diagnostic(
                            "E0340",
                            "intrinsic atomic type has no generic arguments".into(),
                        ));
                    }
                    i128::from(identity.byte_size(self.layout))
                }
            }),
            TypeKind::Record { .. }
            | TypeKind::Array { .. }
            | TypeKind::Map { .. }
            | TypeKind::Tuple(_)
            | TypeKind::Optional(_)
            | TypeKind::Callable { .. } => Ok(pointer),
            _ => Err(Failure::Unsupported("layout of computed type".into())),
        }
    }
    fn materialize(&self, value: StaticValue, span: Span) -> Result<Expr> {
        if matches!(value, StaticValue::Result(_)) {
            return self.materialize_graph(&value, span);
        }
        // Non-finite floats have no source token spelling. The sealed pool
        // preserves the selected format and IEEE bits without re-parsing.
        if matches!(&value,StaticValue::Float(value,_)if !value.is_finite()) {
            return self.materialize_graph(&value, span);
        }
        if let StaticValue::Integer(value) = &value
            && *value < 0
        {
            self.check_integer(*value, self.layout.pointer_bits, true)?;
            // The magnitude of int's minimum is valid only together with its
            // immediate minus. It is not a separate positive int value.
            return Ok(Expr {
                hir_id: None,
                kind: ExprKind::Unary {
                    operator: "-".into(),
                    operand: Box::new(Expr {
                        hir_id: None,
                        kind: ExprKind::Literal(Literal::Integer(format!("{}int", -*value))),
                        span,
                    }),
                },
                span,
            });
        }
        let positive = match &value {
            StaticValue::TypedInteger(value, bits, signed) if *value < 0 => {
                Some(StaticValue::TypedInteger(-*value, *bits, *signed))
            }
            StaticValue::Float(value, narrow) if value.is_sign_negative() => {
                Some(StaticValue::Float(-*value, *narrow))
            }
            StaticValue::BigInteger(value) if value.sign() == num_bigint::Sign::Minus => {
                Some(StaticValue::BigInteger(-value))
            }
            _ => None,
        };
        if let Some(positive) = positive {
            return Ok(Expr {
                hir_id: None,
                kind: ExprKind::Unary {
                    operator: "-".into(),
                    operand: Box::new(self.materialize(positive, span)?),
                },
                span,
            });
        }
        if let Some(id) = value.collection_id() {
            if let Some(name) = self.publications.visible_name(id) {
                self.budget.work(name.len() as u64)?;
                return Ok(Expr {
                    hir_id: None,
                    kind: ExprKind::Name(name.into()),
                    span,
                });
            }
            // First publication, including a local one, is already an arena
            // reference. Hiding every alias can never split its object later.
            return self.materialize_graph(&value, span);
        }
        if matches!(value, StaticValue::Variant(..))
            && contains_leaf(&value, |value| value.collection_id().is_some())
        {
            return self.materialize_graph(&value, span);
        }
        let tuple = matches!(&value, StaticValue::Tuple(_));
        let literal = match value {
            StaticValue::Integer(value) => {
                self.check_integer(value, self.layout.pointer_bits, true)?;
                // An evaluated scalar already has type int. Reification is
                // not another unsuffixed literal inference opportunity, even
                // when several constant children share a diagnostic span.
                Literal::Integer(format!("{value}int"))
            }
            StaticValue::TypedInteger(value, bits, signed) => {
                Literal::Integer(format!("{value}{}{bits}", if signed { 'i' } else { 'u' }))
            }
            StaticValue::Bool(value) => Literal::Bool(value),
            StaticValue::Unit => Literal::Unit,
            StaticValue::String(value) => {
                return Ok(Expr {
                    hir_id: None,
                    kind: ExprKind::Interpolated(vec![StringPart::Text(value)]),
                    span,
                });
            }
            StaticValue::Type(ty) => {
                return Ok(Expr {
                    hir_id: None,
                    kind: ExprKind::TypeValue(ty),
                    span,
                });
            }
            StaticValue::Float(value, narrow) => {
                Literal::Float(format!("{value:?}{}", if narrow { "f32" } else { "f64" }))
            }
            StaticValue::BigInteger(value) => Literal::Integer(format!("{value}bigint")),
            StaticValue::Bytes(value) => Literal::Bytes(format!(
                "b\"{}\"",
                value
                    .iter()
                    .map(|byte| format!("\\x{byte:02X}"))
                    .collect::<String>()
            )),
            StaticValue::Array(items) | StaticValue::Tuple(items) => {
                if items.iter().any(|value| self.unpublished_reference(value)) {
                    return Err(Failure::Unsupported(
                        "alias-preserving nested static graph materialization".into(),
                    ));
                }
                let items = items
                    .into_iter()
                    .map(|item| self.materialize(item, span))
                    .collect::<Result<_>>()?;
                return Ok(Expr {
                    hir_id: None,
                    kind: if tuple {
                        ExprKind::Tuple(items)
                    } else {
                        ExprKind::Array(items)
                    },
                    span,
                });
            }
            StaticValue::Map(entries) => {
                if entries.iter().any(|(key, value)| {
                    self.unpublished_reference(key) || self.unpublished_reference(value)
                }) {
                    return Err(Failure::Unsupported(
                        "alias-preserving static map graph materialization".into(),
                    ));
                }
                let entries = entries
                    .into_iter()
                    .map(|(key, value)| {
                        Ok((self.materialize(key, span)?, self.materialize(value, span)?))
                    })
                    .collect::<Result<_>>()?;
                return Ok(Expr {
                    hir_id: None,
                    kind: ExprKind::Map(entries),
                    span,
                });
            }
            StaticValue::Variant(name, payload, _) => {
                if payload
                    .iter()
                    .any(|value| self.unpublished_reference(value))
                {
                    return Err(Failure::Unsupported(
                        "static constructor graph materialization".into(),
                    ));
                }
                let kind = if payload.is_empty() {
                    ExprKind::Name(name)
                } else {
                    ExprKind::Call {
                        callee: Box::new(Expr {
                            hir_id: None,
                            kind: ExprKind::Name(name),
                            span,
                        }),
                        arguments: payload
                            .into_iter()
                            .map(|item| {
                                Ok(Argument {
                                    label: None,
                                    mode: ParameterMode::Read,
                                    value: self.materialize(item, span)?,
                                    span,
                                })
                            })
                            .collect::<Result<_>>()?,
                    }
                };
                return Ok(Expr {
                    hir_id: None,
                    kind,
                    span,
                });
            }
            StaticValue::Record(_) | StaticValue::Callable(_) | StaticValue::Result(_) => {
                return Err(Failure::Unsupported(
                    "static reference/environment materialization".into(),
                ));
            }
        };
        Ok(Expr {
            hir_id: None,
            kind: ExprKind::Literal(literal),
            span,
        })
    }
    fn unpublished_reference(&self, value: &StaticValue) -> bool {
        reference_value(value)
            && value
                .collection_id()
                .is_none_or(|id| self.publications.visible_name(id).is_none())
    }
}
fn canonical_type(ty: &TypeExpr) -> String {
    types::type_key(ty)
}
fn primitive_type(name: &str) -> bool {
    matches!(
        name,
        "int"
            | "bigint"
            | "bool"
            | "str"
            | "bytes"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "f32"
            | "f64"
            | "never"
    )
}
fn expression_name(expression: &Expr) -> Option<String> {
    match &expression.kind {
        ExprKind::Name(name) => Some(name.clone()),
        ExprKind::Path(path) => Some(path.join("::")),
        _ => None,
    }
}
fn reference_value(value: &StaticValue) -> bool {
    matches!(
        value,
        StaticValue::Array(_)
            | StaticValue::Tuple(_)
            | StaticValue::Map(_)
            | StaticValue::Record(_)
            | StaticValue::Callable(_)
    )
}
fn static_equal(a: &StaticValue, b: &StaticValue) -> bool {
    match (a, b) {
        (StaticValue::Result(a), StaticValue::Result(b)) => {
            a.success == b.success && static_equal(&a.payload, &b.payload)
        }
        (StaticValue::Type(a), StaticValue::Type(b)) => canonical_type(a) == canonical_type(b),
        (StaticValue::Array(a), StaticValue::Array(b))
        | (StaticValue::Tuple(a), StaticValue::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| static_equal(a, b))
        }
        (StaticValue::Record(a), StaticValue::Record(b)) => {
            a.len() == b.len()
                && a.iter().all(|(name, value)| {
                    b.get(name).is_some_and(|other| static_equal(value, other))
                })
        }
        (StaticValue::Map(a), StaticValue::Map(b)) => {
            a.len() == b.len()
                && a.iter().all(|(key, value)| {
                    b.iter().any(|(other_key, other_value)| {
                        static_equal(key, other_key) && static_equal(value, other_value)
                    })
                })
        }
        (StaticValue::Variant(a, ap, _), StaticValue::Variant(b, bp, _)) => {
            a.trim_start_matches("Prelude::") == b.trim_start_matches("Prelude::")
                && ap.len() == bp.len()
                && ap.iter().zip(bp).all(|(a, b)| static_equal(a, b))
        }
        _ => a == b,
    }
}
fn contains_callable(value: &StaticValue) -> bool {
    contains_leaf(value, |value| matches!(value, StaticValue::Callable(_)))
}
fn contains_type_value(value: &StaticValue) -> bool {
    contains_leaf(value, |value| matches!(value, StaticValue::Type(_)))
}
fn contains_leaf(value: &StaticValue, predicate: impl Fn(&StaticValue) -> bool) -> bool {
    let mut seen = BTreeSet::new();
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        if predicate(value) {
            return true;
        }
        if value.collection_id().is_some_and(|id| !seen.insert(id)) {
            continue;
        }
        match value {
            StaticValue::Array(values) | StaticValue::Tuple(values) => work.extend(values.iter()),
            StaticValue::Record(values) => work.extend(values.values()),
            StaticValue::Map(values) => {
                for (key, value) in values {
                    work.extend([key, value]);
                }
            }
            StaticValue::Variant(_, values, _) => work.extend(values),
            StaticValue::Result(produced) => work.push(&produced.payload),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn non_product_type_projections_keep_the_specific_diagnostic() {
        for source in [
            "type Item=([]int).elem",
            "type Item=([str:int]).value",
            "type Item=int.elem",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let result = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0337"),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn unicode_escapes_and_doubled_braces_never_become_interpolation_expressions() {
        let parsed = ril_syntax::parse(
            "meta let _=assert(String::byte_len(\"\\u{10FFFF}\")==4)\nmeta let _=assert(String::byte_len(\"\\u{D7FF}\")==3)\nmeta let _=assert(\"{{literal}}\"==`{literal}`)\nfn example(){let maximum=\"\\u{10FFFF}\";let edge=\"\\u{D7FF}\";let braces=\"{{literal}}\"}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let evaluated = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            evaluated.diagnostics.is_empty() && evaluated.unsupported.is_empty(),
            "{:?} {:?}",
            evaluated.diagnostics,
            evaluated.unsupported
        );
        let checked = crate::sema::analyze_project_for(
            &evaluated.program,
            ril_compiler_core::source::FileId(0),
            &[],
            TargetLayout::POINTER64,
            &evaluated.constants,
        );
        assert!(
            checked.program.is_some(),
            "{:?} {:?}",
            checked.diagnostics,
            checked.unsupported
        );
    }
    #[test]
    fn sum_type_projection_checks_result_equations_after_recovering_local_types() {
        for source in [
            "type Packed<T>{Item(T)->Packed<T>}\ntype Payload=Packed<int>.Item\nmeta let _=assert(type<Payload>==type<int>)",
            "type Box<T>{Item<U>(U)->Box<U>}\ntype Payload=Box<int>.Item\nmeta let _=assert(type<Payload>==type<int>)",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let result = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                result.diagnostics.is_empty() && result.unsupported.is_empty(),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for source in [
            "type Box<T>{Item<U:bool>(U)->Box<U>}\ntype Payload=Box<int>.Item",
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\ntype Payload=Expr<int>.Bool",
            "type Box<T>{Item<U>(U)->Box<[]U>}\ntype Payload=Box<[2]int>.Item",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let result = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn projection_accessors_desugar_with_private_bindings_and_safe_paths() {
        let parsed = ril_syntax::parse(
            "fn example(){let values=[.{id:1,name:\"a\"},.{id:2,name:\"b\"}];let names=Array::map(values,\\.name);let ids=Array::map([(1,\"a\")],\\.0);let optional:[]?{name:str}=[Some(.{name:\"a\"}),None];let selected=Array::map(optional,\\?.name);let nested:[]?{child:?{value:int}}=[Some(.{child:Some(.{value:1})}),None];let result=Array::map(nested,\\?.child?.value)}\nmeta let NAMES=Array::map([.{name:\"a\"},.{name:\"b\"}],\\.name)\nmeta let _=assert(NAMES==[\"a\",\"b\"])\nmeta let SAFE=Array::map([Some(.{child:Some(.{value:1})}),None],\\?.child?.value)\nmeta let _=assert(SAFE==[Some(1),None])",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let evaluated = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            evaluated.diagnostics.is_empty() && evaluated.unsupported.is_empty(),
            "{:?} {:?}",
            evaluated.diagnostics,
            evaluated.unsupported
        );
        let checked = crate::sema::analyze_project_for(
            &evaluated.program,
            ril_compiler_core::source::FileId(0),
            &[],
            TargetLayout::POINTER64,
            &evaluated.constants,
        );
        assert!(
            checked.program.is_some(),
            "{:?} {:?}",
            checked.diagnostics,
            checked.unsupported
        );
        let StmtKind::Function(function) = &evaluated.program.statements[0].kind else {
            panic!()
        };
        let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[1].kind else {
            panic!()
        };
        let ExprKind::Call { arguments, .. } = &binding.value.kind else {
            panic!()
        };
        let ExprKind::Lambda {
            parameters, body, ..
        } = &arguments[1].value.kind
        else {
            panic!()
        };
        assert!(
            matches!(&parameters[0].pattern.kind,PatternKind::Name(name) if name.contains("__"))
        );
        assert_ne!(body.span, arguments[1].value.span);
        assert!(matches!(&body.kind,ExprKind::Field{field,safe:false,..} if field=="name"));
    }
    #[test]
    fn accessors_keep_product_diagnostics_and_do_not_restore_field_writers() {
        for (source, code) in [
            (
                "fn example(){let get=\\.missing;let value=get(.{id:1})}",
                "E0336",
            ),
            ("fn example(){let get=\\.2;let value=get((1,2))}", "E0312"),
            ("fn example(){let get=\\.0;let value=get([1,2])}", "E0337"),
            (
                "type Cell={mut value:int}\nfn example(mut cell:Cell)&mut{let holder=.{cell:cell};let get=\\.cell;let mut alias=^mut get(holder);alias.value+=1}",
                "E0520",
            ),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let transformed = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                transformed.diagnostics.is_empty() && transformed.unsupported.is_empty(),
                "{:?} {:?}",
                transformed.diagnostics,
                transformed.unsupported
            );
            let checked = crate::sema::analyze_project_for(
                &transformed.program,
                ril_compiler_core::source::FileId(0),
                &[],
                TargetLayout::POINTER64,
                &transformed.constants,
            );
            assert!(
                checked
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source}: {:?} {:?}",
                checked.diagnostics,
                checked.unsupported
            );
        }
    }
    #[test]
    fn byte_size_uses_selected_layout_and_assertions_are_real_computations() {
        let syntax = ril_syntax::parse(
            "meta let _ = assert(byte_size(type<int>) == 4)\nmeta let _ = assert(byte_size(type<u8>) == 1)",
        );
        assert!(syntax.is_ok(), "{:?}", syntax.diagnostics);
        let narrow = evaluate(&syntax.program, TargetLayout::POINTER32);
        assert!(narrow.diagnostics.is_empty());
        assert!(narrow.unsupported.is_empty());
        let wide = evaluate(&syntax.program, TargetLayout::POINTER64);
        assert_eq!(wide.diagnostics[0].code, "E0830");
    }

    #[test]
    fn positive_static_corpus_computes_real_values_and_types() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
        let mut failures = vec![];
        for case in cases {
            if case.meta.mode != ril_test::Mode::CheckPass
                || !(case.id.starts_with("tests/conformance/static.ril")
                    || case.id.starts_with("tests/stdlib/static.ril")
                    || case.name == "static-argument-identity")
            {
                continue;
            }
            let mut units = vec![];
            let mut root = ril_compiler_core::source::FileId(0);
            for file in case.files.iter().filter(|file| file.name.ends_with(".ril")) {
                let id = ril_compiler_core::source::FileId(units.len() as u32);
                if file.name == case.root {
                    root = id;
                }
                let parsed = ril_syntax::parse_file(std::str::from_utf8(&file.bytes).unwrap(), id);
                assert!(parsed.is_ok(), "{}: {:?}", case.id, parsed.diagnostics);
                units.push(crate::modules::ModuleUnit {
                    path: std::path::PathBuf::from("/ril-static-tests").join(&file.name),
                    file: id,
                    program: parsed.program,
                    is_declaration: file.name.ends_with(".d.ril"),
                });
            }
            let project = crate::modules::resolve(units, root);
            let result = evaluate(
                &project.program,
                if case.meta.target == Some(ril_test::PointerTarget::Pointer32) {
                    TargetLayout::POINTER32
                } else {
                    TargetLayout::POINTER64
                },
            );
            if !result.diagnostics.is_empty() || !result.unsupported.is_empty() {
                failures.push(format!(
                    "{}: {:?} {:?}",
                    case.id, result.diagnostics, result.unsupported
                ));
            }
        }
        assert!(
            failures.is_empty(),
            "{} cases failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn static_reference_aliases_reuse_published_storage() {
        let parsed =
            ril_syntax::parse("meta let A = [1]\nmeta let B = A\nmeta let C = Array::reverse(A)");
        let evaluated = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            evaluated.diagnostics.is_empty(),
            "{:?}",
            evaluated.diagnostics
        );
        assert!(
            evaluated.unsupported.is_empty(),
            "{:?}",
            evaluated.unsupported
        );
        let StmtKind::Binding(b) = &evaluated.program.statements[1].kind else {
            panic!()
        };
        let StmtKind::Binding(a) = &evaluated.program.statements[0].kind else {
            panic!()
        };
        assert_eq!(a.value.kind, b.value.kind);
        let StmtKind::Binding(c) = &evaluated.program.statements[2].kind else {
            panic!()
        };
        assert_ne!(b.value.kind, c.value.kind);
    }

    #[test]
    fn unused_meta_definitions_still_check_types_without_executing_panics() {
        for (text, expected) in [
            ("meta fn wrong() -> str { 1 }", "E0301"),
            (
                "meta fn branches() -> int { if false { \"bad\" } else { 1 } }",
                "E0301",
            ),
        ] {
            let parsed = ril_syntax::parse(text);
            let result = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == expected),
                "{:?}",
                result.diagnostics
            );
        }
        let parsed = ril_syntax::parse("meta fn deferred() { assert(false) }");
        let result = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(result.static_definitions.len(), 1);
        assert!(result.static_definitions[0].is_meta);
    }

    #[test]
    fn erased_static_queries_do_not_hide_bad_branches_arguments_or_result_duties() {
        for text in [
            "meta let VALUE = if true { 1 } else { false }",
            "meta fn identity(value: []int) -> []int { value }\nmeta let VALUE = identity([\"bad\"])",
            "meta fn identity<T>(value: T) -> T { value }\nmeta let VALUE: str = identity(1)",
        ] {
            let parsed = ril_syntax::parse(text);
            assert!(parsed.is_ok(), "{text}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{text}: {:?}",
                output.diagnostics
            );
        }
        for text in [
            "meta fn bad() -> int { let r = Err(\"lost\"); 1 }",
            "meta let VALUE = len([Err(\"lost\")])",
        ] {
            let parsed = ril_syntax::parse(text);
            assert!(parsed.is_ok(), "{text}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{text}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        {
            let text = "type Bad = \\T -> { let r = Err(\"lost\"); type<T> }";
            let parsed = ril_syntax::parse(text);
            assert!(parsed.is_ok(), "{text}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                !output.unsupported.is_empty(),
                "{text} erased an unverified Result flow"
            );
        }
    }

    #[test]
    fn aliases_have_structural_guards_and_float_identity_has_ieee_bits() {
        let parsed = ril_syntax::parse(
            "type First = { following: Second }\ntype Second = { previous: First }",
        );
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0313")
        );
        let parsed = ril_syntax::parse(
            "type Node = { following: ?Node }\nmeta let _ = assert(1.0000000596046447753906250000000001f32 != 1.0f32)\ntype Token<value: f64>(int)\nmeta let _ = assert(type<Token<0.0>> != type<Token<-0.0>>)\nmeta let _ = assert(type<Token<0.0 / 0.0>> == type<Token<0.0 / 0.0>>)\nmeta let _ = assert((0.0 / 0.0) != (0.0 / 0.0))",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }
    #[test]
    fn unused_static_bodies_keep_literal_and_nested_type_argument_validation() {
        let syntax = ril_syntax::parse("meta let LOW = -128i8\nmeta let _ = assert(LOW == -128i8)");
        let output = evaluate(&syntax.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        for (source, code) in [
            (
                "meta fn invalid() -> int { let value = 99999999999999999999999999999999999; 1 }",
                "E0326",
            ),
            (
                "type Identity = \\T -> type<T>\ntype Bad = \\T -> Identity<Missing>",
                "E0204",
            ),
        ] {
            let syntax = ril_syntax::parse(source);
            assert!(syntax.is_ok(), "{:?}", syntax.diagnostics);
            let output = evaluate(&syntax.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        let syntax = ril_syntax::parse("meta fn bad() -> int { return \"wrong\"; 1 }");
        let output = evaluate(&syntax.program, TargetLayout::POINTER64);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301")
        );
    }
    #[test]
    fn explicit_static_returns_and_fallible_bindings_have_callable_targets() {
        let parsed = ril_syntax::parse(
            "meta fn extract(input: ?int) -> int { let Some(value) = input else { return 0 }; return value }\nmeta let _ = assert(extract(None) == 0)\nmeta let _ = assert(extract(Some(4)) == 4)\nmeta let _ = assert(Array::map([1], \\value -> { return value + 1 }) == [2])\ntype ReturnType = \\T -> { return type<T> }\ntype Returned = ReturnType<int>\nmeta let _ = assert(type<Returned> == type<int>)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }
    #[test]
    fn nested_static_declarations_keep_lexical_identity_and_captured_values() {
        let parsed = ril_syntax::parse(
            "meta fn factory(number: int) -> fn() -> int { helper\nwhere\nmeta fn helper() -> int { number }\n}\nmeta let FIRST = factory(1)\nmeta let SECOND = factory(2)\nmeta let _ = assert(FIRST() == 1 && SECOND() == 2)\nfn example() { meta let LOCAL = helper()\nwhere\nmeta fn helper() -> int { 3 }\n}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        assert_eq!(output.static_definitions.len(), 3);
        assert_ne!(
            output.static_definitions[1].name,
            output.static_definitions[2].name
        );
        for source in [
            "meta fn same() -> int { 1 }\nfn example(same: fn() -> int) {\nwhere\nmeta fn bad() -> int { same() }\n}",
            "fn example(number: int) {\nwhere\nmeta fn bad() -> int { number }\n}",
            "meta fn same() -> int { 1 }\nfn example() {\nwhere\nfn same() -> int { 2 }\nmeta fn bad() -> int { same() }\n}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                !output.diagnostics.is_empty() || !output.unsupported.is_empty(),
                "unverified runtime capture became a static value: {source}"
            );
        }
    }
    #[test]
    fn static_halt_proof_is_transitive_and_independent_of_evaluation_requests() {
        for source in [
            "halt type Spin = \\T -> Spin<T>",
            "type Spin = \\T -> Spin<T>\nhalt type Claim = \\T -> Spin<T>",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0820"),
                "{:?}",
                output.diagnostics
            );
        }
        let parsed = ril_syntax::parse(
            "type Identity = \\T -> type<T>\nhalt type Finite = \\T -> Identity<T>",
        );
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        assert!(
            output
                .static_termination
                .values()
                .all(|judgment| !judgment.unresolved && !judgment.may_diverge)
        );
    }
    #[test]
    fn static_structural_patterns_bind_array_map_and_optional_parts() {
        let parsed = ril_syntax::parse(
            "halt type Element = \\T -> match type<T> { type<[]let E> -> type<E>, type<[let _: let V]> -> type<V>, type<Option<let U>> -> type<U>, _ -> type<never> }\ntype A = Element<[2]int>\ntype M = Element<[str: bool]>\ntype O = Element<?int>\nmeta let _ = assert(type<A> == type<int> && type<M> == type<bool> && type<O> == type<int>)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }
    #[test]
    fn type_function_lexical_values_and_actual_argument_contexts_do_not_mix() {
        let parsed = ril_syntax::parse(
            "meta let SIZE = 1\ntype Pick = \\T -> if SIZE == 1 { type<u8> } else { type<i64> }\ntype Pair = \\left: int, right: int -> if left == 1 && right == 2 { type<u8> } else { type<i64> }\ntype Token<size: int = SIZE>(int)\nmeta fn invoke() -> int { meta let SIZE = 2; byte_size(type<Pick<int>>) }\nmeta fn swapped(left: int, right: int) -> int { byte_size(type<Pair<right, left>>) }\nmeta fn defaults() -> bool { meta let SIZE = 2; type<Token> == type<Token<1>> }\nmeta let _ = assert(invoke() == 1 && swapped(2, 1) == 1 && defaults())",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }
    #[test]
    fn static_data_computation_keeps_format_and_map_key_constraints() {
        let parsed = ril_syntax::parse(
            "meta let VALUE = \"{1}:{true}\"\nmeta let _ = assert(VALUE == \"1:true\")",
        );
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        for (source, code) in [
            ("meta fn bad() -> str { \"{true:.2}\" }", "E0329"),
            ("meta let VALUE = Map::keys([1.0: 1])", "E0328"),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
    }
    #[test]
    fn type_function_bounds_and_constructor_kinds_are_checked_even_if_unused_by_body() {
        for (source, code) in [
            (
                "type Ignore = \\T: { id: int } -> type<int>\ntype Bad = Ignore<str>",
                "E0301",
            ),
            (
                "type Ignore = \\M: Type -> Type -> type<int>\ntype Bad = Ignore<Result>",
                "E0306",
            ),
            (
                "type Identity = \\T -> type<T>\ntype Unused = \\T -> Identity<int, str>",
                "E0340",
            ),
            (
                "type Identity = \\T -> type<T>\ntype Unused = \\T -> Identity<1>",
                "E0323",
            ),
            ("type Unused = \\M: Type -> Type -> type<M>", "E0306"),
            (
                "type NeedId = \\T: { id: int } -> type<int>\ntype Unused = \\T -> NeedId<str>",
                "E0301",
            ),
            (
                "type NeedId = \\T: { id: int } -> type<int>\ntype Unused = \\T -> NeedId<{ id: int, name: str }>",
                "E0301",
            ),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        let parsed = ril_syntax::parse(
            "type Rest = \\T: { id: int, ..R } -> type<R>\ntype Extra = Rest<{ id: int, name: str }>\nmeta let _ = assert(type<Extra> == type<{ name: str }>)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        let parsed = ril_syntax::parse(
            "type Apply = \\M: Type -> Type, T -> M<T>\ntype Forward = \\N: Type -> Type, T -> Apply<N, T>\ntype Value = Forward<Option, int>\nmeta let _ = assert(type<Value> == type<Option<int>>)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        let parsed = ril_syntax::parse(
            "meta fn ignore<T: { id: int }>(value: T) -> int { 1 }\nmeta let VALUE = ignore(1)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301")
                && output.unsupported.is_empty(),
            "invalid structural meta argument must be rejected: diagnostics={:?}, unsupported={:?}",
            output.diagnostics,
            output.unsupported,
        );
    }

    #[test]
    fn fixed_array_facts_survive_static_calls_without_crossing_branch_joins() {
        let source = "meta let SIZE = 2\nmeta fn same(value: [SIZE]int) -> [2]int { value }\nmeta fn built() -> [3]int { Array::concat(Array::reverse([1, 2]), [3]) }\nmeta fn mapped() -> [2]int { Array::map([1, 2], \\value -> value + 1) }\nmeta fn local() -> [2]int { let size = len([1, 2]); let value: [size]int = [3, 4]; value }\nmeta let _ = assert(same([1, 2]) == [1, 2] && built() == [2, 1, 3] && mapped() == [2, 3] && local() == [3, 4])";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        for (source, code) in [
            ("meta fn wrong() -> [2]int { [1] }", "E0301"),
            (
                "meta fn same(value: [2]int) -> [2]int { value }\nmeta let VALUE = same([1])",
                "E0301",
            ),
            ("meta fn wrong() { let value: [-1]int = [] }", "E0815"),
            ("meta fn wrong() { let value: [true]int = [] }", "E0323"),
            (
                "meta fn wrong(size: int) { let value: [size]int = [] }",
                "E0814",
            ),
            (
                "meta fn wrong(flag: bool) { let size = if flag { 1 } else { 2 }; let value: [size]int = [1] }",
                "E0814",
            ),
            (
                "meta fn wrong(flag: bool) -> [1]int { if flag { [1] } else { [1, 2] } }",
                "E0301",
            ),
            (
                "meta fn wrong() { let items = [1, 2]; let size = items[1]; let value: [size]int = [0] }",
                "E0814",
            ),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source} expected {code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        let parsed = ril_syntax::parse(
            "meta fn early(flag: bool) -> int { if flag { return 1 } else { 2 } }",
        );
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }

    #[test]
    fn where_tiers_and_nominal_confinement_use_lexical_alias_meaning() {
        for source in [
            "fn example() -> Token\nwhere\n type Token = int\n{ 1 }",
            "type Token(int)\ntype Existing = Token\nfn example(value: Existing) -> Existing\nwhere\n type Token(str)\n{ value }",
            "fn example(value: Local) -> int\nwhere\n type Local(int)\n{ inner(value) }",
            "fn example() -> Dropped<Local>\nwhere\n type Local(int)\n type Dropped<T> = int\n{ 1 }",
            "type Internal = int\nfn example() -> Wrapper\nwhere\n type Wrapper = { value: Internal }\n{ .{value: 1}\nwhere\n type Internal = str\n}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output.diagnostics.is_empty(),
                "{source}: {:?}",
                output.diagnostics
            );
            assert!(
                output.unsupported.is_empty(),
                "{source}: {:?}",
                output.unsupported
            );
        }
        for (source, code) in [
            (
                "fn example(action: Action) { action()\nwhere\n type Action = fn() -> ()\n}",
                "E0706",
            ),
            (
                "fn example() -> Wrapper\nwhere\n type Wrapper = { value: Internal }\n{ .{value: 1}\nwhere\n type Internal = int\n}",
                "E0705",
            ),
            (
                "fn example() -> Local\nwhere\n type Local(int)\n{ Local(1) }",
                "E0315",
            ),
            (
                "fn example() -> Wrapped\nwhere\n type Local(int)\n type Wrapped = { value: Local }\n{ .{value: Local(1)} }",
                "E0315",
            ),
            (
                "fn example() -> fn(Local) -> int\nwhere\n type Local(int)\n{ \\value -> inner(value) }",
                "E0315",
            ),
            (
                "fn example() -> Same\nwhere\n type Same = int\n{ 1\nwhere\n type Same = int\n}",
                "E0203",
            ),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source} expected {code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
    }

    #[test]
    fn finite_static_aggregate_sorts_keep_tuple_unit_optional_and_length_identity() {
        let source = "type Choice = \\value: (int, ?str), empty: () -> if value.0 == 1 { type<u8> } else { type<u16> }\ntype First = Choice<(1, Some(\"a\")), ()>\ntype Second = Choice<(2, None), ()>\nmeta let _ = assert(type<First> == type<u8> && type<Second> == type<u16>)\ntype Sized = \\values: [2]int -> type<int>\ntype Valid = Sized<[1, 2]>";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        for source in [
            "type Choice = \\value: (int, ?str) -> type<int>\ntype Wrong = Choice<(1, Some(2))>",
            "type Sized = \\values: [2]int -> type<int>\ntype Wrong = Sized<[1]>",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0323"),
                "{:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
    }

    #[test]
    fn runtime_mutual_recursion_is_not_executed_during_static_preprocessing() {
        let source = "fn parity(value: int) -> bool { even(value)\nwhere\n fn even(value: int) -> bool { if value == 0 { true } else { odd(value - 1) } }\n fn odd(value: int) -> bool { if value == 0 { false } else { even(value - 1) } }\n}";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        assert_eq!(output.program.statements.len(), 1);
    }

    #[test]
    fn typeof_checks_scalar_expressions_without_evaluating_faults_or_runtime_calls() {
        let source = "fn fail() -> int { assert(false); 1 }\nfn spin() -> never { loop {} }\ntype Inferred = typeof fail()\ntype Bottom = typeof spin()\ntype Local = \\T -> { let value = 1; type<typeof value> }\ntype Value = Local<str>\nmeta let _ = assert(type<Inferred> == type<int> && type<Bottom> == type<never> && type<Value> == type<int> && type<typeof (1 / 0)> == type<int>)";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
        let parsed = ril_syntax::parse("meta let _ = assert(type<typeof (true + 1)> == type<int>)");
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn incomplete_static_qualifications_are_not_erased_when_definitions_are_unused() {
        for source in [
            "meta fn erased(value: { mut count: int }) -> { count: int } { value }",
            "type Mutable = { mut count: int }\nmeta fn erased(value: Mutable) -> { count: int } { value }",
            "meta fn erased(callback: fn(mut []int) -> (), items: []int) { callback(items) }",
            "type Mutable = { mut count: int }\ntype NeedRead = \\T: { count: int } -> type<int>\ntype Unused = \\T -> NeedRead<Mutable>",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
            let output = evaluate(&parsed.program, TargetLayout::POINTER64);
            assert!(
                !output.unsupported.is_empty(),
                "unverified qualification disappeared: {source}: {:?}",
                output.diagnostics
            );
        }
    }

    #[test]
    fn normalized_static_identity_ignores_literal_spelling_and_source_locations() {
        let source = "type Token<value: ?int>(int)\ntype Label<value: str>(int)\ntype Data<value: bytes>(int)\nmeta let _=assert(type<Token<Some(1)>> == type<Token<Some(0x1)>>)\nmeta let _=assert(type<Label<\"a\">> == type<Label<\"\\u{61}\">>)\nmeta let _=assert(type<Data<b\"a\">> == type<Data<b\"\\x61\">>)";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(output.unsupported.is_empty(), "{:?}", output.unsupported);
    }

    #[test]
    fn nested_static_calls_stop_at_an_explicit_resource_boundary() {
        let source = format!(
            "meta fn count(value:int)->int {{ if value==0 {{0}} else {{ {}count(value-1)}} }}\nmeta let VALUE=count(100)",
            "- ".repeat(40)
        );
        let parsed = ril_syntax::parse(&source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let output = evaluate(&parsed.program, TargetLayout::POINTER64);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(
            output
                .unsupported
                .iter()
                .any(|feature| feature.description.contains("stack budget")),
            "{:?}",
            output.unsupported
        );
    }

    #[test]
    fn static_negative_corpus_enforces_families_budgets_and_type_computation() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
        let mut failures = vec![];
        for case in cases {
            if !(case.id.starts_with("tests/conformance/static.ril")
                || case.id.starts_with("tests/conformance/generics.ril"))
            {
                continue;
            }
            let expected: Vec<_> = case
                .errors
                .iter()
                .filter(|code| {
                    matches!(
                        code.as_str(),
                        "E0313"
                            | "E0316"
                            | "E0317"
                            | "E0318"
                            | "E0319"
                            | "E0320"
                            | "E0340"
                            | "E0341"
                            | "E0342"
                            | "E0343"
                            | "E0810"
                            | "E0811"
                            | "E0812"
                            | "E0813"
                            | "E0830"
                            | "E0831"
                            | "E0102"
                            | "E0210"
                            | "E0306"
                    )
                })
                .collect();
            if expected.is_empty() {
                continue;
            }
            let mut codes = vec![];
            for file in case.files.iter().filter(|file| file.name.ends_with(".ril")) {
                let parsed = ril_syntax::parse(std::str::from_utf8(&file.bytes).unwrap());
                codes.extend(
                    parsed
                        .diagnostics
                        .iter()
                        .map(|diagnostic| diagnostic.code.clone()),
                );
                let result = evaluate(&parsed.program, TargetLayout::POINTER64);
                codes.extend(
                    result
                        .diagnostics
                        .into_iter()
                        .map(|diagnostic| diagnostic.code),
                );
            }
            for code in expected {
                if !codes.contains(code) {
                    failures.push(format!("{} expected {code}, got {codes:?}", case.id));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "{} cases failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}
