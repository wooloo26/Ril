//! One original-header ingress. Structural types remain a finite graph;
//! declaration sorts alone admit normalized Const coordinates.
use super::super::{CallableRowIdentity, CallableRowOrigin};
use super::super::{
    SourceBuilder, SourceContainer, SourceField, SourceLength, SourceNode, SourceScalar,
    SourceSchema, SourceTypeId, SourceTypesError, WorkLimit,
};
use crate::hir::lexical::{LexicalBindings, TypeNameBinding};
use crate::{hir::nodes as hir, static_eval};
use ril_compiler_core::{
    ids::{GenericParamId, StmtId, TypeExprId},
    target::TargetLayout,
};
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
#[path = "constructor_instance.rs"]
mod constructor_instance;
#[path = "original_header/declaration_syntax.rs"]
mod declaration_syntax;
pub(crate) use constructor_instance::{DeclaredConstructorInstance, constructor_instance};

#[derive(Clone, Copy)]
pub(crate) struct HeaderContext<'a> {
    pub(crate) declarations: &'a BTreeMap<String, TypeDeclaration>,
    pub(crate) program: &'a Program,
    pub(crate) hir: &'a hir::HirProgram,
    pub(crate) lexical: &'a LexicalBindings,
    pub(crate) binders: &'a BTreeMap<String, String>,
    pub(crate) functions: &'a [crate::sema::model::FunctionInfo],
    pub(crate) generic_binders: &'a BTreeMap<String, crate::sema::GenericBinder>,
    pub(crate) layout: TargetLayout,
}

/// Interpret only genuine generic declarations whose UID is already available
/// in this frozen context. Names and UID token spellings cannot choose an owner.
fn generic_definitions(
    id: GenericParamId,
    functions: &[crate::sema::model::FunctionInfo],
    hir: &hir::HirProgram,
    work: &mut WorkLimit,
) -> Result<
    (
        std::collections::BTreeSet<ril_compiler_core::ids::DefinitionId>,
        usize,
    ),
    SourceTypesError,
> {
    work.charge(1)?;
    let canonical = hir.generic(id).ok_or(SourceTypesError::MissingNode)?;
    let hir::LexicalOwner::Declaration(owner) = canonical.info.owner else {
        return Err(SourceTypesError::Unresolved);
    };
    let statement = hir.statement(owner).ok_or(SourceTypesError::MissingNode)?;
    let hir::StmtKind::Function(original) = &statement.kind else {
        return Err(SourceTypesError::Unresolved);
    };
    work.charge(original.generics.len())?;
    let index = original
        .generics
        .iter()
        .position(|parameter| *parameter == id)
        .ok_or(SourceTypesError::Unresolved)?;
    let lookup_cost = |len: usize| len.checked_ilog2().unwrap_or(0) as usize + 1;
    work.charge(functions.len())?;
    let mut definitions = std::collections::BTreeSet::new();
    for function in functions {
        if function.hir_id != Some(owner) {
            continue;
        }
        let parameter = function
            .syntax
            .generics
            .get(index)
            .ok_or(SourceTypesError::MissingNode)?;
        work.text(&parameter.name)?;
        work.text(&canonical.name)?;
        if parameter.hir_id != Some(id) || parameter.name != canonical.name {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(lookup_cost(definitions.len()))?;
        definitions.insert(function.definition);
    }
    if definitions.is_empty() {
        return Err(SourceTypesError::MissingNode);
    }
    Ok((definitions, index))
}

fn generic_parameter(
    id: GenericParamId,
    functions: &[crate::sema::model::FunctionInfo],
    registry: &BTreeMap<String, crate::sema::GenericBinder>,
    available: &BTreeMap<String, String>,
    hir: &hir::HirProgram,
    work: &mut WorkLimit,
) -> Result<String, SourceTypesError> {
    let (definitions, index) = generic_definitions(id, functions, hir, work)?;
    work.charge(available.len())?;
    let canonical = hir.generic(id).ok_or(SourceTypesError::MissingNode)?;
    let lookup_cost = |len: usize| len.checked_ilog2().unwrap_or(0) as usize + 1;
    let mut selected = None;
    for identity in available.values() {
        work.text(identity)?;
        work.charge(lookup_cost(registry.len()) * (1 + identity.len().div_ceil(32)))?;
        let Some(binder) = registry.get(identity) else {
            // Implicit record rows and other non-function roles have their own
            // admission. They cannot supply an original GenericParamId here.
            continue;
        };
        work.charge(lookup_cost(definitions.len()))?;
        if binder.index as usize != index || !definitions.contains(&binder.definition) {
            continue;
        }
        work.text(&binder.name)?;
        work.text(&binder.identity)?;
        if binder.identity != *identity || binder.name != canonical.name {
            return Err(SourceTypesError::Unresolved);
        }
        if selected
            .as_ref()
            .is_some_and(|previous| previous != identity)
        {
            return Err(SourceTypesError::Unresolved);
        }
        selected = Some(identity.clone());
    }
    selected.ok_or(SourceTypesError::Unresolved)
}

/// This is invoked only for an original header's typed elaboration request.
/// Actual observed Source graphs never enter the static interpreter here.
pub(crate) fn elaborate_original_header(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    charge_syntax(syntax, work)?;
    let header = Header::new(context)?;
    header.validate_syntax(syntax, work)?;
    let elaborated = header.elaborate(syntax, work)?;
    build(&elaborated, context, work, false).map(|schema| schema.with_original(syntax.hir_id))
}

pub(crate) fn original_header(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    build(syntax, context, work, true)
}

/// Runtime values of an original Key parameter use the declared product's
/// scalar carrier. This supplies neither membership nor a Type-binder view.
pub(crate) fn key_carrier_source(
    parameter: GenericParamId,
    identity: &str,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    work.text(identity)?;
    let actual = generic_parameter(
        parameter,
        context.functions,
        context.generic_binders,
        context.binders,
        context.hir,
        work,
    )?;
    if actual != identity {
        return Err(SourceTypesError::Unresolved);
    }
    let generic = context
        .hir
        .generic(parameter)
        .ok_or(SourceTypesError::MissingNode)?;
    let binder = context
        .generic_binders
        .get(identity)
        .ok_or(SourceTypesError::MissingNode)?;
    work.charge(context.functions.len())?;
    let declaration = context
        .functions
        .iter()
        .find(|function| function.definition == binder.definition)
        .ok_or(SourceTypesError::MissingNode)?;
    let original_bound = declaration
        .syntax
        .generics
        .get(binder.index as usize)
        .and_then(|parameter| parameter.bound.as_ref())
        .ok_or(SourceTypesError::MissingNode)?;
    if original_bound.hir_id != generic.bound {
        return Err(SourceTypesError::Unresolved);
    }
    let header = Header::new(context)?;
    header.validate_syntax(original_bound, work)?;
    let bound = generic
        .bound
        .and_then(|id| context.hir.type_expression(id))
        .ok_or(SourceTypesError::MissingNode)?;
    let hir::TypeKind::KeyOf(base) = &bound.kind else {
        return Err(SourceTypesError::Unresolved);
    };
    let carrier = header.key_carrier(*base, work, 0)?;
    SourceSchema::scalar(carrier, None, work)
}

/// An original row is identified by its canonical header and all visible
/// function binders, including a binder occurring only inside the row.
pub(crate) fn callable_row_identity(
    origin: CallableRowOrigin,
    annotations: &[Annotation],
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<Option<CallableRowIdentity<SourceSchema>>, SourceTypesError> {
    let mut header = Header::new(context)?;
    let Some(row) = header.callable_row(origin, annotations, work)? else {
        return Ok(None);
    };
    let types = header.builder.freeze(work)?;
    work.charge(row.parameters.len() + 1)?;
    Ok(Some(CallableRowIdentity {
        origin: row.origin,
        parameters: row
            .parameters
            .into_iter()
            .map(|(id, root)| Ok((id, SourceSchema::frozen_view(&types, root, None, work)?)))
            .collect::<Result<_, SourceTypesError>>()?,
    }))
}

#[derive(Clone)]
pub(crate) struct EffectSource {
    pub(crate) declaration: std::sync::Arc<EffectDeclaration>,
    pub(crate) arguments: std::sync::Arc<[TypeExpr]>,
    pub(crate) operations: SourceSchema,
}

pub(crate) enum EffectSourceError {
    Source(SourceTypesError),
    Normalization(static_eval::ArgumentNormalizationError),
}
impl From<SourceTypesError> for EffectSourceError {
    fn from(error: SourceTypesError) -> Self {
        Self::Source(error)
    }
}
impl std::fmt::Display for EffectSourceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(error) => write!(formatter, "{error}"),
            Self::Normalization(static_eval::ArgumentNormalizationError::Diagnostic(
                code,
                message,
            )) => write!(formatter, "{code}: {message}"),
            Self::Normalization(static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                formatter.write_str(message)
            }
        }
    }
}

/// One authenticated declaration instance produces all operation signatures in
/// one arena. Consumers project an operation; they never reinterpret a normalized
/// head as original syntax or reconstruct an observed graph through a key.
pub(crate) fn effect_source(
    source: StmtId,
    declaration: &EffectDeclaration,
    arguments: &[TypeExpr],
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<EffectSource, EffectSourceError> {
    work.charge(1)?;
    let mut remaining = work.remaining();
    let admitted = static_eval::charge_effect_declaration_clone(declaration, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    admitted.ok_or(SourceTypesError::BudgetExceeded)?;
    let mut statement = Stmt {
        hir_id: Some(source),
        span: declaration.span,
        kind: StmtKind::Effect(declaration.clone()),
    };
    let mut remaining = work.remaining();
    let admitted = static_eval::charge_statement_syntax_clone(&statement, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    admitted.ok_or(SourceTypesError::BudgetExceeded)?;
    context
        .hir
        .validate_statement_syntax(&mut statement, source, hir::HirLimits::default())
        .map_err(super::lexical_error)?;
    let StmtKind::Effect(effect) = statement.kind else {
        return Err(SourceTypesError::Unresolved.into());
    };
    let mut remaining = work.remaining();
    let normalized = static_eval::effects::instantiate_bounded(
        &effect,
        arguments,
        context.declarations,
        context.layout,
        &mut remaining,
    );
    work.charge(work.remaining() - remaining)?;
    let normalized = normalized.map_err(EffectSourceError::Normalization)?;
    work.charge(normalized.declaration.operations.len())?;
    let mut operations = Vec::with_capacity(normalized.declaration.operations.len());
    let mut names = BTreeMap::new();
    for (index, header) in normalized.declaration.operations.iter().enumerate() {
        work.text(&header.name)?;
        work.charge(1 + names.len().checked_ilog2().unwrap_or(0) as usize)?;
        if names.insert(header.name.clone(), index as u32).is_some() {
            return Err(SourceTypesError::Unresolved.into());
        }
        let mut remaining = work.remaining();
        let admitted = static_eval::charge_function_syntax_clone(header, &mut remaining);
        work.charge(work.remaining() - remaining)?;
        admitted.ok_or(SourceTypesError::BudgetExceeded)?;
        operations.push(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: header.span,
            kind: TypeKind::Callable {
                parameters: header.parameters.clone(),
                result: header.return_type.clone().map(Box::new),
                annotations: header.annotations.clone(),
            },
        });
    }
    let syntax = TypeExpr {
        hir_id: None,
        text: String::new(),
        span: declaration.span,
        kind: TypeKind::Tuple(operations),
    };
    let operations = build(&syntax, context, work, false)?;
    Ok(EffectSource {
        declaration: std::sync::Arc::new(normalized.declaration),
        arguments: normalized.arguments.into(),
        operations,
    })
}

fn build(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
    authenticate: bool,
) -> Result<SourceSchema, SourceTypesError> {
    charge_syntax(syntax, work)?;
    work.charge(context.binders.len())?;
    for (name, identity) in context.binders {
        work.text(name)?;
        work.text(identity)?;
    }
    let mut binders = context.binders.clone();
    for identity in context.binders.values() {
        work.charge(1)?;
        work.text(identity)?;
        let token = format!("\0effect-binder:{identity}");
        if binders
            .insert(token, identity.clone())
            .is_some_and(|old| old != *identity)
        {
            return Err(SourceTypesError::Unresolved);
        }
    }
    let mut header = Header::new(HeaderContext {
        binders: &binders,
        ..context
    })?;
    if authenticate {
        header.validate_syntax(syntax, work)?;
    }
    let root = header.ty(syntax, true, authenticate, work, 0)?;
    let types = header.builder.freeze(work)?;
    super::super::reception::complete(&types, root, work)?;
    SourceSchema::frozen_view(&types, root, syntax.hir_id, work)
}

fn charge_syntax(syntax: &TypeExpr, work: &mut WorkLimit) -> Result<(), SourceTypesError> {
    let mut remaining = work.remaining();
    let admitted = static_eval::charge_type_syntax_clone(syntax, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    admitted.ok_or(SourceTypesError::BudgetExceeded)
}

struct Header<'a> {
    context: HeaderContext<'a>,
    aliases: BTreeMap<StmtId, SourceTypeId>,
    builder: SourceBuilder,
    declarations: Option<BTreeMap<StmtId, &'a Stmt>>,
    generic_parameters: BTreeMap<GenericParamId, String>,
}

impl<'a> Header<'a> {
    fn new(context: HeaderContext<'a>) -> Result<Self, SourceTypesError> {
        Ok(Self {
            context,
            aliases: BTreeMap::new(),
            builder: SourceBuilder::new()?,
            declarations: None,
            generic_parameters: BTreeMap::new(),
        })
    }

    fn callable_row(
        &mut self,
        origin: CallableRowOrigin,
        annotations: &[Annotation],
        work: &mut WorkLimit,
    ) -> Result<Option<CallableRowIdentity>, SourceTypesError> {
        work.charge(1 + annotations.len())?;
        let (canonical, mut owner) = match origin {
            CallableRowOrigin::Declaration(id) => {
                let statement = self
                    .context
                    .hir
                    .statement(id)
                    .ok_or(SourceTypesError::MissingNode)?;
                let hir::StmtKind::Function(function) = &statement.kind else {
                    return Err(SourceTypesError::Unresolved);
                };
                (&function.annotations, hir::LexicalOwner::Declaration(id))
            }
            CallableRowOrigin::Type(id) => {
                let syntax = self
                    .context
                    .hir
                    .type_expression(id)
                    .ok_or(SourceTypesError::MissingNode)?;
                let hir::TypeKind::Callable { annotations, .. } = &syntax.kind else {
                    return Err(SourceTypesError::Unresolved);
                };
                (annotations, syntax.info.owner)
            }
            CallableRowOrigin::Lambda(id) => {
                let expression = self
                    .context
                    .hir
                    .expression(id)
                    .ok_or(SourceTypesError::MissingNode)?;
                let hir::ExprKind::Lambda { annotations, .. } = &expression.kind else {
                    return Err(SourceTypesError::Unresolved);
                };
                (annotations, expression.info.owner)
            }
        };
        if canonical.len() != annotations.len() {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(canonical.len())?;
        let mut needs_original = false;
        for (actual, original) in annotations.iter().zip(canonical) {
            work.text(&actual.text)?;
            work.text(&original.text)?;
            work.charge(actual.text.len() + 1)?;
            if actual.kind != original.kind || actual.text != original.text {
                return Err(SourceTypesError::Unresolved);
            }
            needs_original |=
                super::super::annotation_identity::text_requires_original(&actual.text);
        }
        if !needs_original {
            return Ok(None);
        }
        let mut seen = BTreeSet::new();
        let mut parameters = BTreeMap::new();
        loop {
            work.charge(2 + seen.len().checked_ilog2().unwrap_or(0) as usize)?;
            if !seen.insert(owner) {
                return Err(SourceTypesError::AliasCycle);
            }
            match owner {
                hir::LexicalOwner::Module => break,
                hir::LexicalOwner::Declaration(id) => {
                    let statement = self
                        .context
                        .hir
                        .statement(id)
                        .ok_or(SourceTypesError::MissingNode)?;
                    if let hir::StmtKind::Function(function) = &statement.kind {
                        work.charge(self.context.functions.len() + function.generics.len())?;
                        let mut definitions = BTreeSet::new();
                        for function in self
                            .context
                            .functions
                            .iter()
                            .filter(|function| function.hir_id == Some(id))
                        {
                            work.charge(
                                2 + definitions.len().checked_ilog2().unwrap_or(0) as usize,
                            )?;
                            definitions.insert(function.definition);
                        }
                        let mut admitted = BTreeMap::new();
                        for definition in definitions {
                            let map = super::super::owned_header_binders::function(
                                definition,
                                id,
                                self.context.functions,
                                self.context.generic_binders,
                                self.context.hir,
                                work,
                            )?;
                            for (parameter, identity) in map {
                                work.charge(self.context.binders.len())?;
                                if self
                                    .context
                                    .binders
                                    .values()
                                    .any(|available| available == &identity)
                                {
                                    work.text(&identity)?;
                                    if admitted
                                        .insert(parameter, identity.clone())
                                        .is_some_and(|previous| previous != identity)
                                    {
                                        return Err(SourceTypesError::Unresolved);
                                    }
                                }
                            }
                        }
                        for parameter in &function.generics {
                            let canonical = self
                                .context
                                .hir
                                .generic(*parameter)
                                .ok_or(SourceTypesError::MissingNode)?;
                            work.text(&canonical.name)?;
                            let type_sort = canonical
                                .name
                                .chars()
                                .next()
                                .is_some_and(char::is_uppercase)
                                && match canonical.bound {
                                    None => true,
                                    Some(bound) => match &self
                                        .context
                                        .hir
                                        .type_expression(bound)
                                        .ok_or(SourceTypesError::MissingNode)?
                                        .kind
                                    {
                                        hir::TypeKind::Name { path, arguments } => {
                                            work.charge(path.len() + arguments.len())?;
                                            for part in path {
                                                work.text(part)?;
                                            }
                                            path == &["Type"] && arguments.is_empty()
                                        }
                                        hir::TypeKind::Record { .. } => true,
                                        _ => false,
                                    },
                                };
                            if !type_sort {
                                return Err(SourceTypesError::Unresolved);
                            }
                            let identity = admitted
                                .remove(parameter)
                                .ok_or(SourceTypesError::Unresolved)?;
                            work.charge(
                                2 + parameters.len().checked_ilog2().unwrap_or(0) as usize,
                            )?;
                            let root = self.builder.insert(SourceNode::Binder(identity), work)?;
                            if parameters.insert(*parameter, root).is_some() {
                                return Err(SourceTypesError::Unresolved);
                            }
                        }
                    }
                    owner = statement.info.owner;
                }
                hir::LexicalOwner::Lambda(id) => {
                    owner = self
                        .context
                        .hir
                        .expression(id)
                        .ok_or(SourceTypesError::MissingNode)?
                        .info
                        .owner
                }
                hir::LexicalOwner::CallableType(id) => {
                    owner = self
                        .context
                        .hir
                        .type_expression(id)
                        .ok_or(SourceTypesError::MissingNode)?
                        .info
                        .owner
                }
                _ => return Err(SourceTypesError::Unresolved),
            }
        }
        Ok(Some(CallableRowIdentity {
            origin,
            parameters: parameters.into_iter().collect(),
        }))
    }

    fn type_binding(
        &self,
        source: TypeExprId,
        work: &mut WorkLimit,
    ) -> Result<TypeNameBinding, SourceTypesError> {
        let mut remaining = work.remaining();
        let before = remaining;
        let binding = self.context.lexical.lookup_type(source, &mut remaining);
        work.charge(before - remaining)?;
        binding.map_err(super::lexical_error)
    }

    /// A static coordinate is a run-time scalar carrier, never a Type UID.
    /// Its carrier follows the original product layout; membership and the
    /// selected key retain their separate static-argument/access receipts.
    fn key_carrier(
        &self,
        source: TypeExprId,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceScalar, SourceTypesError> {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let syntax = self
            .context
            .hir
            .type_expression(source)
            .ok_or(SourceTypesError::MissingNode)?;
        match &syntax.kind {
            hir::TypeKind::Record { .. } => Ok(SourceScalar::Str),
            hir::TypeKind::Tuple(_) => Ok(SourceScalar::Int),
            hir::TypeKind::Name { path, arguments } => {
                work.charge(path.len() + arguments.len())?;
                for part in path {
                    work.text(part)?;
                }
                match self.type_binding(source, work)? {
                    TypeNameBinding::Generic(id) => {
                        let parameter = self
                            .context
                            .hir
                            .generic(id)
                            .ok_or(SourceTypesError::MissingNode)?;
                        self.key_carrier(
                            parameter.bound.ok_or(SourceTypesError::Unresolved)?,
                            work,
                            depth + 1,
                        )
                    }
                    TypeNameBinding::Declaration(id) => {
                        let declaration = self
                            .context
                            .hir
                            .statement(id)
                            .ok_or(SourceTypesError::MissingNode)?;
                        let hir::StmtKind::Type {
                            generics,
                            value: Some(value),
                            variants,
                            nominal: false,
                            opaque: false,
                            ..
                        } = &declaration.kind
                        else {
                            return Err(SourceTypesError::Unresolved);
                        };
                        if !generics.is_empty() || !variants.is_empty() || !arguments.is_empty() {
                            return Err(SourceTypesError::Unresolved);
                        }
                        self.key_carrier(*value, work, depth + 1)
                    }
                    TypeNameBinding::Unbound
                        if matches!(path.as_slice(),[name] if name == "Immut")
                            && arguments.len() == 1 =>
                    {
                        self.key_carrier(arguments[0], work, depth + 1)
                    }
                    _ => Err(SourceTypesError::Unresolved),
                }
            }
            _ => Err(SourceTypesError::Unresolved),
        }
    }

    /// The original Name selects a declaration identity before any spelling
    /// map is consulted. The map cannot distinguish same-named local aliases.
    fn original_declaration(
        &mut self,
        id: StmtId,
        name: &str,
        work: &mut WorkLimit,
    ) -> Result<TypeDeclaration, SourceTypesError> {
        let statement = self
            .context
            .hir
            .statement(id)
            .ok_or(SourceTypesError::MissingNode)?;
        if statement.info.owner == hir::LexicalOwner::Module {
            let (retained_id, declaration) = self
                .declaration(name, work)?
                .ok_or(SourceTypesError::MissingNode)?;
            if retained_id != id {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(declaration);
        }
        if self.declarations.is_none() {
            self.declarations = Some(declaration_syntax::declarations(
                self.context.program,
                work,
            )?);
        }
        work.charge(
            self.declarations
                .as_ref()
                .ok_or(SourceTypesError::MissingNode)?
                .len()
                .checked_ilog2()
                .unwrap_or(0) as usize
                + 1,
        )?;
        let original = self
            .declarations
            .as_ref()
            .and_then(|declarations| declarations.get(&id))
            .copied()
            .ok_or(SourceTypesError::MissingNode)?;
        let StmtKind::Type(declaration) = &original.kind else {
            return Err(SourceTypesError::Unresolved);
        };
        work.text(&declaration.name)?;
        work.text(name)?;
        if declaration.name != name {
            return Err(SourceTypesError::Unresolved);
        }
        self.charge_declaration(declaration, work)?;
        self.charge_declaration(declaration, work)?;
        let mut candidate = original.clone();
        self.context
            .hir
            .validate_statement_syntax(&mut candidate, id, hir::HirLimits::default())
            .map_err(super::lexical_error)?;
        let StmtKind::Type(declaration) = candidate.kind else {
            unreachable!()
        };
        Ok(declaration)
    }

    fn validate_syntax(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        let id = syntax.hir_id.ok_or(SourceTypesError::MissingNode)?;
        // One exhaustive admission pays the clone and one pays the canonical
        // pairing before either operation visits the original tree.
        charge_syntax(syntax, work)?;
        charge_syntax(syntax, work)?;
        let mut original = syntax.clone();
        self.context
            .hir
            .validate_type_syntax(&mut original, id, hir::HirLimits::default())
            .map_err(|error| match error {
                hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
                _ => SourceTypesError::Unresolved,
            })
    }
    /// Authenticate the map entry against both the original syntax declaration
    /// and its exact module HIR node. A same-spelled replacement is not a sort.
    fn declaration(
        &self,
        name: &str,
        work: &mut WorkLimit,
    ) -> Result<Option<(StmtId, TypeDeclaration)>, SourceTypesError> {
        let Some(declaration) = self.context.declarations.get(name) else {
            return Ok(None);
        };
        work.text(name)?;
        if declaration.name != name {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(self.context.program.statements.len())?;
        let mut originals = self.context.program.statements.iter().filter(|statement| {
            matches!(&statement.kind,
                StmtKind::Type(actual) if actual.name == name)
        });
        let actual = originals.next().ok_or(SourceTypesError::Unresolved)?;
        if originals.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let id = actual.hir_id.ok_or(SourceTypesError::MissingNode)?;
        let statement = self
            .context
            .hir
            .statement(id)
            .ok_or(SourceTypesError::MissingNode)?;
        if statement.info.owner != hir::LexicalOwner::Module {
            return Err(SourceTypesError::Unresolved);
        }
        let StmtKind::Type(actual_declaration) = &actual.kind else {
            unreachable!()
        };
        // Pay clone and canonical pairing separately for both retained views.
        self.charge_declaration(actual_declaration, work)?;
        self.charge_declaration(actual_declaration, work)?;
        self.charge_declaration(declaration, work)?;
        self.charge_declaration(declaration, work)?;
        let mut original = actual.clone();
        let mut candidate = Stmt {
            hir_id: Some(id),
            span: declaration.span,
            kind: StmtKind::Type(declaration.clone()),
        };
        for syntax in [&mut original, &mut candidate] {
            self.context
                .hir
                .validate_statement_syntax(syntax, id, hir::HirLimits::default())
                .map_err(|error| match error {
                    hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
                    _ => SourceTypesError::Unresolved,
                })?;
        }
        let StmtKind::Type(declaration) = candidate.kind else {
            unreachable!()
        };
        Ok(Some((id, declaration)))
    }

    fn charge_declaration(
        &self,
        declaration: &TypeDeclaration,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        work.charge(1 + declaration.generics.len() + declaration.variants.len())?;
        work.text(&declaration.name)?;
        for generic in &declaration.generics {
            work.text(&generic.name)?;
            for ty in generic.bound.iter().chain(&generic.default) {
                charge_syntax(ty, work)?;
            }
        }
        if let Some(ty) = &declaration.value {
            charge_syntax(ty, work)?;
        }
        for variant in &declaration.variants {
            work.text(&variant.name)?;
            work.charge(variant.generics.len() + variant.annotations.len())?;
            for generic in &variant.generics {
                work.text(&generic.name)?;
                for ty in generic.bound.iter().chain(&generic.default) {
                    charge_syntax(ty, work)?;
                }
            }
            for ty in variant.payload.iter().chain(&variant.result) {
                charge_syntax(ty, work)?;
            }
            for annotation in &variant.annotations {
                work.text(&annotation.text)?;
            }
        }
        Ok(())
    }

    fn ty(
        &mut self,
        syntax: &TypeExpr,
        caller: bool,
        original: bool,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let node = match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                work.charge(path.len() + arguments.len())?;
                for part in path {
                    work.text(part)?;
                }
                let name = path.join("::");
                let binding =
                    if original {
                        Some(self.type_binding(
                            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
                            work,
                        )?)
                    } else {
                        None
                    };
                if binding == Some(TypeNameBinding::Other) {
                    return Err(SourceTypesError::Unresolved);
                }
                if let Some(TypeNameBinding::Generic(id)) = binding {
                    if !arguments.is_empty() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    let generic = self
                        .context
                        .hir
                        .generic(id)
                        .ok_or(SourceTypesError::MissingNode)?;
                    if let Some(bound) = generic.bound
                        && let hir::TypeKind::KeyOf(base) = &self
                            .context
                            .hir
                            .type_expression(bound)
                            .ok_or(SourceTypesError::MissingNode)?
                            .kind
                    {
                        generic_definitions(id, self.context.functions, self.context.hir, work)?;
                        let scalar = self.key_carrier(*base, work, 0)?;
                        return self.builder.insert(SourceNode::Scalar(scalar), work);
                    }
                    work.charge(
                        self.generic_parameters.len().checked_ilog2().unwrap_or(0) as usize + 1,
                    )?;
                    if !self.generic_parameters.contains_key(&id) {
                        let identity = generic_parameter(
                            id,
                            self.context.functions,
                            self.context.generic_binders,
                            self.context.binders,
                            self.context.hir,
                            work,
                        )?;
                        self.generic_parameters.insert(id, identity);
                    }
                    let identity = self
                        .generic_parameters
                        .get(&id)
                        .ok_or(SourceTypesError::MissingNode)?;
                    work.text(identity)?;
                    return self
                        .builder
                        .insert(SourceNode::Binder(identity.clone()), work);
                }
                if caller
                    && arguments.is_empty()
                    && !matches!(binding, Some(TypeNameBinding::Declaration(_)))
                    && let Some(identity) = self.context.binders.get(&name)
                {
                    work.text(identity)?;
                    return self
                        .builder
                        .insert(SourceNode::Binder(identity.clone()), work);
                }
                if arguments.is_empty() && !matches!(binding, Some(TypeNameBinding::Declaration(_)))
                {
                    if let Some(scalar) = super::super::legacy::scalar(&name) {
                        return self.builder.insert(SourceNode::Scalar(scalar), work);
                    }
                    if let Some(schema) = super::super::standard_data::schema(&name) {
                        return schema.insert(&mut self.builder, work);
                    }
                }
                let declaration = match binding {
                    Some(TypeNameBinding::Declaration(id)) => {
                        Some((id, self.original_declaration(id, &name, work)?))
                    }
                    _ => None,
                };
                let needs_declaration = declaration
                    .as_ref()
                    .map(|(_, declaration)| declaration)
                    .or_else(|| self.context.declarations.get(&name))
                    .is_some_and(|declaration| {
                        (!declaration.nominal
                            && !declaration.opaque
                            && declaration.variants.is_empty())
                            || declaration
                                .generics
                                .iter()
                                .any(static_eval::const_nominal::static_parameter)
                    });
                let declaration = if needs_declaration {
                    match declaration {
                        Some(declaration) => Some(declaration),
                        None => self.declaration(&name, work)?,
                    }
                } else {
                    None
                };
                if let Some((declaration_id, declaration)) = declaration {
                    if !declaration.nominal
                        && !declaration.opaque
                        && declaration.variants.is_empty()
                    {
                        if !declaration.generics.is_empty() || !arguments.is_empty() {
                            return Err(SourceTypesError::NeedsStaticElaboration);
                        }
                        if let Some(&root) = self.aliases.get(&declaration_id) {
                            return Ok(root);
                        }
                        let value = declaration
                            .value
                            .as_ref()
                            .ok_or(SourceTypesError::Unresolved)?;
                        self.validate_syntax(value, work)?;
                        let root = self.builder.reserve(work)?;
                        self.aliases.insert(declaration_id, root);
                        let target = self.ty(value, false, true, work, depth + 1)?;
                        self.builder.define(
                            root,
                            SourceNode::Alias {
                                declaration: name,
                                target,
                            },
                            work,
                        )?;
                        return Ok(root);
                    }
                    if declaration.nominal && !declaration.generics.is_empty() {
                        let mut remaining = work.remaining();
                        let normalized = static_eval::const_nominal::closed_const_nominal_arguments(
                            &declaration,
                            arguments,
                            self.context.declarations,
                            self.context.layout,
                            &mut remaining,
                        );
                        work.charge(work.remaining() - remaining)?;
                        if let Some(arguments) =
                            normalized.map_err(|_| SourceTypesError::Unresolved)?
                        {
                            let schema = SourceSchema::certified_const_nominal(
                                &name,
                                &arguments,
                                syntax.hir_id,
                                work,
                            )?;
                            return schema.copy_into(&mut self.builder, work);
                        }
                        if declaration
                            .generics
                            .iter()
                            .any(static_eval::const_nominal::static_parameter)
                        {
                            return Err(SourceTypesError::NeedsStaticElaboration);
                        }
                    }
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| self.ty(argument, caller, original, work, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(root) = super::super::standard_views::instantiate(
                    &name,
                    &arguments,
                    &mut self.builder,
                    work,
                )? {
                    return Ok(root);
                }
                if let Some(kind) = super::super::legacy::container(&name) {
                    SourceNode::Container { kind, arguments }
                } else {
                    if !caller
                        && !matches!(binding, Some(TypeNameBinding::Declaration(_)))
                        && !self.context.declarations.contains_key(&name)
                        && !crate::sema::checker::is_known_builtin_source_type(&name)
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    SourceNode::OpaqueName { name, arguments }
                }
            }
            TypeKind::Optional(inner) => SourceNode::Container {
                kind: SourceContainer::Option,
                arguments: vec![self.ty(inner, caller, original, work, depth + 1)?],
            },
            TypeKind::Array { length, element } => SourceNode::Array {
                length: match length {
                    None => SourceLength::Dynamic,
                    Some(_) => self.extent(syntax, work)?,
                },
                element: self.ty(element, caller, original, work, depth + 1)?,
            },
            TypeKind::Map { key, value } => SourceNode::Map {
                key: self.ty(key, caller, original, work, depth + 1)?,
                value: self.ty(value, caller, original, work, depth + 1)?,
            },
            TypeKind::Tuple(items) if items.is_empty() => SourceNode::Scalar(SourceScalar::Unit),
            TypeKind::Tuple(items) => {
                work.charge(items.len())?;
                SourceNode::Tuple(
                    items
                        .iter()
                        .map(|item| self.ty(item, caller, original, work, depth + 1))
                        .collect::<Result<_, _>>()?,
                )
            }
            TypeKind::Record { fields, row } => {
                work.charge(fields.len() + usize::from(row.is_some()))?;
                let fields = fields
                    .iter()
                    .map(|field| {
                        work.text(&field.name)?;
                        Ok(SourceField {
                            label: field.name.clone(),
                            mutable: field.mutable,
                            value: self.ty(&field.ty, caller, original, work, depth + 1)?,
                        })
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                SourceNode::Record {
                    fields,
                    row: row
                        .as_ref()
                        .map(|row| self.ty(row, caller, original, work, depth + 1))
                        .transpose()?,
                }
            }
            TypeKind::ComputedProjection { base, key } if original => {
                let ExprKind::Name(_) = &key.kind else {
                    return Err(SourceTypesError::NeedsStaticElaboration);
                };
                let mut remaining = work.remaining();
                let parameter = self.context.lexical.lookup_generic(
                    key.hir_id.ok_or(SourceTypesError::MissingNode)?,
                    &mut remaining,
                );
                work.charge(work.remaining() - remaining)?;
                let parameter = parameter
                    .map_err(super::lexical_error)?
                    .ok_or(SourceTypesError::Unresolved)?;
                let identity = generic_parameter(
                    parameter,
                    self.context.functions,
                    self.context.generic_binders,
                    self.context.binders,
                    self.context.hir,
                    work,
                )?;
                let binder = self
                    .context
                    .generic_binders
                    .get(&identity)
                    .ok_or(SourceTypesError::MissingNode)?;
                work.charge(self.context.functions.len())?;
                let function = self
                    .context
                    .functions
                    .iter()
                    .find(|function| function.definition == binder.definition)
                    .ok_or(SourceTypesError::MissingNode)?;
                let bound = function
                    .syntax
                    .generics
                    .get(binder.index as usize)
                    .and_then(|parameter| parameter.bound.as_ref())
                    .ok_or(SourceTypesError::MissingNode)?;
                self.validate_syntax(bound, work)?;
                let TypeKind::KeyOf(bound_base) = &bound.kind else {
                    return Err(SourceTypesError::Unresolved);
                };
                let base = self.ty(base, caller, true, work, depth + 1)?;
                let original_base = self.ty(bound_base, caller, true, work, depth + 1)?;
                if !super::super::reception::equivalent(
                    &self.builder,
                    base,
                    &self.builder,
                    original_base,
                    work,
                )? {
                    return Err(SourceTypesError::Unresolved);
                }
                SourceNode::KeyProjection {
                    origin: super::super::KeyProjectionOrigin::Type(
                        syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
                    ),
                    parameter,
                    identity,
                    base,
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                work.charge(parameters.len() + annotations.len() + 1)?;
                let row_identity = if original {
                    self.callable_row(
                        CallableRowOrigin::Type(
                            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
                        ),
                        annotations,
                        work,
                    )?
                } else {
                    None
                };
                let parameters = parameters
                    .iter()
                    .map(|parameter| {
                        if parameter.default.is_some() {
                            return Err(SourceTypesError::Unresolved);
                        }
                        Ok((
                            parameter.mode,
                            self.ty(
                                parameter.ty.as_ref().ok_or(SourceTypesError::Unresolved)?,
                                caller,
                                original,
                                work,
                                depth + 1,
                            )?,
                        ))
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                let result = match result {
                    Some(result) => self.ty(result, caller, original, work, depth + 1)?,
                    None => self
                        .builder
                        .insert(SourceNode::Scalar(SourceScalar::Unit), work)?,
                };
                let annotations = annotations
                    .iter()
                    .map(|annotation| {
                        work.text(&annotation.text)?;
                        Ok(annotation.text.clone())
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                SourceNode::Callable {
                    parameters,
                    result,
                    annotations,
                    row_identity,
                }
            }
            _ => return Err(SourceTypesError::NeedsStaticElaboration),
        };
        self.builder.insert(node, work)
    }

    fn extent(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<SourceLength, SourceTypesError> {
        use num_traits::ToPrimitive;
        work.charge(4)?;
        charge_syntax(syntax, work)?;
        let TypeKind::Array {
            length: Some(length),
            ..
        } = &syntax.kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let shell = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: syntax.span,
            kind: TypeKind::Array {
                length: Some(length.clone()),
                element: Box::new(TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Tuple(vec![]),
                }),
            },
        };
        let normalized = self.elaborate(&shell, work)?;
        let TypeKind::Array {
            length: Some(length),
            ..
        } = normalized.kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let ExprKind::Literal(Literal::Integer(text)) = &length.kind else {
            return Err(SourceTypesError::Unresolved);
        };
        work.text(text)?;
        let value = crate::numeric_literals::ExactLiteral::integer(
            text,
            false,
            crate::numeric_literals::ParseLimit { max_bytes: 4096 },
        )
        .map_err(|error| {
            if error == crate::numeric_literals::Error::ResourceLimit {
                SourceTypesError::BudgetExceeded
            } else {
                SourceTypesError::Unresolved
            }
        })?;
        Ok(SourceLength::Fixed(
            value
                .magnitude()
                .and_then(ToPrimitive::to_u64)
                .ok_or(SourceTypesError::Unresolved)?,
        ))
    }

    fn elaborate(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<TypeExpr, SourceTypesError> {
        work.charge(2)?;
        charge_syntax(syntax, work)?;
        let declaration = TypeDeclaration {
            visibility: Visibility::Private,
            is_halt: false,
            name: "\0source-header-elaboration".into(),
            generics: vec![],
            value: Some(syntax.clone()),
            variants: vec![],
            opaque: false,
            nominal: true,
            span: syntax.span,
        };
        let mut remaining = work.remaining();
        let normalized = static_eval::normalize_constructor_arguments_bounded(
            &declaration,
            &[],
            self.context.declarations,
            self.context.layout,
            &mut remaining,
        );
        work.charge(work.remaining() - remaining)?;
        normalized
            .map_err(|_| SourceTypesError::Unresolved)?
            .payloads
            .remove(&declaration.name)
            .flatten()
            .ok_or(SourceTypesError::Unresolved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::SourceTypeQueries;

    #[test]
    fn static_key_headers_use_the_declared_product_carrier_without_a_type_uid() {
        for tuple in [false, true] {
            let parsed = ril_syntax::parse(ril_test::case_source(
                "tests/conformance/static.ril::accept-key-membership",
            ));
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let mut program = parsed.program;
            if tuple {
                let function = program
                    .statements
                    .iter_mut()
                    .find_map(|statement| match &mut statement.kind {
                        StmtKind::Function(function) if function.name == "get_field" => {
                            Some(function)
                        }
                        _ => None,
                    })
                    .unwrap();
                let bound = function.generics[1].bound.as_mut().unwrap();
                let scalar = |name: &str| TypeExpr {
                    hir_id: None,
                    text: name.into(),
                    span: bound.span,
                    kind: TypeKind::Name {
                        path: vec![name.into()],
                        arguments: vec![],
                    },
                };
                bound.kind = TypeKind::KeyOf(Box::new(TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: bound.span,
                    kind: TypeKind::Tuple(vec![scalar("int"), scalar("str")]),
                }));
            }
            let hir =
                hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
            let lexical = LexicalBindings::new(&hir, &mut 65536).unwrap();
            let GenericModel {
                functions,
                registry,
                ..
            } = generic_model(&program);
            let function = functions
                .iter()
                .find(|function| function.syntax.name == "get_field")
                .unwrap();
            let header = function.syntax.parameters[1].ty.as_ref().unwrap();
            let declarations = BTreeMap::new();
            let binders = BTreeMap::new();
            let context = HeaderContext {
                functions: &functions,
                generic_binders: &registry,
                ..context(&program, &hir, &lexical, &declarations, &binders)
            };
            let schema = original_header(header, context, &mut WorkLimit::new(4096)).unwrap();
            assert_eq!(
                schema
                    .scalar_representation(&mut WorkLimit::new(4096))
                    .unwrap(),
                Some(if tuple {
                    SourceScalar::Int
                } else {
                    SourceScalar::Str
                })
            );
            assert!(
                schema
                    .binder_identities(&mut WorkLimit::new(4096))
                    .unwrap()
                    .is_empty()
            );
            let mut forged = functions.clone();
            forged
                .iter_mut()
                .find(|function| function.syntax.name == "get_field")
                .unwrap()
                .syntax
                .generics[1]
                .hir_id = function.syntax.generics[0].hir_id;
            assert!(
                original_header(
                    header,
                    HeaderContext {
                        functions: &forged,
                        ..context
                    },
                    &mut WorkLimit::new(4096)
                )
                .is_err()
            );
            assert!(matches!(
                original_header(header, context, &mut WorkLimit::new(0)),
                Err(SourceTypesError::BudgetExceeded)
            ));
        }
    }

    #[test]
    fn original_key_projection_schemes_keep_key_sort_coordinates_and_reach_core() {
        let mut parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/static.ril::accept-key-membership",
        ));
        assert!(parsed.is_ok());
        let hir = hir::HirProgram::lower_identified(&mut parsed.program, hir::InputOrigin::Source)
            .unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let GenericModel {
            functions,
            registry,
            available,
        } = generic_model(&parsed.program);
        let function = functions
            .iter()
            .find(|function| function.syntax.generics.len() == 2)
            .unwrap();
        let header = function.syntax.return_type.as_ref().unwrap();
        let declarations = BTreeMap::new();
        let context = HeaderContext {
            functions: &functions,
            generic_binders: &registry,
            ..context(&parsed.program, &hir, &lexical, &declarations, &available)
        };
        let mut work = WorkLimit::new(16384);
        let schema = original_header(header, context, &mut work).unwrap();
        let (types, root) = schema.graph();
        let SourceNode::KeyProjection {
            origin,
            parameter,
            identity,
            base,
        } = types.get(root).unwrap()
        else {
            panic!("the original dependent result must remain a Key projection")
        };
        assert_eq!(
            *origin,
            super::super::KeyProjectionOrigin::Type(header.hir_id.unwrap())
        );
        assert_eq!(Some(*parameter), function.syntax.generics[1].hir_id);
        assert_eq!(registry[identity].index, 1);
        let SourceNode::Binder(type_identity) = types.get(*base).unwrap() else {
            panic!("the base retains its genuine Type UID")
        };
        assert_ne!(identity, type_identity);
        assert_eq!(
            schema.binder_identities(&mut work).unwrap(),
            [type_identity.clone()].into()
        );
        assert!(schema.equivalent(&schema, &mut work).unwrap());
        assert!(schema.scalar_representation(&mut work).is_err());
        assert!(schema.key().is_err());
        let mut live = crate::sema::source_types::LiveSourceTypes::default();
        live.record_schema(
            0,
            Some(&schema),
            crate::sema::context::FrozenEnvironment::default(),
        )
        .unwrap();
        let frozen = live.freeze();
        frozen.validate(&mut WorkLimit::new(16384)).unwrap();
        for mutation in 0..3 {
            let mut builder = SourceBuilder::new().unwrap();
            let mut budget = WorkLimit::new(4096);
            let base = types.copy_into([*base], &mut builder, &mut budget).unwrap()[base];
            let changed = builder
                .insert(
                    SourceNode::KeyProjection {
                        origin: if mutation == 0 {
                            super::super::KeyProjectionOrigin::Type(TypeExprId(
                                header.hir_id.unwrap().0 + 1,
                            ))
                        } else {
                            *origin
                        },
                        parameter: if mutation == 1 {
                            GenericParamId(parameter.0 + 1)
                        } else {
                            *parameter
                        },
                        identity: if mutation == 2 {
                            type_identity.clone()
                        } else {
                            identity.clone()
                        },
                        base,
                    },
                    &mut budget,
                )
                .unwrap();
            let changed = SourceSchema::frozen_view(
                &builder.freeze(&mut budget).unwrap(),
                changed,
                header.hir_id,
                &mut budget,
            )
            .unwrap();
            assert!(
                !schema.equivalent(&changed, &mut budget).unwrap_or(false),
                "projection coordinate mutation {mutation} was accepted"
            );
        }
        assert!(original_header(header, context, &mut WorkLimit::new(0)).is_err());
    }

    #[test]
    fn an_effect_instance_builds_all_operation_views_from_one_original_declaration() {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/effects.ril::generic-instances",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let statement=program.statements.iter_mut().find(|statement|matches!(&statement.kind,StmtKind::Effect(effect) if effect.name == "State")).unwrap();
        let StmtKind::Effect(effect) = &mut statement.kind else {
            unreachable!()
        };
        let mut second = effect.operations[0].clone();
        second.name = "other".into();
        effect.operations.push(second);
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 65536).unwrap();
        let (id, declaration) = program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Effect(effect) if effect.name == "State" => {
                    Some((statement.hir_id.unwrap(), effect))
                }
                _ => None,
            })
            .unwrap();
        let declarations = BTreeMap::new();
        let binders = BTreeMap::new();
        let context = context(&program, &hir, &lexical, &declarations, &binders);
        let argument = |name: &str| TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: vec![name.into()],
                arguments: vec![],
            },
        };
        let expected = |name: &str| match effect_source(
            id,
            declaration,
            &[argument(name)],
            context,
            &mut WorkLimit::new(16384),
        ) {
            Ok(source) => source,
            Err(error) => panic!("{error}"),
        };
        let source = expected("int");
        let first = source
            .operations
            .project_steps(
                &[super::super::super::SourcePath::Tuple(0)],
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        let second = source
            .operations
            .project_steps(
                &[super::super::super::SourcePath::Tuple(1)],
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        assert_eq!(first.root_id().arena, second.root_id().arena);
        assert!(
            first
                .equivalent(&second, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let other = expected("str");
        assert!(
            !source
                .operations
                .equivalent(&other.operations, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let mut forged = declaration.clone();
        forged.operations[0].return_type.as_mut().unwrap().hir_id = None;
        assert!(
            effect_source(
                id,
                &forged,
                &[argument("int")],
                context,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
        let mut forged = declaration.clone();
        forged.generics[0].hir_id = None;
        assert!(
            effect_source(
                id,
                &forged,
                &[argument("int")],
                context,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
        assert!(
            effect_source(
                id,
                declaration,
                &[argument("int")],
                context,
                &mut WorkLimit::new(0)
            )
            .is_err()
        );
    }

    fn fixture() -> (Program, hir::HirProgram, BTreeMap<String, TypeDeclaration>) {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::nested-const-original-headers",
        );
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let declarations = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) => {
                    Some((declaration.name.clone(), declaration.clone()))
                }
                _ => None,
            })
            .collect();
        (program, hir, declarations)
    }

    fn parameter(program: &Program, name: &str) -> TypeExpr {
        program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Function(function) if function.name == name => {
                    function.parameters[0].ty.clone()
                }
                _ => None,
            })
            .unwrap()
    }

    fn context<'a>(
        program: &'a Program,
        hir: &'a hir::HirProgram,
        lexical: &'a LexicalBindings,
        declarations: &'a BTreeMap<String, TypeDeclaration>,
        binders: &'a BTreeMap<String, String>,
    ) -> HeaderContext<'a> {
        static EMPTY: std::sync::OnceLock<BTreeMap<String, crate::sema::GenericBinder>> =
            std::sync::OnceLock::new();
        HeaderContext {
            program,
            hir,
            lexical,
            declarations,
            binders,
            functions: &[],
            generic_binders: EMPTY.get_or_init(BTreeMap::new),
            layout: TargetLayout::POINTER64,
        }
    }

    struct GenericModel {
        functions: Vec<crate::sema::model::FunctionInfo>,
        registry: BTreeMap<String, crate::sema::GenericBinder>,
        available: BTreeMap<String, String>,
    }

    fn generic_model(program: &Program) -> GenericModel {
        use crate::sema::{GenericBinder, context::FrozenEnvironment, model::FunctionInfo};
        use ril_compiler_core::ids::DefinitionId;
        let mut registry = BTreeMap::new();
        let mut available = BTreeMap::new();
        let functions = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Function(function) => Some((statement, function)),
                _ => None,
            })
            .enumerate()
            .map(|(index, (statement, function))| {
                let definition = DefinitionId(index as u32);
                for (index, parameter) in function.generics.iter().enumerate() {
                    let identity = format!("model:declaration:{}:parameter:{index}", definition.0);
                    registry.insert(
                        identity.clone(),
                        GenericBinder {
                            identity: identity.clone(),
                            definition,
                            owner: function.span,
                            index: index as u32,
                            name: parameter.name.clone(),
                        },
                    );
                    available.insert(format!("\0effect-binder:{identity}"), identity);
                }
                FunctionInfo {
                    hir_id: statement.hir_id,
                    definition,
                    lexical_owner: None,
                    typing_environment: FrozenEnvironment::default(),
                    syntax: function.clone(),
                    lexical: Default::default(),
                    owner: None,
                    handler_context: vec![],
                    lexical_scope: 0,
                    environment: None,
                    captures: Default::default(),
                    writes: Default::default(),
                    environment_published: false,
                }
            })
            .collect();
        GenericModel {
            functions,
            registry,
            available,
        }
    }

    fn row_fixture() -> (Program, hir::HirProgram, GenericModel) {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/regressions/defaults.ril::local-budget",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let model = generic_model(&program);
        (program, hir, model)
    }

    fn row_context<'a>(
        program: &'a Program,
        hir: &'a hir::HirProgram,
        lexical: &'a LexicalBindings,
        model: &'a GenericModel,
        declarations: &'a BTreeMap<String, TypeDeclaration>,
    ) -> HeaderContext<'a> {
        HeaderContext {
            program,
            hir,
            lexical,
            declarations,
            binders: &model.available,
            functions: &model.functions,
            generic_binders: &model.registry,
            layout: TargetLayout::POINTER64,
        }
    }

    #[test]
    fn original_applied_rows_require_their_header_environment_and_all_type_arguments() {
        let (program, hir, model) = row_fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let declarations = BTreeMap::new();
        let function = model
            .functions
            .iter()
            .find(|function| function.syntax.name == "measured")
            .unwrap();
        let context = row_context(&program, &hir, &lexical, &model, &declarations);
        let origin = CallableRowOrigin::Declaration(function.hir_id.unwrap());
        let mut work = WorkLimit::new(65536);
        let row = callable_row_identity(origin, &function.syntax.annotations, context, &mut work)
            .unwrap()
            .unwrap();
        assert_eq!(row.parameters.len(), 1);
        assert_eq!(
            row.parameters[0].0,
            function.syntax.generics[0].hir_id.unwrap()
        );
        let int = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        let annotations: Vec<_> = function
            .syntax
            .annotations
            .iter()
            .map(|annotation| annotation.text.clone())
            .collect();
        let source =
            SourceSchema::callable_original(&[], &int, &annotations, Some(&row), None, &mut work)
                .unwrap();
        let environment = crate::sema::context::FrozenEnvironment::default();
        assert_eq!(
            source.equivalent_in(&source, &environment, &environment, &mut work),
            Ok(true)
        );
        assert!(source.equivalent(&source, &mut work).is_err());
        assert!(source.key_with_work(&mut work).is_err());
        let other_environment = environment.thaw().freeze();
        assert!(
            source
                .equivalent_in(&source, &environment, &other_environment, &mut work)
                .is_err()
        );
        for mutation in 0..6 {
            let mut changed = row.clone();
            let mut text = annotations.clone();
            match mutation {
                0 => {
                    changed.origin = CallableRowOrigin::Declaration(
                        model
                            .functions
                            .iter()
                            .find(|candidate| candidate.syntax.name == "answer")
                            .unwrap()
                            .hir_id
                            .unwrap(),
                    )
                }
                1 => changed.parameters[0].0 = GenericParamId(u32::MAX),
                2 => changed.parameters[0].1 = int.clone(),
                3 => changed.parameters.clear(),
                4 => text[0].push(' '),
                _ => {}
            }
            let candidate = SourceSchema::callable_original(
                &[],
                &int,
                &text,
                (mutation != 5).then_some(&changed),
                None,
                &mut work,
            )
            .unwrap();
            assert_ne!(
                source.equivalent_in(&candidate, &environment, &environment, &mut work),
                Ok(true),
                "mutation {mutation}"
            );
        }
        let mut changed = function.syntax.annotations.clone();
        changed[0].text.push(' ');
        assert!(callable_row_identity(origin, &changed, context, &mut work).is_err());
        assert!(
            callable_row_identity(
                CallableRowOrigin::Declaration(
                    model
                        .functions
                        .iter()
                        .find(|candidate| candidate.syntax.name == "answer")
                        .unwrap()
                        .hir_id
                        .unwrap()
                ),
                &function.syntax.annotations,
                context,
                &mut work
            )
            .is_err()
        );
        let mut missing = model.available.clone();
        missing.clear();
        assert!(
            callable_row_identity(
                origin,
                &function.syntax.annotations,
                HeaderContext {
                    binders: &missing,
                    ..context
                },
                &mut work
            )
            .is_err()
        );
    }

    #[test]
    fn original_row_dependencies_survive_substitution_and_core_retention() {
        let (program, hir, model) = row_fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let declarations = BTreeMap::new();
        let function = model
            .functions
            .iter()
            .find(|function| function.syntax.name == "measured")
            .unwrap();
        let mut work = WorkLimit::new(65536);
        let row = callable_row_identity(
            CallableRowOrigin::Declaration(function.hir_id.unwrap()),
            &function.syntax.annotations,
            row_context(&program, &hir, &lexical, &model, &declarations),
            &mut work,
        )
        .unwrap()
        .unwrap();
        let int = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        let text = function
            .syntax
            .annotations
            .iter()
            .map(|annotation| annotation.text.clone())
            .collect::<Vec<_>>();
        let source =
            SourceSchema::callable_original(&[], &int, &text, Some(&row), None, &mut work).unwrap();
        let identities = source.binder_identities(&mut work).unwrap();
        assert_eq!(identities.len(), 1);
        let selected = source
            .substitute(
                &BTreeMap::from([(identities.into_iter().next().unwrap(), int)]),
                &mut work,
            )
            .unwrap();
        assert!(selected.binder_identities(&mut work).unwrap().is_empty());
        let environment = crate::sema::context::FrozenEnvironment::default();
        let mut live = super::super::super::LiveSourceTypes::default();
        live.record_schema(0, Some(&selected), environment.clone())
            .unwrap();
        let frozen = live.freeze();
        frozen.validate(&mut WorkLimit::new(16384)).unwrap();
        let str_source = SourceSchema::scalar(SourceScalar::Str, None, &mut work).unwrap();
        let identities = source.binder_identities(&mut work).unwrap();
        let other = source
            .substitute(
                &BTreeMap::from([(identities.into_iter().next().unwrap(), str_source)]),
                &mut work,
            )
            .unwrap();
        assert_eq!(
            selected.equivalent_in(&other, &environment, &environment, &mut work),
            Ok(false)
        );
    }

    #[test]
    fn original_row_admission_and_comparison_precharge_the_shared_budget() {
        let (program, hir, model) = row_fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let declarations = BTreeMap::new();
        let function = model
            .functions
            .iter()
            .find(|function| function.syntax.name == "measured")
            .unwrap();
        let context = row_context(&program, &hir, &lexical, &model, &declarations);
        let origin = CallableRowOrigin::Declaration(function.hir_id.unwrap());
        let mut work = WorkLimit::new(65536);
        callable_row_identity(origin, &function.syntax.annotations, context, &mut work).unwrap();
        let cost = 65536 - work.remaining();
        for limit in [0, cost - 1] {
            assert!(
                callable_row_identity(
                    origin,
                    &function.syntax.annotations,
                    context,
                    &mut WorkLimit::new(limit)
                )
                .is_err()
            );
        }
        let mut exact = WorkLimit::new(cost);
        let row = callable_row_identity(origin, &function.syntax.annotations, context, &mut exact)
            .unwrap()
            .unwrap();
        assert_eq!(exact.remaining(), 0);
        let int = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        let text = function
            .syntax
            .annotations
            .iter()
            .map(|annotation| annotation.text.clone())
            .collect::<Vec<_>>();
        let schema =
            SourceSchema::callable_original(&[], &int, &text, Some(&row), None, &mut work).unwrap();
        let environment = crate::sema::context::FrozenEnvironment::default();
        assert!(
            schema
                .equivalent_in(&schema, &environment, &environment, &mut WorkLimit::new(0))
                .is_err()
        );
    }

    #[test]
    fn original_headers_keep_nested_const_coordinates_and_regular_alias_backedges() {
        let (program, hir, declarations) = fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let GenericModel {
            functions,
            registry,
            available: binders,
        } = generic_model(&program);
        let identity = registry
            .values()
            .find(|binder| binder.name == "U")
            .unwrap()
            .identity
            .clone();
        let context = HeaderContext {
            functions: &functions,
            generic_binders: &registry,
            ..context(&program, &hir, &lexical, &declarations, &binders)
        };
        let mut work = WorkLimit::new(65536);
        for name in [
            "keep_callback",
            "keep_array",
            "keep_record",
            "keep_node",
            "keep_generic",
        ] {
            let syntax = parameter(&program, name);
            let schema = original_header(&syntax, context, &mut work).unwrap();
            assert_eq!(schema.original(), syntax.hir_id);
            let (types, root) = schema.graph();
            assert!(
                types
                    .reachable([root], &mut work)
                    .unwrap()
                    .iter()
                    .any(|id| { matches!(types.get(*id).unwrap(), SourceNode::StaticValue(_)) })
            );
            if name == "keep_node" {
                assert!(schema.has_cycles(&mut work).unwrap());
                assert_eq!(
                    schema.key().unwrap_err(),
                    SourceTypesError::RecursiveLegacyKey
                );
            }
            if name == "keep_generic" {
                assert_eq!(
                    schema.binder_identities(&mut work).unwrap(),
                    std::collections::BTreeSet::from([identity.clone()])
                );
            }
        }
        let first = original_header(&parameter(&program, "token_one"), context, &mut work).unwrap();
        let other = original_header(&parameter(&program, "token_two"), context, &mut work).unwrap();
        assert!(!first.equivalent(&other, &mut work).unwrap());
    }

    #[test]
    fn generic_headers_select_available_uids_by_the_original_parameter_identity() {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::deferred-arithmetic-safe",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let GenericModel {
            functions,
            registry,
            available,
        } = generic_model(&program);
        let declarations = BTreeMap::new();
        let mut work = WorkLimit::new(65536);
        let function = functions
            .iter()
            .find(|function| function.syntax.name == "choose")
            .unwrap();
        let id = function.syntax.generics[0].hir_id.unwrap();
        let identity =
            generic_parameter(id, &functions, &registry, &available, &hir, &mut work).unwrap();
        let sibling_id = functions
            .iter()
            .find(|function| function.syntax.name == "identity")
            .unwrap()
            .syntax
            .generics[0]
            .hir_id
            .unwrap();
        let sibling_identity = generic_parameter(
            sibling_id, &functions, &registry, &available, &hir, &mut work,
        )
        .unwrap();
        let mut shadowed_names = available.clone();
        shadowed_names.insert("T".into(), sibling_identity);
        let context = HeaderContext {
            functions: &functions,
            generic_binders: &registry,
            ..context(&program, &hir, &lexical, &declarations, &shadowed_names)
        };
        for parameter in &function.syntax.parameters {
            let syntax = parameter.ty.as_ref().unwrap();
            let schema = original_header(syntax, context, &mut work).unwrap();
            assert_eq!(
                schema.bare_binder_identity(&mut work).unwrap(),
                Some(identity.clone())
            );
            let selected = SourceSchema::scalar(SourceScalar::I8, None, &mut work).unwrap();
            let selected = schema
                .substitute(&BTreeMap::from([(identity.clone(), selected)]), &mut work)
                .unwrap();
            assert_eq!(
                selected.scalar_representation(&mut work).unwrap(),
                Some(SourceScalar::I8)
            );
        }
        let mut changed = functions.clone();
        let sibling = functions
            .iter()
            .find(|function| function.syntax.name == "identity")
            .unwrap()
            .syntax
            .generics[0]
            .hir_id;
        changed
            .iter_mut()
            .find(|function| function.syntax.name == "choose")
            .unwrap()
            .syntax
            .generics[0]
            .hir_id = sibling;
        assert!(generic_parameter(id, &changed, &registry, &available, &hir, &mut work).is_err());
        let mut wrong_owner = registry.clone();
        wrong_owner.get_mut(&identity).unwrap().definition = functions
            .iter()
            .find(|function| function.syntax.name == "identity")
            .unwrap()
            .definition;
        assert!(
            generic_parameter(id, &functions, &wrong_owner, &available, &hir, &mut work).is_err()
        );
        assert!(matches!(
            generic_parameter(
                id,
                &functions,
                &registry,
                &available,
                &hir,
                &mut WorkLimit::new(0)
            ),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let empty = BTreeMap::new();
        let missing = HeaderContext {
            generic_binders: &empty,
            ..context
        };
        assert!(original_header(&parameter(&program, "choose"), missing, &mut work).is_err());
    }

    #[test]
    fn closed_headers_do_not_query_unrelated_synthetic_generic_owners() {
        let case =
            ril_test::case_by_id("tests/conformance/numeric.ril::external-const-floating-defaults");
        let source = std::str::from_utf8(
            &case
                .files
                .iter()
                .find(|file| file.name == "api.d.ril")
                .unwrap()
                .bytes,
        )
        .unwrap();
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let GenericModel {
            mut functions,
            registry,
            available,
        } = generic_model(&program);
        let required = functions[0].syntax.generics[0].hir_id.unwrap();
        // Monomorphic foreign instances carry the original selected UID but
        // are derived declarations, not another original function owner.
        for function in &mut functions {
            function.hir_id = None;
        }
        let declarations = BTreeMap::new();
        let context = HeaderContext {
            functions: &functions,
            generic_binders: &registry,
            ..context(&program, &hir, &lexical, &declarations, &available)
        };
        for function in &functions {
            for syntax in function
                .syntax
                .parameters
                .iter()
                .filter_map(|parameter| parameter.ty.as_ref())
                .chain(&function.syntax.return_type)
            {
                let mut actual_work = WorkLimit::new(16384);
                let actual = original_header(syntax, context, &mut actual_work).unwrap();
                let mut baseline_work = WorkLimit::new(16384);
                let baseline = original_header(
                    syntax,
                    HeaderContext {
                        functions: &[],
                        ..context
                    },
                    &mut baseline_work,
                )
                .unwrap();
                assert_eq!(
                    actual_work.remaining(),
                    baseline_work.remaining(),
                    "a closed header must not scan function owners"
                );
                assert!(
                    actual
                        .equivalent(&baseline, &mut WorkLimit::new(4096))
                        .unwrap()
                );
            }
        }
        assert!(
            generic_parameter(
                required,
                &functions,
                &registry,
                &available,
                &hir,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
        assert!(matches!(
            original_header(
                &parameter(&program, "fixed"),
                context,
                &mut WorkLimit::new(0)
            ),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn original_headers_select_signature_aliases_by_their_actual_declaration() {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::shadowed-alias-pattern-safe",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        // The ambient compatibility map deliberately retains the outer i64.
        // Only the original parameter occurrence can select the inner i8.
        let declarations = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) => {
                    Some((declaration.name.clone(), declaration.clone()))
                }
                _ => None,
            })
            .collect();
        let binders = BTreeMap::new();
        let syntax = parameter(&program, "matches_local");
        let mut work = WorkLimit::new(16384);
        let schema = original_header(
            &syntax,
            context(&program, &hir, &lexical, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        assert_eq!(
            schema.scalar_representation(&mut work).unwrap(),
            Some(SourceScalar::I8)
        );
        let mut changed = program.clone();
        let function = changed
            .statements
            .iter_mut()
            .find_map(|statement| match &mut statement.kind {
                StmtKind::Function(function) if function.name == "matches_local" => Some(function),
                _ => None,
            })
            .unwrap();
        function.signature_where.clear();
        assert!(
            original_header(
                &syntax,
                context(&changed, &hir, &lexical, &declarations, &binders),
                &mut WorkLimit::new(16384),
            )
            .is_err()
        );
    }

    #[test]
    fn original_headers_reject_missing_or_replaced_declaration_identity_and_work() {
        let (program, hir, declarations) = fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let binders = BTreeMap::new();
        let syntax = parameter(&program, "token_one");
        assert!(matches!(
            original_header(
                &syntax,
                context(&program, &hir, &lexical, &declarations, &binders),
                &mut WorkLimit::new(0)
            ),
            Err(SourceTypesError::BudgetExceeded)
        ));
        for mutation in 0..3 {
            let mut changed = program.clone();
            let mut changed_declarations = declarations.clone();
            match mutation {
                0 => changed_declarations.get_mut("Token").unwrap().name = "Other".into(),
                1 => changed.statements.retain(|statement| !matches!(&statement.kind, StmtKind::Type(declaration) if declaration.name == "Token")),
                _ => changed.statements.iter_mut().find(|statement| matches!(&statement.kind, StmtKind::Type(declaration) if declaration.name == "Token")).unwrap().hir_id = None,
            }
            assert!(
                original_header(
                    &syntax,
                    context(&changed, &hir, &lexical, &changed_declarations, &binders),
                    &mut WorkLimit::new(16384)
                )
                .is_err()
            );
        }
        let other = parameter(&program, "token_two");
        for mutation in 0..4 {
            let mut changed = syntax.clone();
            let TypeKind::Name { arguments, .. } = &mut changed.kind else {
                unreachable!()
            };
            let TypeKind::Name {
                arguments: other_arguments,
                ..
            } = &other.kind
            else {
                unreachable!()
            };
            let TypeKind::Computation(expression) = &mut arguments[0].kind else {
                unreachable!()
            };
            let TypeKind::Computation(other_expression) = &other_arguments[0].kind else {
                unreachable!()
            };
            match mutation {
                0 => expression.kind = ExprKind::Literal(Literal::Integer("2".into())),
                1 => expression.hir_id = other_expression.hir_id,
                2 => arguments[0].hir_id = other_arguments[0].hir_id,
                _ => changed.hir_id = None,
            }
            assert!(
                original_header(
                    &changed,
                    context(&program, &hir, &lexical, &declarations, &binders),
                    &mut WorkLimit::new(16384)
                )
                .is_err()
            );
        }
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::nested-const-header-sort-conflict",
        );
        let mut bad = ril_syntax::parse(source).program;
        let bad_hir =
            hir::HirProgram::lower_identified(&mut bad, hir::InputOrigin::Source).unwrap();
        let bad_lexical = LexicalBindings::new(&bad_hir, &mut 4_000_000).unwrap();
        let bad_declarations = bad
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) => {
                    Some((declaration.name.clone(), declaration.clone()))
                }
                _ => None,
            })
            .collect();
        assert!(
            original_header(
                &parameter(&bad, "example"),
                context(&bad, &bad_hir, &bad_lexical, &bad_declarations, &binders),
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
    }

    #[test]
    fn constructor_instances_use_declared_sorts_and_keep_owner_and_payload_graphs() {
        let (program, hir, declarations) = fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let binders = BTreeMap::new();
        let context = context(&program, &hir, &lexical, &declarations, &binders);
        let mut first = parameter(&program, "token_one");
        first.hir_id = None;
        let mut work = WorkLimit::new(65536);
        assert!(matches!(
            original_header(&first, context, &mut work),
            Err(SourceTypesError::MissingNode)
        ));
        let instance = constructor_instance(&first, context, &mut work).unwrap();
        let payload = instance.payloads["Token"].as_ref().unwrap();
        assert_eq!(instance.schema.original(), None);
        assert_eq!(
            payload.schema.original(),
            declarations["Token"].value.as_ref().unwrap().hir_id
        );
        assert!(
            payload
                .schema
                .equivalent_key(
                    &crate::sema::effect_identity::ArgumentKey::Name {
                        name: "int".into(),
                        arguments: vec![]
                    },
                    &mut work
                )
                .unwrap()
        );
        let other =
            constructor_instance(&parameter(&program, "token_two"), context, &mut work).unwrap();
        assert!(
            !instance
                .schema
                .equivalent(&other.schema, &mut work)
                .unwrap()
        );
        let mut changed = declarations.clone();
        changed.get_mut("Token").unwrap().name = "Other".into();
        assert!(
            constructor_instance(
                &first,
                super::tests::context(&program, &hir, &lexical, &changed, &binders),
                &mut work
            )
            .is_err()
        );
        assert!(matches!(
            constructor_instance(&first, context, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn original_declaration_identity_does_not_depend_on_diagnostic_spans() {
        let (program, hir, declarations) = fixture();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let binders = BTreeMap::new();
        let syntax = parameter(&program, "keep_node");
        let mut work = WorkLimit::new(65536);
        let original = original_header(
            &syntax,
            context(&program, &hir, &lexical, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        let mut moved = declarations.clone();
        for declaration in moved.values_mut() {
            declaration.span.start = declaration.span.start.saturating_add(17);
            declaration.span.end = declaration.span.end.saturating_add(17);
            if let Some(value) = &mut declaration.value {
                value.span.start = value.span.start.saturating_add(29);
                value.span.end = value.span.end.saturating_add(29);
            }
        }
        let moved = original_header(
            &syntax,
            context(&program, &hir, &lexical, &moved, &binders),
            &mut work,
        )
        .unwrap();
        assert!(original.equivalent(&moved, &mut work).unwrap());
        assert!(moved.has_cycles(&mut work).unwrap());
    }

    #[test]
    fn only_the_exact_standard_step_declaration_uses_the_catalog_instance_role() {
        let program = Program::default();
        let hir = hir::HirProgram::default();
        let lexical = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let declaration = crate::sema::model::iteration::step_declaration();
        let mut declarations = BTreeMap::from([(declaration.name.clone(), declaration.clone())]);
        let binders = BTreeMap::new();
        let scalar = |name: &str| TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: vec![name.into()],
                arguments: vec![],
            },
        };
        let syntax = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: declaration.name.split("::").map(str::to_owned).collect(),
                arguments: vec![scalar("int"), scalar("str")],
            },
        };
        let mut work = WorkLimit::new(65536);
        let instance = constructor_instance(
            &syntax,
            context(&program, &hir, &lexical, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        assert_eq!(
            instance
                .schema
                .opaque_arguments("Iter::Step", 2, &mut work)
                .unwrap()
                .unwrap()
                .len(),
            2
        );
        assert!(
            instance
                .payloads
                .values()
                .any(|payload| payload.as_ref().is_some_and(|payload| payload
                    .schema
                    .tuple_parts(&mut work)
                    .unwrap()
                    .is_some_and(|items| items.len() == 2)))
        );
        declarations.get_mut("Iter::Step").unwrap().span.start = 123;
        declarations.get_mut("Iter::Step").unwrap().span.end = 456;
        let relabeled = constructor_instance(
            &syntax,
            context(&program, &hir, &lexical, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        assert!(
            instance
                .schema
                .equivalent(&relabeled.schema, &mut work)
                .unwrap()
        );
        for mutation in 0..3 {
            let mut changed = declaration.clone();
            match mutation {
                0 => changed.generics[0].name = "Altered".into(),
                1 => changed.generics[0].bound = Some(scalar("int")),
                _ => changed.variants[1].payload = Some(scalar("int")),
            }
            declarations.insert("Iter::Step".into(), changed);
            assert!(
                constructor_instance(
                    &syntax,
                    context(&program, &hir, &lexical, &declarations, &binders),
                    &mut work
                )
                .is_err()
            );
        }
        declarations.insert("Iter::Step".into(), declaration.clone());
        let source_owned = Program {
            statements: vec![Stmt {
                hir_id: None,
                span: declaration.span,
                kind: StmtKind::Type(declaration),
            }],
        };
        assert!(
            constructor_instance(
                &syntax,
                context(&source_owned, &hir, &lexical, &declarations, &binders),
                &mut work
            )
            .is_err()
        );
    }
}
