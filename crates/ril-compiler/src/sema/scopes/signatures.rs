//! Source signatures are rederived from original declarations and selectors.
//! Runtime Ty is checked only as the erased projection, never as a Source.
use super::*;
use crate::hir::nodes::LexicalOwner;
use crate::sema::{
    effect_identity::ArgumentKey,
    model::{OperationFact, Ty},
    source_types::WorkLimit,
};
use ril_compiler_core::ids::{ExprId, StmtId};
use ril_syntax::ast::{Expr, ExprKind, TypeExpr, TypeKind};

type EffectCacheKey = (
    StmtId,
    crate::sema::context::FrozenEnvId,
    ScopeId,
    InvocationContext,
    Vec<String>,
);

pub(super) struct SignatureIndex<'a> {
    facts: &'a crate::sema::SemanticFacts,
    sources: crate::sema::record_bound_validation::SourceSites<'a>,
    declarations: BTreeMap<(LexicalOwner, String), Vec<StmtId>>,
    tokens: BTreeMap<String, String>,
    lexical: Option<std::sync::Arc<crate::hir::lexical::LexicalBindings>>,
    effects: std::cell::RefCell<
        BTreeMap<EffectCacheKey, crate::sema::source_types::declarations::EffectSource>,
    >,
}

pub(crate) struct Signature {
    pub declared: ArgumentKey,
    pub expanded: ArgumentKey,
}
#[derive(Clone, Copy)]
pub(crate) enum SignatureContext<'a> {
    Evaluation(InvocationContext),
    Declaration(&'a crate::sema::context::FrozenEnvironment),
}

fn require(condition: bool, message: &str) -> Result<(), String> {
    condition.then_some(()).ok_or_else(|| message.to_owned())
}

fn admit_syntax(syntax: &TypeExpr, work: &mut WorkLimit) -> Result<usize, String> {
    let before = work.remaining();
    let mut remaining = before;
    let admitted = crate::static_eval::charge_type_syntax_clone(syntax, &mut remaining);
    work.charge(before - remaining)
        .map_err(|error| error.to_string())?;
    admitted.ok_or_else(|| "effect argument syntax exceeds its shared work bound".to_owned())?;
    Ok(before - remaining)
}

fn argument_key(
    syntax: &TypeExpr,
    tokens: &BTreeMap<String, String>,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, String> {
    let before = work.remaining();
    let mut remaining = before;
    let key = crate::static_eval::effects::argument_key_with_work(syntax, tokens, &mut remaining);
    work.charge(before - remaining)
        .map_err(|error| error.to_string())?;
    key.ok_or_else(|| "effect key construction exceeds its shared work bound".into())
}

fn admit_key(key: &ArgumentKey, work: &mut WorkLimit) -> Result<(), String> {
    let before = work.remaining();
    let mut remaining = before;
    let admitted = crate::sema::clone_work::key(&mut remaining, key, 0);
    work.charge(before - remaining)
        .map_err(|error| error.to_string())?;
    admitted.ok_or_else(|| "effect signature key exceeds its shared work bound".into())
}

fn lookup_identity<'e>(
    environment: Option<&'e crate::sema::context::FrozenEnvironment>,
    name: &str,
    work: &mut WorkLimit,
) -> Result<Option<&'e String>, String> {
    let Some(environment) = environment else {
        return Ok(None);
    };
    work.charge(
        (1 + name.len().div_ceil(32))
            * (1 + environment
                .generic_context
                .len()
                .checked_ilog2()
                .unwrap_or(0) as usize),
    )
    .map_err(|error| error.to_string())?;
    Ok(environment.generic_context.get(name))
}

impl<'a> SignatureIndex<'a> {
    pub(super) fn new_with_work(
        facts: &'a crate::sema::SemanticFacts,
        work: &mut usize,
    ) -> Result<Self, String> {
        let lexical = facts
            .semantic_hir
            .as_deref()
            .map(|hir| {
                crate::hir::lexical::LexicalBindings::new(hir, work).map(std::sync::Arc::new)
            })
            .transpose()
            .map_err(|error| format!("effect signature lexical index: {error}"))?;
        Self::new_with_lexical(facts, lexical, work)
    }

    pub(super) fn new_with_lexical(
        facts: &'a crate::sema::SemanticFacts,
        lexical: Option<std::sync::Arc<crate::hir::lexical::LexicalBindings>>,
        work: &mut usize,
    ) -> Result<Self, String> {
        *work = work
            .checked_sub(1)
            .ok_or("effect signature index exceeds its work bound")?;
        let sources =
            crate::sema::record_bound_validation::source_sites_base_with_work(facts, work)?;
        let mut declarations = BTreeMap::<_, Vec<_>>::new();
        for (&id, effect) in &sources.effects {
            *work = work
                .checked_sub(1 + effect.name.len().div_ceil(32))
                .ok_or("effect declaration index exceeds its work bound")?;
            let owner = facts
                .semantic_hir
                .as_ref()
                .and_then(|hir| hir.statement(id))
                .ok_or("effect signature declaration lost its HIR owner")?
                .info
                .owner;
            declarations
                .entry((owner, effect.name.clone()))
                .or_default()
                .push(id);
        }
        let mut tokens = BTreeMap::new();
        for identity in facts.generic_binders.keys() {
            *work = work
                .checked_sub(1 + identity.len().div_ceil(32))
                .ok_or("effect binder index exceeds its work bound")?;
            tokens.insert(format!("\0effect-binder:{identity}"), identity.clone());
        }
        Ok(Self {
            facts,
            sources,
            declarations,
            tokens,
            lexical,
            effects: Default::default(),
        })
    }

    fn declaration(
        &self,
        name: &str,
        mut owner: LexicalOwner,
        work: &mut WorkLimit,
    ) -> Result<StmtId, String> {
        let hir = self
            .facts
            .semantic_hir
            .as_ref()
            .ok_or("effect selector has no HIR")?;
        for _ in 0..256 {
            work.charge(
                (1 + name.len().div_ceil(32))
                    * (1 + self.declarations.len().checked_ilog2().unwrap_or(0) as usize),
            )
            .map_err(|error| error.to_string())?;
            if let Some(ids) = self.declarations.get(&(owner, name.to_owned())) {
                let [id] = ids.as_slice() else {
                    return Err("effect selector has ambiguous lexical declarations".into());
                };
                return Ok(*id);
            }
            owner = match owner {
                LexicalOwner::Module => break,
                LexicalOwner::Declaration(id)
                | LexicalOwner::HandlerArm { statement: id, .. }
                | LexicalOwner::Variant {
                    declaration: id, ..
                } => {
                    hir.statement(id)
                        .ok_or("effect selector owner is absent")?
                        .info
                        .owner
                }
                LexicalOwner::Lambda(id) => {
                    hir.expression(id)
                        .ok_or("effect selector lambda is absent")?
                        .info
                        .owner
                }
                LexicalOwner::TypeFunction(id) | LexicalOwner::CallableType(id) => {
                    hir.type_expression(id)
                        .ok_or("effect selector type owner is absent")?
                        .info
                        .owner
                }
            };
        }
        Err("effect selector has no genuine lexical declaration".into())
    }

    pub(crate) fn signature(
        &self,
        operation: &OperationFact,
        selector: ExprId,
        context: SignatureContext<'_>,
        work: &mut WorkLimit,
    ) -> Result<Signature, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        let Some(source) = &operation.source else {
            work.charge(8).map_err(|error| error.to_string())?;
            let result = if operation.name == "Fiber::yield" {
                ArgumentKey::Tuple(vec![])
            } else if operation.name == "Div::exhausted" {
                ArgumentKey::Name {
                    name: "never".into(),
                    arguments: vec![],
                }
            } else {
                return Err("operation has no intrinsic signature".into());
            };
            let key = ArgumentKey::Callable {
                parameters: vec![],
                result: Box::new(result),
                annotations: vec![],
            };
            let ArgumentKey::Callable { result, .. } = &key else {
                unreachable!()
            };
            let shape = self.shape(&operation.result, result, work)?;
            let source = operation
                .signature
                .as_ref()
                .ok_or("intrinsic operation has no complete Source signature")?;
            let equivalent = source
                .equivalent_key(&key, work)
                .map_err(|error| error.to_string())?;
            require(
                operation.parameters.is_empty() && shape && equivalent,
                "intrinsic operation lost its declared Source signature",
            )?;
            admit_key(&key, work)?;
            return Ok(Signature {
                declared: key.clone(),
                expanded: key,
            });
        };
        let syntax = self
            .sources
            .expressions
            .get(&selector)
            .ok_or("effect selector lost its original AST")?;
        let creation = self
            .facts
            .scopes
            .get(&source.scope)
            .ok_or("operation declaration lost its creation scope")?;
        let context_matches = match &creation.origin {
            ScopeOrigin::Module => {
                source.scope == ScopeId(0)
                    && source.context.owner == Some(ril_compiler_core::ids::CallableOwner::Global)
                    && source.context.invocation.is_none()
                    && source.context.closure_invocation.is_none()
            }
            ScopeOrigin::Named(id) => {
                source.context.invocation == Some(*id)
                    && self
                        .facts
                        .copy_invocations
                        .get(id.0 as usize)
                        .is_some_and(|call| {
                            call.id == *id
                                && source.context.owner
                                    == Some(ril_compiler_core::ids::CallableOwner::Function(
                                        call.target,
                                    ))
                        })
            }
            ScopeOrigin::Closure(id) => {
                source.context.closure_invocation == Some(*id)
                    && self
                        .facts
                        .closure_invocations
                        .get(id.0 as usize)
                        .is_some_and(|call| call.id == *id && call.activation == Some(source.scope))
            }
            ScopeOrigin::Operation(entry) => entry.context == source.context,
            ScopeOrigin::Unresolved => {
                work.charge(self.facts.evaluations.len())
                    .map_err(|error| error.to_string())?;
                self.facts
                    .evaluations
                    .iter()
                    .any(|record| record.scope == source.scope && record.context == source.context)
            }
        };
        require(
            context_matches,
            "operation signature borrowed another declaration activation",
        )?;
        let mut remaining = work.remaining();
        let before = remaining;
        let admitted = crate::static_eval::charge_expression_syntax_clone(syntax, &mut remaining);
        work.charge(before - remaining)
            .map_err(|error| error.to_string())?;
        admitted.ok_or("effect selector syntax exceeds its shared work bound")?;
        let (family, arguments, member) = selector_parts(syntax)
            .ok_or("effect selector needs its original qualified operation")?;
        let hir = self
            .facts
            .semantic_hir
            .as_ref()
            .ok_or("effect signature has no canonical HIR")?;
        let owner = hir
            .expression(selector)
            .ok_or("effect selector source is absent")?
            .info
            .owner;
        let declaration = self.declaration(&family, owner, work)?;
        let arguments = arguments
            .iter()
            .map(|syntax| self.argument(syntax, context, work, 0))
            .collect::<Result<Vec<_>, _>>()?;
        let schema = self
            .resolve(declaration, &arguments, &member, operation, work, 0)?
            .ok_or("effect selector has no original operation")?;
        // The remaining key consumers receive projections of this independently
        // rebuilt graph. No retained graph is exported merely to import it.
        let declared = schema
            .key_with_work(work)
            .map_err(|error| error.to_string())?;
        let expanded = schema
            .key_with_work(work)
            .map_err(|error| error.to_string())?;
        let runtime_shape = if let ArgumentKey::Callable {
            parameters, result, ..
        } = &expanded
        {
            work.charge(parameters.len())
                .map_err(|error| error.to_string())?;
            let mut valid = parameters.len() == operation.parameters.len();
            if valid {
                for ((mode, key), (actual, ty)) in parameters.iter().zip(&operation.parameters) {
                    valid &= mode == actual && self.shape(ty, key, work)?;
                }
                valid &= self.shape(&operation.result, result, work)?;
            }
            valid
        } else {
            false
        };
        require(
            runtime_shape,
            "operation runtime signature disagrees with its original Source projection",
        )?;
        let signature = operation
            .signature
            .as_ref()
            .ok_or("operation has no retained complete Source signature")?;
        require(
            signature
                .equivalent(&schema, work)
                .map_err(|error| error.to_string())?,
            "operation Source signature differs from its genuine declaration",
        )?;
        require(
            !source.environment.is_poisoned(),
            "operation signature has a poisoned declaration environment",
        )?;
        Ok(Signature { declared, expanded })
    }

    fn argument(
        &self,
        syntax: &TypeExpr,
        context: SignatureContext<'_>,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<TypeExpr, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        require(
            depth < 64,
            "effect argument interpretation exceeded its work bound",
        )?;
        admit_syntax(syntax, work)?;
        let name = match &syntax.kind {
            TypeKind::Name { path, arguments } if arguments.is_empty() => Some(path.join("::")),
            TypeKind::Computation(expression) => match &expression.kind {
                ExprKind::Name(name) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        };
        if let Some(name) = name
            && let Some(selected) = self.selected(&name, context, work, depth)?
        {
            return Ok(selected);
        }
        admit_syntax(syntax, work)?;
        let mut result = syntax.clone();
        let mut child = |syntax: &TypeExpr| self.argument(syntax, context, work, depth + 1);
        match &mut result.kind {
            TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                for argument in arguments {
                    *argument = child(argument)?;
                }
            }
            TypeKind::Array { element, .. }
            | TypeKind::Optional(element)
            | TypeKind::Rest(element) => **element = child(element)?,
            TypeKind::Map { key, value } => {
                **key = child(key)?;
                **value = child(value)?;
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    field.ty = child(&field.ty)?;
                }
                if let Some(row) = row {
                    **row = child(row)?;
                }
            }
            TypeKind::Callable {
                parameters, result, ..
            } => {
                for parameter in parameters {
                    if let Some(ty) = &mut parameter.ty {
                        *ty = child(ty)?;
                    }
                }
                if let Some(result) = result {
                    **result = child(result)?;
                }
            }
            _ => {}
        }
        Ok(result)
    }

    fn selected(
        &self,
        name: &str,
        context: SignatureContext<'_>,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<Option<TypeExpr>, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        require(
            depth < 64,
            "effect argument selection exceeded its depth bound",
        )?;
        let mut environment = match context {
            SignatureContext::Declaration(environment) => Some(environment),
            _ => None,
        };
        let mut identity = lookup_identity(environment, name, work)?;
        if let SignatureContext::Evaluation(context) = context {
            if let Some(ril_compiler_core::ids::CallableOwner::Function(owner)) = context.owner {
                work.charge(self.facts.functions.len())
                    .map_err(|error| error.to_string())?;
                let function = self
                    .facts
                    .functions
                    .iter()
                    .find(|function| function.definition == owner)
                    .ok_or("effect argument caller definition is absent")?;
                environment = Some(&function.typing_environment);
                work.charge(function.syntax.generics.len() + self.facts.generic_binders.len())
                    .map_err(|error| error.to_string())?;
                for parameter in &function.syntax.generics {
                    work.text(&parameter.name)
                        .map_err(|error| error.to_string())?;
                }
                identity = function
                    .syntax
                    .generics
                    .iter()
                    .position(|parameter| parameter.name == name)
                    .and_then(|index| {
                        self.facts
                            .generic_binders
                            .values()
                            .find(|binder| {
                                binder.definition == owner && binder.index as usize == index
                            })
                            .map(|binder| &binder.identity)
                    });
                if identity.is_none() {
                    identity = lookup_identity(environment, name, work)?;
                }
            } else if let Some(id) = context.closure_invocation {
                work.charge(2).map_err(|error| error.to_string())?;
                environment = self
                    .facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .and_then(|call| self.facts.closures.get(call.closure))
                    .map(|closure| &closure.contract.typing_environment);
                identity = lookup_identity(environment, name, work)?;
            }
            if let Some(identity) = identity {
                work.text(identity).map_err(|error| error.to_string())?;
                work.charge(1).map_err(|error| error.to_string())?;
                let mut rows = context
                    .default_use
                    .and_then(|id| self.facts.default_uses.get(id.0 as usize))
                    .map(|row| (&row.arguments, &row.captured_arguments));
                if rows.is_none() {
                    work.charge(self.facts.effect_invocations.len())
                        .map_err(|error| error.to_string())?;
                    rows = self
                        .facts
                        .effect_invocations
                        .iter()
                        .find(|row| {
                            row.invocation == context.invocation
                                && Some(ril_compiler_core::ids::CallableOwner::Function(
                                    row.function,
                                )) == context.owner
                        })
                        .map(|row| (&row.arguments, &row.captured_arguments));
                }
                if let Some((arguments, captured)) = rows {
                    work.charge(arguments.len() + captured.len())
                        .map_err(|error| error.to_string())?;
                    for argument in arguments.iter().chain(captured) {
                        work.text(&argument.binder)
                            .map_err(|error| error.to_string())?;
                    }
                    if let Some(argument) = arguments
                        .iter()
                        .chain(captured)
                        .find(|argument| &argument.binder == identity)
                        && let Some(syntax) = &argument.syntax
                    {
                        let key = argument_key(syntax, &self.tokens, work)?;
                        if let Some(original) = argument.key.as_ref() {
                            admit_key(original, work)?;
                        }
                        require(
                            argument.key.as_ref() == Some(&key),
                            "effect argument syntax differs from its owned static witness",
                        )?;
                        admit_syntax(syntax, work)?;
                        return Ok(Some(syntax.clone()));
                    }
                }
            }
        }
        let Some(identity) = identity else {
            return Ok(None);
        };
        work.charge(
            (1 + identity.len().div_ceil(32))
                * (1 + self
                    .facts
                    .generic_binders
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize),
        )
        .map_err(|error| error.to_string())?;
        let binder = self
            .facts
            .generic_binders
            .get(identity)
            .ok_or("effect argument has no genuine owned binder")?;
        work.charge(self.facts.functions.len() + self.facts.record_bounds.len())
            .map_err(|error| error.to_string())?;
        for bound in &self.facts.record_bounds {
            work.text(&bound.binder)
                .map_err(|error| error.to_string())?;
        }
        let function = self
            .facts
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)
            .ok_or("effect binder has no source declaration")?;
        require(
            function
                .syntax
                .generics
                .get(binder.index as usize)
                .is_some_and(|parameter| {
                    crate::sema::record_bounds::certifies_type_sort(
                        identity,
                        binder,
                        parameter,
                        &self.facts.record_bounds,
                    )
                }),
            "effect argument has no certified Type sort",
        )?;
        if let Some(environment) = environment {
            work.charge(
                (1 + identity.len().div_ceil(32))
                    * (1 + environment
                        .generic_sources
                        .len()
                        .checked_ilog2()
                        .unwrap_or(0) as usize),
            )
            .map_err(|error| error.to_string())?;
            if let Some(source) = environment.generic_sources.get(identity) {
                if let Some(closed) = source.closed() {
                    admit_syntax(&closed.syntax, work)?;
                    return Ok(Some(closed.syntax.clone()));
                }
                let syntax = self.argument(
                    &source.syntax,
                    SignatureContext::Declaration(&source.environment),
                    work,
                    depth + 1,
                )?;
                let key = argument_key(&syntax, &self.tokens, work)?;
                require(
                    source
                        .schema
                        .equivalent_key(&key, work)
                        .map_err(|error| error.to_string())?,
                    "captured effect selection changed its complete interpretation",
                )?;
                return Ok(Some(syntax));
            }
        }
        work.text(identity)
            .and_then(|()| work.charge(4))
            .map_err(|error| error.to_string())?;
        let token = format!("\0effect-binder:{identity}");
        Ok(Some(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: binder.owner,
            kind: TypeKind::Name {
                path: vec![token],
                arguments: vec![],
            },
        }))
    }

    fn resolve(
        &self,
        declaration: StmtId,
        arguments: &[TypeExpr],
        member: &str,
        operation: &OperationFact,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<Option<crate::sema::source_types::SourceSchema>, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        require(
            depth < 64,
            "effect signature member expansion exceeded its work bound",
        )?;
        let instance = self.effect_instance_graph(declaration, arguments, operation, work)?;
        let selected = instance.declaration.as_ref();
        if !selected.members.is_empty() {
            let mut choices = Vec::new();
            let hir = self.facts.semantic_hir.as_ref().unwrap();
            work.charge(selected.members.len())
                .map_err(|error| error.to_string())?;
            for member_type in &selected.members {
                admit_syntax(member_type, work)?;
                let TypeKind::Name { path, arguments } = &member_type.kind else {
                    return Err("effect member has no original named selector".into());
                };
                let owner = hir
                    .statement(declaration)
                    .ok_or("effect member has no lexical owner")?
                    .info
                    .owner;
                let target = self.declaration(&path.join("::"), owner, work)?;
                if let Some(key) =
                    self.resolve(target, arguments, member, operation, work, depth + 1)?
                {
                    choices.push(key);
                }
            }
            if choices.is_empty() {
                return Ok(None);
            }
            require(
                choices.len() == 1,
                "effect member has no unique actual operation signature",
            )?;
            return Ok(choices.pop());
        }
        work.charge(
            (1 + member.len().div_ceil(32))
                * (1 + instance.names.len().checked_ilog2().unwrap_or(0) as usize),
        )
        .map_err(|error| error.to_string())?;
        if !instance.names.contains_key(member) {
            return Ok(None);
        }
        let source = operation
            .source
            .as_ref()
            .ok_or("user operation has no declaration source")?;
        require(
            declaration == source.effect && selected.name == operation.effect,
            "effect selector borrowed another declaration or static instance",
        )?;
        let header = selected
            .operations
            .get(source.index as usize)
            .ok_or("effect operation signature index is absent")?;
        work.text(&selected.name)
            .and_then(|()| work.text(member))
            .map_err(|error| error.to_string())?;
        require(
            header.name == member && operation.name == format!("{}::{member}", selected.name),
            "effect selector names another original operation",
        )?;
        instance
            .operations
            .project_steps(
                &[crate::sema::source_types::SourcePath::Tuple(source.index)],
                work,
            )
            .map(Some)
            .map_err(|error| error.to_string())
    }

    fn effect_instance_graph(
        &self,
        declaration: StmtId,
        arguments: &[TypeExpr],
        operation: &OperationFact,
        work: &mut WorkLimit,
    ) -> Result<crate::sema::source_types::declarations::EffectSource, String> {
        let source = operation
            .source
            .as_ref()
            .ok_or("operation type source is absent")?;
        work.charge(1 + arguments.len())
            .map_err(|error| error.to_string())?;
        let mut keys = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let mut remaining = work.remaining();
            let admitted = crate::static_eval::charge_type_syntax_clone(argument, &mut remaining);
            work.charge(work.remaining() - remaining)
                .map_err(|error| error.to_string())?;
            admitted.ok_or("effect Source argument identity exceeds its syntax budget")?;
            let key = crate::static_eval::normalized_argument_key(argument);
            work.text(&key).map_err(|error| error.to_string())?;
            keys.push(key);
        }
        let cache_key = (
            declaration,
            source.environment.id(),
            source.scope,
            source.context,
            keys,
        );
        let key_work = cache_key
            .4
            .iter()
            .try_fold(1usize, |cost, key| {
                cost.checked_add(1 + key.len().div_ceil(32))
            })
            .ok_or("effect Source cache key exceeds its work bound")?;
        work.charge(
            key_work * (1 + self.effects.borrow().len().checked_ilog2().unwrap_or(0) as usize),
        )
        .map_err(|error| error.to_string())?;
        if let Some(cached) = self.effects.borrow().get(&cache_key).cloned() {
            return Ok(cached);
        }
        // Instantiation projects certified Type UIDs to private tokens. They
        // retain their registered meaning even when the effect declaration's
        // own frozen environment is at module scope and has no generic names.
        work.charge(source.environment.generic_context.len() + self.tokens.len())
            .map_err(|error| error.to_string())?;
        let mut scope = BTreeMap::new();
        for (name, identity) in source
            .environment
            .generic_context
            .iter()
            .chain(&self.tokens)
        {
            work.text(name)
                .and_then(|()| work.text(identity))
                .map_err(|error| error.to_string())?;
            require(
                scope
                    .insert(name.clone(), identity.clone())
                    .is_none_or(|previous| previous == *identity),
                "operation type token changed its registered Type identity",
            )?;
        }
        use crate::sema::source_types::declarations::{HeaderContext, effect_source};
        let mut schema = effect_source(
            declaration,
            self.sources
                .effects
                .get(&declaration)
                .ok_or("effect Source lost its original declaration")?,
            arguments,
            HeaderContext {
                declarations: &self.facts.external_type_declarations,
                program: self
                    .facts
                    .source_program
                    .as_deref()
                    .ok_or("effect Source has no original program")?,
                hir: self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("effect Source has no original HIR")?,
                lexical: self
                    .lexical
                    .as_deref()
                    .ok_or("effect Source has no lexical index")?,
                binders: &scope,
                functions: &self.facts.functions,
                generic_binders: &self.facts.generic_binders,
                layout: self
                    .facts
                    .target_layout
                    .ok_or("effect Source has no target layout")?,
            },
            work,
        )
        .map_err(|error| error.to_string())?;
        work.charge(source.environment.generic_sources.len())
            .map_err(|error| error.to_string())?;
        let mut selected = BTreeMap::new();
        for (identity, selection) in &source.environment.generic_sources {
            work.text(identity).map_err(|error| error.to_string())?;
            require(
                !selection.environment.is_poisoned(),
                "operation Source selection has a poisoned environment",
            )?;
            selected.insert(identity.clone(), selection.schema.clone());
        }
        schema.operations = schema
            .operations
            .substitute(&selected, work)
            .map_err(|error| error.to_string())?;
        work.charge(
            key_work * (1 + self.effects.borrow().len().checked_ilog2().unwrap_or(0) as usize),
        )
        .map_err(|error| error.to_string())?;
        self.effects.borrow_mut().insert(cache_key, schema.clone());
        Ok(schema)
    }
}

fn selector_parts(expression: &Expr) -> Option<(String, &[TypeExpr], String)> {
    fn name(expression: &Expr) -> Option<String> {
        match &expression.kind {
            ExprKind::Name(name) => Some(name.clone()),
            ExprKind::Path(path) => Some(path.join("::")),
            _ => None,
        }
    }
    match &expression.kind {
        ExprKind::Field {
            base,
            field,
            safe: false,
        } => match &base.kind {
            ExprKind::Generic { base, arguments } => Some((name(base)?, arguments, field.clone())),
            _ => Some((name(base)?, &[], field.clone())),
        },
        ExprKind::Path(path) if path.len() > 1 => {
            Some((path[..path.len() - 1].join("::"), &[], path.last()?.clone()))
        }
        ExprKind::Name(path) => {
            let (family, member) = path.rsplit_once("::")?;
            Some((family.into(), &[], member.into()))
        }
        _ => None,
    }
}

impl SignatureIndex<'_> {
    fn shape(&self, ty: &Ty, key: &ArgumentKey, work: &mut WorkLimit) -> Result<bool, String> {
        let before = work.remaining();
        let mut remaining = before;
        let admitted = crate::sema::clone_work::ty(&mut remaining, ty, 0);
        work.charge(before - remaining)
            .map_err(|error| error.to_string())?;
        admitted.ok_or("effect runtime projection exceeds its shared work bound")?;
        let ty_cost = before - remaining;
        let before_key = work.remaining();
        admit_key(key, work)?;
        let key_cost = before_key - work.remaining();
        work.charge(
            key_cost
                .checked_mul(ty_cost.checked_ilog2().unwrap_or(0) as usize + 1)
                .ok_or("effect projection map lookup exceeds its work bound")?,
        )
        .map_err(|error| error.to_string())?;
        self.shape_inner(ty, key, work, 0)
    }

    fn shape_inner(
        &self,
        ty: &Ty,
        key: &ArgumentKey,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<bool, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        require(
            depth < 64,
            "effect runtime projection exceeds its depth bound",
        )?;
        // The erased type may name a transparent alias; its meaning still
        // comes from that original declaration, with the same query budget.
        if let Ty::Named(name) = ty
            && !matches!(key, ArgumentKey::Name{name:expected,arguments} if expected == name && arguments.is_empty())
        {
            work.charge(
                (1 + name.len().div_ceil(32))
                    * (1 + self
                        .facts
                        .external_type_declarations
                        .len()
                        .checked_ilog2()
                        .unwrap_or(0) as usize),
            )
            .map_err(|error| error.to_string())?;
            if let Some(declaration) = self.facts.external_type_declarations.get(name)
                && !declaration.nominal
                && !declaration.opaque
                && declaration.generics.is_empty()
                && declaration.variants.is_empty()
                && let Some(syntax) = declaration.value.as_ref()
            {
                use crate::sema::source_types::declarations::{
                    HeaderContext, elaborate_original_header, original_header,
                };
                let context = HeaderContext {
                    declarations: &self.facts.external_type_declarations,
                    program: self
                        .facts
                        .source_program
                        .as_deref()
                        .ok_or("effect alias projection has no original program")?,
                    hir: self
                        .facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("effect alias projection has no original HIR")?,
                    lexical: self
                        .lexical
                        .as_deref()
                        .ok_or("effect alias projection has no lexical index")?,
                    binders: &self.tokens,
                    functions: &self.facts.functions,
                    generic_binders: &self.facts.generic_binders,
                    layout: self
                        .facts
                        .target_layout
                        .ok_or("effect alias projection has no target layout")?,
                };
                let expected = match original_header(syntax, context, work) {
                    Err(crate::sema::source_types::SourceTypesError::NeedsStaticElaboration) => {
                        elaborate_original_header(syntax, context, work)
                    }
                    result => result,
                }
                .map_err(|error| error.to_string())?;
                return expected
                    .equivalent_key(key, work)
                    .map_err(|error| error.to_string());
            }
        }
        let mut child = |ty, key| self.shape_inner(ty, key, work, depth + 1);
        Ok(match (ty, key) {
            (Ty::Unit, ArgumentKey::Tuple(items)) => items.is_empty(),
            (Ty::Bool, ArgumentKey::Name { name, arguments }) => {
                name == "bool" && arguments.is_empty()
            }
            (Ty::Str, ArgumentKey::Name { name, arguments }) => {
                name == "str" && arguments.is_empty()
            }
            (Ty::Bytes, ArgumentKey::Name { name, arguments }) => {
                name == "bytes" && arguments.is_empty()
            }
            (Ty::Never, ArgumentKey::Name { name, arguments }) => {
                name == "never" && arguments.is_empty()
            }
            (
                Ty::Int(actual) | Ty::Float(actual) | Ty::Named(actual),
                ArgumentKey::Name { name, arguments },
            ) => actual == name && arguments.is_empty(),
            (Ty::Generic(actual), ArgumentKey::Binder { identity, .. }) => actual == identity,
            (Ty::Array(ty), ArgumentKey::Array { element, .. }) => child(ty, element)?,
            (Ty::Tuple(types), ArgumentKey::Tuple(keys)) => {
                if types.len() != keys.len() {
                    return Ok(false);
                }
                for (ty, key) in types.iter().zip(keys) {
                    if !child(ty, key)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Ty::Record(types), ArgumentKey::Record { fields, row: None }) => {
                if types.len() != fields.len() {
                    return Ok(false);
                }
                // The admitted key includes names; account for map comparisons.
                for (name, mode, key) in fields {
                    let Some((actual, ty)) = types.get(name) else {
                        return Ok(false);
                    };
                    if actual != mode || !child(ty, key)? {
                        return Ok(false);
                    }
                }
                true
            }
            (
                Ty::Callable(types, result),
                ArgumentKey::Callable {
                    parameters,
                    result: expected,
                    ..
                },
            ) => {
                if types.len() != parameters.len() {
                    return Ok(false);
                }
                for (ty, (_, key)) in types.iter().zip(parameters) {
                    if !child(ty, key)? {
                        return Ok(false);
                    }
                }
                child(result, expected)?
            }
            (Ty::Map(a, b), ArgumentKey::Map { key, value }) => child(a, key)? && child(b, value)?,
            (Ty::Immutable(ty), ArgumentKey::Name { name, arguments }) if name == "Immut" => {
                if let [key] = arguments.as_slice() {
                    child(ty, key)?
                } else {
                    false
                }
            }
            (Ty::Optional(ty), ArgumentKey::Name { name, arguments }) if name == "Option" => {
                if let [key] = arguments.as_slice() {
                    child(ty, key)?
                } else {
                    false
                }
            }
            (Ty::Set(ty), ArgumentKey::Name { name, arguments }) if name == "Set" => {
                if let [key] = arguments.as_slice() {
                    child(ty, key)?
                } else {
                    false
                }
            }
            (Ty::Range(ty), ArgumentKey::Name { name, arguments }) if name == "Range" => {
                if let [key] = arguments.as_slice() {
                    child(ty, key)?
                } else {
                    false
                }
            }
            (Ty::Result(a, b), ArgumentKey::Name { name, arguments }) if name == "Result" => {
                if let [x, y] = arguments.as_slice() {
                    child(a, x)? && child(b, y)?
                } else {
                    false
                }
            }
            _ => false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn name(value: String) -> TypeExpr {
        TypeExpr {
            hir_id: None,
            text: String::new(),
            span: ril_compiler_core::source::Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            },
            kind: TypeKind::Name {
                path: vec![value],
                arguments: vec![],
            },
        }
    }

    #[test]
    fn argument_syntax_copies_and_recursive_arguments_borrow_the_exact_work_allowance() {
        let facts = crate::sema::SemanticFacts::default();
        let index = SignatureIndex::new_with_work(&facts, &mut 4_000_000).unwrap();
        let environment = crate::sema::context::FrozenEnvironment::default();
        let large = name("x".repeat(1024 * 1024));
        let mut nested = name("int".into());
        for _ in 0..6 {
            nested = TypeExpr {
                hir_id: None,
                text: String::new(),
                span: nested.span,
                kind: TypeKind::Tuple(vec![nested]),
            };
        }
        for syntax in [&large, &nested] {
            for units in [0, 1] {
                let mut work = WorkLimit::new(units);
                assert!(
                    index
                        .argument(
                            syntax,
                            SignatureContext::Declaration(&environment),
                            &mut work,
                            0
                        )
                        .is_err()
                );
                assert!(work.remaining() <= units);
            }
            let initial = 16_000_000;
            let mut work = WorkLimit::new(initial);
            let result = index
                .argument(
                    syntax,
                    SignatureContext::Declaration(&environment),
                    &mut work,
                    0,
                )
                .unwrap();
            assert_eq!(&result, syntax);
            let used = initial - work.remaining();
            let mut exact = WorkLimit::new(used);
            assert_eq!(
                index
                    .argument(
                        syntax,
                        SignatureContext::Declaration(&environment),
                        &mut exact,
                        0
                    )
                    .unwrap(),
                *syntax
            );
            assert_eq!(exact.remaining(), 0);
            assert!(
                index
                    .argument(
                        syntax,
                        SignatureContext::Declaration(&environment),
                        &mut WorkLimit::new(used - 1),
                        0
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn selected_source_recursion_keeps_the_same_remaining_work() {
        use crate::sema::{
            context::TypingEnvironment,
            source_types::{SourceSchema, SourceSelectionInput, TypeSourceSelection},
        };
        use ril_compiler_core::ids::{DefinitionId, TypeExprId};
        let syntax = name("T".into());
        let mut selected = name("int".into());
        selected.hir_id = Some(TypeExprId(1));
        let selection = TypeSourceSelection::from_parameter(
            SourceSchema::import(
                &ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![],
                },
                selected.hir_id,
                &mut WorkLimit::new(4096),
            )
            .unwrap(),
            selected.clone(),
            crate::sema::context::FrozenEnvironment::default(),
            SourceSelectionInput {
                invocation: crate::sema::copy_templates::InstanceId(0),
                event: crate::sema::copy_contract::CopyCallEventId(0),
                slot: 0,
                observation: 0,
                binding: 0,
            },
        )
        .unwrap();
        let mut environment = TypingEnvironment::default();
        environment
            .generic_context
            .insert("T".into(), "genuine-type".into());
        environment
            .generic_sources
            .insert("genuine-type".into(), selection);
        let environment = environment.freeze();
        let mut facts = crate::sema::SemanticFacts::default();
        facts.generic_binders.insert(
            "genuine-type".into(),
            crate::sema::GenericBinder {
                identity: "genuine-type".into(),
                definition: DefinitionId(0),
                owner: syntax.span,
                index: 0,
                name: "T".into(),
            },
        );
        facts.functions.push(crate::sema::model::FunctionInfo {
            hir_id: None,
            definition: DefinitionId(0),
            lexical_owner: None,
            typing_environment: environment.clone(),
            syntax: ril_syntax::ast::Function {
                visibility: Default::default(),
                is_meta: false,
                is_halt: false,
                name: "model".into(),
                generics: vec![ril_syntax::ast::GenericParameter {
                    name: "T".into(),
                    bound: None,
                    default: None,
                    span: syntax.span,
                    hir_id: None,
                }],
                parameters: vec![],
                return_type: None,
                annotations: vec![],
                signature_where: vec![],
                body: None,
                span: syntax.span,
            },
            lexical: BTreeMap::new(),
            owner: None,
            handler_context: vec![],
            lexical_scope: 0,
            environment: None,
            captures: Default::default(),
            writes: Default::default(),
            environment_published: false,
        });
        let index = SignatureIndex::new_with_work(&facts, &mut 4_000_000).unwrap();
        let context = SignatureContext::Declaration(&environment);
        let initial = 65536;
        let mut work = WorkLimit::new(initial);
        assert_eq!(
            index.argument(&syntax, context, &mut work, 0).unwrap(),
            selected
        );
        let used = initial - work.remaining();
        assert!(used > 1);
        let mut exact = WorkLimit::new(used);
        assert_eq!(
            index.argument(&syntax, context, &mut exact, 0).unwrap(),
            selected
        );
        assert_eq!(exact.remaining(), 0);
        for units in [0, 1, used - 1] {
            assert!(
                index
                    .argument(&syntax, context, &mut WorkLimit::new(units), 0)
                    .is_err()
            );
        }
    }

    #[test]
    fn key_projection_prepays_the_selected_uid_output_without_a_fresh_budget() {
        let syntax = name("T".into());
        let identity = "u".repeat(1024 * 1024);
        let tokens = BTreeMap::from([("T".into(), identity.clone())]);
        let mut small = WorkLimit::new(1);
        assert!(argument_key(&syntax, &tokens, &mut small).is_err());
        let initial = 4_000_000;
        let mut work = WorkLimit::new(initial);
        let expected = ArgumentKey::Binder {
            identity,
            sort: crate::sema::effect_identity::StaticBinderSort::Type,
        };
        assert_eq!(argument_key(&syntax, &tokens, &mut work).unwrap(), expected);
        let used = initial - work.remaining();
        assert!(used >= 1024 * 1024);
        let mut exact = WorkLimit::new(used);
        assert_eq!(
            argument_key(&syntax, &tokens, &mut exact).unwrap(),
            expected
        );
        assert_eq!(exact.remaining(), 0);
        assert!(argument_key(&syntax, &tokens, &mut WorkLimit::new(used - 1)).is_err());
    }

    #[test]
    fn intrinsic_signatures_debit_the_callers_budget_on_every_query() {
        let facts = crate::sema::SemanticFacts::default();
        let index = SignatureIndex::new_with_work(&facts, &mut 4_000_000).unwrap();
        let key = ArgumentKey::Callable {
            parameters: vec![],
            result: Box::new(ArgumentKey::Tuple(vec![])),
            annotations: vec![],
        };
        let operation = OperationFact {
            source: None,
            signature: Some(
                crate::sema::source_types::SourceSchema::import(
                    &key,
                    None,
                    &mut WorkLimit::new(4096),
                )
                .unwrap(),
            ),
            identity: 1,
            name: "Fiber::yield".into(),
            effect: "Fiber".into(),
            span: ril_compiler_core::source::Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            },
            parameters: vec![],
            result: Ty::Unit,
        };
        let environment = crate::sema::context::FrozenEnvironment::default();
        let context = SignatureContext::Declaration(&environment);
        for units in [0, 1] {
            assert!(
                index
                    .signature(&operation, ExprId(0), context, &mut WorkLimit::new(units))
                    .is_err()
            );
        }
        let initial = 4096;
        let mut work = WorkLimit::new(initial);
        let signature = index
            .signature(&operation, ExprId(0), context, &mut work)
            .unwrap();
        assert_eq!(signature.declared, key);
        assert_eq!(signature.expanded, key);
        let used = initial - work.remaining();
        let mut exact = WorkLimit::new(used);
        assert!(
            index
                .signature(&operation, ExprId(0), context, &mut exact)
                .is_ok()
        );
        assert_eq!(exact.remaining(), 0);
        assert!(
            index
                .signature(&operation, ExprId(0), context, &mut exact)
                .is_err(),
            "another query cannot mint a fresh allowance"
        );
        assert!(
            index
                .signature(
                    &operation,
                    ExprId(0),
                    context,
                    &mut WorkLimit::new(used - 1)
                )
                .is_err()
        );
    }

    #[test]
    fn source_signatures_and_core_keep_hidden_extents_independently_of_runtime_shape() {
        let source = ril_test::case_source(
            "tests/regressions/effect-source-views.ril::fixed-operation-view",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let operation = facts
            .operations
            .values()
            .find(|operation| operation.name.ends_with("::apply") && operation.source.is_some())
            .unwrap();
        let core = crate::lower::lower_core(&program).unwrap();
        assert!(core.provenance.operations.iter().filter(|item| item.identity == operation.identity).any(|operation|
            matches!(operation.signature.as_ref(),Some(ril_ir::provenance::RecordBoundKey::Callable {parameters,result,..})
                if matches!(&parameters[0].1,ril_ir::provenance::RecordBoundKey::Array {length:Some(length),..} if length=="const(int:2)")
                    && matches!(&**result,ril_ir::provenance::RecordBoundKey::Array {length:Some(length),..} if length=="const(int:2)"))));
        for mutation in 0..3 {
            let mut changed = facts.clone();
            let selected = changed.operations.get_mut(&operation.name).unwrap();
            if mutation == 0 {
                selected.signature = None;
            } else if mutation == 1 {
                selected.parameters[0].1 = Ty::Array(Box::new(Ty::Bool));
            } else {
                let mut key = selected.signature.as_ref().unwrap().key().unwrap();
                let ArgumentKey::Callable { parameters, .. } = &mut key else {
                    unreachable!()
                };
                let ArgumentKey::Array { length, .. } = &mut parameters[0].1 else {
                    unreachable!()
                };
                *length = Some("const(int:3)".into());
                selected.signature = Some(
                    crate::sema::source_types::SourceSchema::import(
                        &key,
                        None,
                        &mut WorkLimit::new(4096),
                    )
                    .unwrap(),
                );
            }
            assert!(
                crate::sema::validate::solved_facts(&changed).is_err(),
                "mutation {mutation} forged a source signature"
            );
        }
    }
}
