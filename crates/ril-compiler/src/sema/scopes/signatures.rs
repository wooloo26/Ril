//! Source signatures are rederived from original declarations and selectors.
//! Runtime Ty is checked only as the erased projection, never as a Source.
use super::*;
use crate::hir::nodes::LexicalOwner;
use crate::sema::{
    effect_identity::ArgumentKey,
    model::{OperationFact, Ty},
    source_types::{SourceTypesError, WorkLimit},
};
use ril_compiler_core::ids::{ExprId, StmtId};
use ril_syntax::ast::{EffectDeclaration, Expr, ExprKind, TypeExpr, TypeKind};

pub(super) struct SignatureIndex<'a> {
    facts: &'a crate::sema::SemanticFacts,
    sources: crate::sema::record_bound_validation::SourceSites<'a>,
    declarations: BTreeMap<(LexicalOwner, String), Vec<StmtId>>,
    tokens: BTreeMap<String, String>,
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

impl<'a> SignatureIndex<'a> {
    pub(super) fn new(facts: &'a crate::sema::SemanticFacts) -> Result<Self, String> {
        let sources = crate::sema::record_bound_validation::source_sites_base(facts)?;
        let mut declarations = BTreeMap::<_, Vec<_>>::new();
        let mut work = WorkLimit::new(4_000_000);
        for (&id, effect) in &sources.effects {
            work.charge(1 + effect.name.len().div_ceil(32))
                .map_err(|error| error.to_string())?;
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
            work.charge(1 + identity.len().div_ceil(32))
                .map_err(|error| error.to_string())?;
            tokens.insert(format!("\0effect-binder:{identity}"), identity.clone());
        }
        Ok(Self {
            facts,
            sources,
            declarations,
            tokens,
        })
    }

    fn declaration(&self, name: &str, mut owner: LexicalOwner) -> Result<StmtId, String> {
        let hir = self
            .facts
            .semantic_hir
            .as_ref()
            .ok_or("effect selector has no HIR")?;
        for _ in 0..256 {
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
    ) -> Result<Signature, String> {
        let Some(source) = &operation.source else {
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
            require(
                operation.parameters.is_empty()
                    && matches!(&key, ArgumentKey::Callable{result,..} if shape(self.facts,&operation.result,result,0))
                    && operation.signature.as_ref().is_some_and(|source| {
                        source.equivalent_key(&key, &mut WorkLimit::new(4096)) == Ok(true)
                    }),
                "intrinsic operation lost its declared Source signature",
            )?;
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
            ScopeOrigin::Unresolved => self
                .facts
                .evaluations
                .iter()
                .any(|record| record.scope == source.scope && record.context == source.context),
        };
        require(
            context_matches,
            "operation signature borrowed another declaration activation",
        )?;
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
        let declaration = self.declaration(&family, owner)?;
        let mut work = WorkLimit::new(4_000_000);
        let arguments = arguments
            .iter()
            .map(|syntax| self.argument(syntax, context, &mut work, 0))
            .collect::<Result<Vec<_>, _>>()?;
        let declared = self
            .resolve(declaration, &arguments, &member, operation, &mut work, 0)?
            .ok_or("effect selector has no original operation")?;
        let expanded =
            crate::sema::source_types::declarations::expanded_key(&declared, hir, &mut work)
                .map_err(|error| error.to_string())?;
        require(
            matches!(&declared, ArgumentKey::Callable {parameters,result,..}
            if parameters.len() == operation.parameters.len()
                && parameters.iter().zip(&operation.parameters).all(|((mode,key),(actual,ty))| mode == actual && shape(self.facts,ty,key,0))
                && shape(self.facts,&operation.result,result,0)),
            "operation runtime signature disagrees with its original Source projection",
        )?;
        let signature = operation
            .signature
            .as_ref()
            .ok_or("operation has no retained complete Source signature")?;
        require(
            signature.equivalent_key(&expanded, &mut work) == Ok(true),
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
        crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
            .ok_or("effect argument syntax exceeded its work bound")?;
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
            crate::static_eval::effects::bounded_argument_key(&selected, &BTreeMap::new())
                .ok_or("selected effect argument exceeded its work bound")?;
            return Ok(selected);
        }
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
        let mut environment = match context {
            SignatureContext::Declaration(environment) => Some(environment),
            _ => None,
        };
        let mut identity = environment
            .and_then(|environment| environment.generic_context.get(name))
            .cloned();
        if let SignatureContext::Evaluation(context) = context {
            if let Some(ril_compiler_core::ids::CallableOwner::Function(owner)) = context.owner {
                let function = self
                    .facts
                    .functions
                    .iter()
                    .find(|function| function.definition == owner)
                    .ok_or("effect argument caller definition is absent")?;
                environment = Some(&function.typing_environment);
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
                            .map(|binder| binder.identity.clone())
                    })
                    .or_else(|| {
                        function
                            .typing_environment
                            .generic_context
                            .get(name)
                            .cloned()
                    });
            } else if let Some(id) = context.closure_invocation {
                environment = self
                    .facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .and_then(|call| self.facts.closures.get(call.closure))
                    .map(|closure| &closure.contract.typing_environment);
                identity = environment
                    .and_then(|environment| environment.generic_context.get(name))
                    .cloned();
            }
            if let Some(identity) = &identity {
                let rows = context
                    .default_use
                    .and_then(|id| self.facts.default_uses.get(id.0 as usize))
                    .map(|row| (&row.arguments, &row.captured_arguments))
                    .or_else(|| {
                        self.facts
                            .effect_invocations
                            .iter()
                            .find(|row| {
                                row.invocation == context.invocation
                                    && Some(ril_compiler_core::ids::CallableOwner::Function(
                                        row.function,
                                    )) == context.owner
                            })
                            .map(|row| (&row.arguments, &row.captured_arguments))
                    });
                if let Some((arguments, captured)) = rows
                    && let Some(argument) = arguments
                        .iter()
                        .chain(captured)
                        .find(|argument| &argument.binder == identity)
                    && let Some(syntax) = &argument.syntax
                {
                    let key =
                        crate::static_eval::effects::bounded_argument_key(syntax, &self.tokens)
                            .ok_or("effect argument witness exceeded its syntax budget")?;
                    require(
                        argument.key.as_ref() == Some(&key),
                        "effect argument syntax differs from its owned static witness",
                    )?;
                    return Ok(Some(syntax.clone()));
                }
            }
        }
        let Some(identity) = identity else {
            return Ok(None);
        };
        let binder = self
            .facts
            .generic_binders
            .get(&identity)
            .ok_or("effect argument has no genuine owned binder")?;
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
                        &identity,
                        binder,
                        parameter,
                        &self.facts.record_bounds,
                    )
                }),
            "effect argument has no certified Type sort",
        )?;
        if let Some(environment) = environment
            && let Some(source) = environment.generic_sources.get(&identity)
        {
            if let Some(closed) = source.closed() {
                crate::static_eval::effects::bounded_argument_key(&closed.syntax, &BTreeMap::new())
                    .ok_or("closed effect selection exceeded its syntax budget")?;
                return Ok(Some(closed.syntax.clone()));
            }
            let syntax = self.argument(
                &source.syntax,
                SignatureContext::Declaration(&source.environment),
                work,
                depth + 1,
            )?;
            let key = crate::static_eval::effects::bounded_argument_key(&syntax, &self.tokens)
                .ok_or("captured effect selection exceeded its syntax budget")?;
            require(
                source.schema.equivalent_key(&key, work) == Ok(true),
                "captured effect selection changed its complete interpretation",
            )?;
            return Ok(Some(syntax));
        }
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
    ) -> Result<Option<ArgumentKey>, String> {
        work.charge(1).map_err(|error| error.to_string())?;
        require(
            depth < 64,
            "effect signature member expansion exceeded its work bound",
        )?;
        let effect = self
            .sources
            .effects
            .get(&declaration)
            .ok_or("effect signature lost its original declaration")?;
        for header in &effect.operations {
            work.charge(1 + header.parameters.len())
                .map_err(|error| error.to_string())?;
            for syntax in header
                .parameters
                .iter()
                .filter_map(|parameter| parameter.ty.as_ref())
                .chain(header.return_type.iter())
            {
                crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
                    .ok_or("effect signature source exceeds its syntax budget")?;
            }
        }
        let normalized;
        let selected: &EffectDeclaration = if effect.generics.is_empty() {
            require(
                arguments.is_empty(),
                "non-generic effect selector has static arguments",
            )?;
            effect
        } else {
            normalized = crate::static_eval::effects::instantiate(
                effect,
                arguments,
                &self.facts.external_type_declarations,
                self.facts
                    .target_layout
                    .ok_or("effect signature has no target layout")?,
            )
            .map_err(|error| match error {
                crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message) => {
                    format!("invalid effect selector {code}: {message}")
                }
                crate::static_eval::ArgumentNormalizationError::Unsupported(message) => message,
            })?;
            &normalized.declaration
        };
        if !selected.members.is_empty() {
            let mut choices = Vec::new();
            let hir = self.facts.semantic_hir.as_ref().unwrap();
            for member_type in &selected.members {
                let TypeKind::Name { path, arguments } = &member_type.kind else {
                    return Err("effect member has no original named selector".into());
                };
                let owner = hir
                    .statement(declaration)
                    .ok_or("effect member has no lexical owner")?
                    .info
                    .owner;
                let target = self.declaration(&path.join("::"), owner)?;
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
        if !selected
            .operations
            .iter()
            .any(|header| header.name == member)
        {
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
        require(
            header.name == member && operation.name == format!("{}::{member}", selected.name),
            "effect selector names another original operation",
        )?;
        let parameters = header
            .parameters
            .iter()
            .map(|parameter| {
                Ok((
                    parameter.mode,
                    self.key(
                        parameter
                            .ty
                            .as_ref()
                            .ok_or("operation parameter has no type source")?,
                        operation,
                        work,
                    )?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let result = match &header.return_type {
            Some(syntax) => self.key(syntax, operation, work)?,
            None => ArgumentKey::Tuple(vec![]),
        };
        Ok(Some(ArgumentKey::Callable {
            parameters,
            result: Box::new(result),
            annotations: header
                .annotations
                .iter()
                .map(|row| row.text.replace(' ', ""))
                .collect(),
        }))
    }

    fn key(
        &self,
        syntax: &TypeExpr,
        operation: &OperationFact,
        work: &mut WorkLimit,
    ) -> Result<ArgumentKey, String> {
        let source = operation
            .source
            .as_ref()
            .ok_or("operation type source is absent")?;
        crate::static_eval::effects::bounded_argument_key(
            syntax,
            &source.environment.generic_context,
        )
        .ok_or("operation type source exceeds its syntax budget")?;
        let normalized = crate::sema::checker::normalize_closed_source_syntax(
            syntax,
            &self.facts.external_type_declarations,
            self.facts
                .target_layout
                .ok_or("operation type source has no target layout")?,
        );
        let syntax = normalized.as_ref().unwrap_or(syntax);
        let key = crate::static_eval::effects::bounded_argument_key(
            syntax,
            &source.environment.generic_context,
        )
        .ok_or("operation type key exceeds its syntax budget")?;
        use std::borrow::Cow;
        let key = crate::sema::source_types::substitute_key_with(
            &key,
            |identity, _| {
                if let Some(source) = source.environment.generic_sources.get(identity) {
                    return source.key().map(|key| Some(Cow::Owned(key)));
                }
                match source.environment.generic_substitutions.get(identity) {
                    Some(Ty::Generic(actual)) if actual != identity => {
                        Ok(Some(Cow::Owned(ArgumentKey::Binder {
                            identity: actual.clone(),
                            sort: crate::sema::effect_identity::StaticBinderSort::Type,
                        })))
                    }
                    Some(Ty::Generic(_)) | None => Ok(None),
                    _ => Err(SourceTypesError::Unresolved),
                }
            },
            work,
        )
        .map_err(|error| error.to_string())?;
        Ok(key)
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

fn shape(facts: &crate::sema::SemanticFacts, ty: &Ty, key: &ArgumentKey, depth: usize) -> bool {
    if depth >= 64 {
        return false;
    }
    let child = |ty, key| shape(facts, ty, key, depth + 1);
    // Alias congruence follows a genuine declaration, never a runtime shape.
    if let Ty::Named(name) = ty
        && !matches!(key, ArgumentKey::Name{name:expected,arguments} if expected == name && arguments.is_empty())
        && let Some(declaration) = facts.external_type_declarations.get(name)
        && !declaration.nominal
        && !declaration.opaque
        && declaration.generics.is_empty()
        && declaration.variants.is_empty()
        && let Some(syntax) = declaration.value.as_ref()
        && let Some(layout) = facts.target_layout
        && let Some(syntax) = crate::sema::checker::normalize_closed_source_syntax(
            syntax,
            &facts.external_type_declarations,
            layout,
        )
        && let Some(expected) =
            crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
    {
        return crate::sema::source_types::reception::equivalent_keys(
            &expected,
            key,
            &mut WorkLimit::new(16384),
        ) == Ok(true);
    }
    match (ty, key) {
        (Ty::Unit, ArgumentKey::Tuple(items)) => items.is_empty(),
        (Ty::Bool, ArgumentKey::Name { name, arguments }) => name == "bool" && arguments.is_empty(),
        (Ty::Str, ArgumentKey::Name { name, arguments }) => name == "str" && arguments.is_empty(),
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
        (Ty::Array(ty), ArgumentKey::Array { element, .. }) => child(ty, element),
        (Ty::Tuple(types), ArgumentKey::Tuple(keys)) => {
            types.len() == keys.len() && types.iter().zip(keys).all(|(ty, key)| child(ty, key))
        }
        (Ty::Record(types), ArgumentKey::Record { fields, row: None }) => {
            types.len() == fields.len()
                && fields.iter().all(|(name, mode, key)| {
                    types
                        .get(name)
                        .is_some_and(|(actual, ty)| actual == mode && child(ty, key))
                })
        }
        (
            Ty::Callable(types, result),
            ArgumentKey::Callable {
                parameters,
                result: expected,
                ..
            },
        ) => {
            types.len() == parameters.len()
                && types
                    .iter()
                    .zip(parameters)
                    .all(|(ty, (_, key))| child(ty, key))
                && child(result, expected)
        }
        (Ty::Map(a, b), ArgumentKey::Map { key, value }) => child(a, key) && child(b, value),
        (Ty::Immutable(ty), ArgumentKey::Name { name, arguments }) if name == "Immut" => {
            matches!(arguments.as_slice(),[key] if child(ty,key))
        }
        (Ty::Optional(ty), ArgumentKey::Name { name, arguments }) if name == "Option" => {
            matches!(arguments.as_slice(),[key] if child(ty,key))
        }
        (Ty::Set(ty), ArgumentKey::Name { name, arguments }) if name == "Set" => {
            matches!(arguments.as_slice(),[key] if child(ty,key))
        }
        (Ty::Range(ty), ArgumentKey::Name { name, arguments }) if name == "Range" => {
            matches!(arguments.as_slice(),[key] if child(ty,key))
        }
        (Ty::Result(a, b), ArgumentKey::Name { name, arguments }) if name == "Result" => {
            matches!(arguments.as_slice(),[x,y] if child(a,x)&&child(b,y))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
