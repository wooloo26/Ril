//! Independent complete scoped identity replay.
//! Current-value witnesses cannot substitute for original formal headers.
use super::*;
use crate::sema::scoped_source_identity::{FormalSourceAnchor, ScopedSourceIdentity};
#[path = "scoped_tokens.rs"]
mod tokens;

fn header_subterm<'a>(
    mut syntax: &'a TypeExpr,
    path: &[BoundTypeSelectionStep],
) -> Check<&'a TypeExpr> {
    require(
        path.len() < 64,
        "scoped source header path exceeds replay depth",
    )?;
    for step in path {
        syntax = match (&syntax.kind, step) {
            (TypeKind::Tuple(items), BoundTypeSelectionStep::Tuple(index)) => {
                items.get(*index as usize)
            }
            (TypeKind::Record { fields, .. }, BoundTypeSelectionStep::Field(label)) => fields
                .iter()
                .find(|field| &field.name == label)
                .map(|field| &field.ty),
            _ => None,
        }
        .ok_or_else(|| {
            "scoped source identity borrowed a nonexistent original header path".to_owned()
        })?;
    }
    Ok(syntax)
}

impl Replay<'_> {
    /// This obligation is derived from the actual selected semantic type, never
    /// from declaration-probe flags or a producer's claim that it checked T.
    /// Closed source schemas continue through their existing independent replay;
    /// this certificate supplies the missing identity of a genuine rigid row.
    fn needs_scoped_identity(&self, value: &Value) -> Check<bool> {
        fn erased(ty: &Ty, depth: usize, work: &mut usize) -> Check<bool> {
            require(
                depth < 64 && *work > 0,
                "scoped complete-identity coverage exceeds its type budget",
            )?;
            *work -= 1;
            Ok(match ty {
                Ty::Array(_) | Ty::Callable(..) => true,
                Ty::Immutable(inner) | Ty::Optional(inner) | Ty::Set(inner) | Ty::Range(inner) => {
                    erased(inner, depth + 1, work)?
                }
                Ty::Result(left, right) | Ty::Map(left, right) => {
                    erased(left, depth + 1, work)? || erased(right, depth + 1, work)?
                }
                Ty::Tuple(items) => {
                    let mut any = false;
                    for item in items {
                        any |= erased(item, depth + 1, work)?;
                    }
                    any
                }
                Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                    let mut any = false;
                    for (_, field) in fields.values() {
                        any |= erased(field, depth + 1, work)?;
                    }
                    any
                }
                Ty::Applied { arguments, .. } => {
                    let mut any = false;
                    for argument in arguments {
                        if let super::super::model::TypeArgument::Type(ty)
                        | super::super::model::TypeArgument::CanonicalType { ty, .. } = argument
                        {
                            any |= erased(ty, depth + 1, work)?;
                        }
                    }
                    any
                }
                _ => false,
            })
        }
        Ok(matches!(value.ty, Ty::OpenRecord { .. }) && erased(&value.ty, 0, &mut 4096)?)
    }

    pub(super) fn scoped_source_coverage(&self) -> Result<(), Failure> {
        if self.facts.scoped_source_identities.len() > LIMIT {
            let span = self
                .facts
                .functions
                .first()
                .map(|function| function.syntax.span)
                .unwrap_or(Span {
                    file: ril_compiler_core::source::FileId(0),
                    start: 0,
                    end: 0,
                });
            return Err((
                span,
                None,
                "scoped source identity arena exceeds replay budget".into(),
            ));
        }
        let mut registered = BTreeSet::new();
        for (index, identity) in self.facts.scoped_source_identities.iter().enumerate() {
            let mut check = || -> Check {
                require(
                    identity.id.0 as usize == index
                        && registered.insert((identity.context.invocation, identity.required)),
                    "scoped source identity IDs or invocation/binder certificates are repeated",
                )?;
                self.replay_scoped_source_identity(identity)
            };
            check().map_err(|message| (identity.span, Some(identity.cause), message))?;
        }
        for call in &self.facts.copy_invocations {
            let check = || -> Check {
                let function = self.function(call.target)?;
                // The real generic header is the authority for required binders.
                // Deleting a registry row or flipping invocation/probe metadata
                // cannot turn a required certificate into an empty iteration.
                let required: Vec<_> = function
                    .syntax
                    .generics
                    .iter()
                    .enumerate()
                    .filter(|(_, parameter)| {
                        parameter
                            .bound
                            .as_ref()
                            .is_some_and(|bound| matches!(bound.kind, TypeKind::Record { .. }))
                    })
                    .collect();
                if required.is_empty() {
                    return Ok(());
                }
                require(
                    call.entry.arguments.len() == function.syntax.parameters.len(),
                    "structural source entry table is missing arguments or has the wrong arity",
                )?;
                for (generic_index, _) in required {
                    let binder = &self.binder(call.target, generic_index as u32)?.identity;
                    let bound = self
                        .bounds
                        .get(&(call.target, generic_index as u32))
                        .ok_or_else(|| {
                            "required scoped binder has no genuine structural declaration"
                                .to_owned()
                        })?;
                    require(
                        &bound.binder == binder,
                        "required scoped binder borrowed another declaration identity",
                    )?;
                    self.every_scoped_occurrence_is_material(call.target, binder)?;
                    let paths = self.declared_type_paths(call.target, binder)?;
                    let mut needed = false;
                    // Check every path before deciding whether this invocation
                    // needs an open scoped descriptor. Missing stored children
                    // must not make coverage vacuously empty.
                    for (argument, path) in &paths {
                        let (_, entry) = call.entry.arguments.get(*argument).ok_or_else(|| {
                            "required T path has no original whole argument".to_owned()
                        })?;
                        self.snapshot(entry)?;
                        let selected = self.selected_value(entry, path)?;
                        needed |= self.needs_scoped_identity(selected)?;
                    }
                    let certificates: Vec<_> = self
                        .facts
                        .scoped_source_identities
                        .iter()
                        .filter(|identity| {
                            identity.required == bound.id
                                && identity.context.invocation == Some(call.id)
                        })
                        .collect();
                    if needed || !certificates.is_empty() {
                        self.every_scoped_occurrence_is_material(call.target, binder)?;
                        require(
                            !paths.is_empty() && certificates.len() == 1,
                            "actual complete T source has missing or duplicated scoped identity coverage",
                        )?;
                    }
                }
                Ok(())
            };
            check().map_err(|message| (call.span, None, message))?;
        }
        Ok(())
    }

    pub(super) fn every_scoped_occurrence_is_material(
        &self,
        definition: DefinitionId,
        binder: &str,
    ) -> Check {
        let scope = self.scope(definition)?;
        let mut pending: Vec<_> = self
            .function(definition)?
            .syntax
            .parameters
            .iter()
            .filter_map(|parameter| parameter.ty.as_ref())
            .map(|syntax| (syntax, 0usize))
            .collect();
        let mut work = 4096;
        while let Some((syntax, depth)) = pending.pop() {
            require(
                depth < 64 && work > 0,
                "scoped source occurrence coverage exceeds replay budget",
            )?;
            work -= 1;
            match &syntax.kind {
                TypeKind::Name { path, arguments }
                    if arguments.is_empty()
                        && scope
                            .types
                            .get(&path.join("::"))
                            .is_some_and(|identity| identity == binder) => {}
                TypeKind::Tuple(items) => {
                    pending.extend(items.iter().map(|syntax| (syntax, depth + 1)))
                }
                TypeKind::Record { fields, row } => {
                    if let Some(row) = row {
                        require(
                            !crate::static_eval::effects::type_dependencies(row)
                                .iter()
                                .any(|name| {
                                    scope
                                        .types
                                        .get(name)
                                        .is_some_and(|identity| identity == binder)
                                }),
                            "a type-only row occurrence cannot borrow a material T source",
                        )?;
                    }
                    pending.extend(fields.iter().map(|field| (&field.ty, depth + 1)));
                }
                _ => require(
                    !crate::static_eval::effects::type_dependencies(syntax)
                        .iter()
                        .any(|name| {
                            scope
                                .types
                                .get(name)
                                .is_some_and(|identity| identity == binder)
                        }),
                    "array, map or type-only T occurrence is missing an independent complete source proof",
                )?,
            }
        }
        Ok(())
    }

    pub(super) fn original_formal_view<'a>(
        &'a self,
        call: &super::super::copy_contract::CopyInvocation,
        anchor: &FormalSourceAnchor,
    ) -> Check<(&'a CopyValueSnapshot, &'a Value, &'a TypeExpr, BoundScope)> {
        let source = self
            .facts
            .copy_invocations
            .get(anchor.invocation.0 as usize)
            .filter(|source| {
                source.id == anchor.invocation
                    && source.target == anchor.definition
                    && source.status == CopyInvocationStatus::Completed
            })
            .ok_or_else(|| {
                "scoped source has no completed original formal invocation".to_owned()
            })?;
        let source_function = self.function(anchor.definition)?;
        require(
            source.entry.arguments.len() == source_function.syntax.parameters.len(),
            "scoped original formal entry table is missing arguments or has the wrong arity",
        )?;
        let mut child = call;
        let mut visited = BTreeSet::new();
        loop {
            let parent = child
                .parent
                .ok_or_else(|| "scoped formal is not an actual caller ancestor".to_owned())?;
            require(
                visited.len() < 256 && visited.insert(parent),
                "scoped formal invocation ancestry is cyclic or too deep",
            )?;
            let parent_entry = self
                .facts
                .copy_invocations
                .get(parent.0 as usize)
                .filter(|entry| entry.id == parent)
                .ok_or_else(|| "scoped caller ancestor is not registered".to_owned())?;
            self.actual_parent_source_edge(child, parent_entry)?;
            if parent == source.id {
                require(
                    child.caller == Some(anchor.definition)
                        && child.caller_owner == Some(CallableOwner::Function(anchor.definition))
                        && child.caller_activation == Some(anchor.activation),
                    "scoped formal borrowed another ancestor's received frame",
                )?;
                break;
            }
            child = parent_entry;
        }
        require(
            anchor.entry_allocation_epoch == source.entry.allocation_epoch
                && anchor.entry_allocation_epoch == call.entry.allocation_epoch,
            "scoped source across recency requires an explicit original source transport proof",
        )?;
        let parameter = self
            .function(anchor.definition)?
            .syntax
            .parameters
            .get(anchor.parameter_index as usize)
            .ok_or_else(|| {
                "scoped original parameter index is outside its declaration".to_owned()
            })?;
        let ril_syntax::ast::PatternKind::Name(name) = &parameter.pattern.kind else {
            return Err("scoped original formal is not a genuine named parameter root".into());
        };
        let (mode, entry) = source
            .entry
            .arguments
            .get(anchor.parameter_index as usize)
            .ok_or_else(|| "scoped original formal has no whole entry snapshot".to_owned())?;
        let binding = self
            .facts
            .bindings
            .get(anchor.binding)
            .ok_or_else(|| "scoped original formal binding is not registered".to_owned())?;
        let mut participants = entry.value.participants.clone();
        if participants.is_empty() {
            participants.insert(super::super::facts::Participant::Root(binding.root));
        }
        require(
            parameter.mode == ril_syntax::ast::ParameterMode::Read
                && *mode == super::super::model::Mode::Read
                && binding.parameter
                && binding.mode == ril_syntax::ast::BindingMode::Let
                && binding.owner == anchor.activation
                && &binding.name == name
                && binding.span == parameter.pattern.span
                && u32::try_from(anchor.binding).ok() == Some(binding.root.0)
                && binding.value.origins == entry.value.origins
                && binding.forwarded == entry.value.sources
                && binding.value.sources == BTreeSet::from([anchor.binding])
                && binding.value.permission == super::super::facts::Permission::Read
                && binding.value.publication == entry.value.publication
                && !binding.value.construction
                && !binding.value.marker
                && !binding.value.retention_result
                && binding.value.participants == participants,
            "scoped original source is not its real readonly parameter reception",
        )?;
        let root_observation = self.observations.row(anchor.root_expression, &mut 4096)?;
        require(
            root_observation.context.invocation == Some(source.id)
                && root_observation.context.owner
                    == Some(CallableOwner::Function(anchor.definition)),
            "scoped formal root has no actual original invocation occurrence",
        )?;
        let root = self
            .facts
            .expressions
            .get(anchor.root_expression)
            .ok_or_else(|| "scoped original root expression is outside its arena".to_owned())?;
        let source_tokens = tokens::source_expressions(&source_function.syntax)?;
        let root_tokens: Vec<_> = source_tokens
            .into_iter()
            .filter(|token| {
                token.span == root.span
                    && matches!(&token.kind, ExprKind::Name(actual) if actual == name)
            })
            .collect();
        require(
            root_tokens.len() == 1 && root.value.sources == BTreeSet::from([anchor.binding]),
            "scoped formal root has no unique genuine parameter Name token",
        )?;
        self.read_parameter_reception(
            &root.value,
            root_tokens[0],
            root_observation.context,
            anchor.activation,
            anchor.entry_allocation_epoch,
        )?;
        let contexts: Vec<_> = self
            .facts
            .invocations
            .iter()
            .filter(|summary| {
                summary.context.is_some_and(|context| {
                    context.invocation == Some(source.id)
                        && context.owner == Some(CallableOwner::Function(source.target))
                })
            })
            .collect();
        require(
            contexts.len() == 1 && contexts[0].activation == Some(anchor.activation),
            "scoped original source has no unique actual activation summary",
        )?;
        self.snapshot(entry)?;
        let selected = self.selected_value(entry, &anchor.type_path)?;
        let syntax = header_subterm(
            parameter
                .ty
                .as_ref()
                .ok_or_else(|| "scoped original parameter has no actual source type".to_owned())?,
            &anchor.type_path,
        )?;
        Ok((entry, selected, syntax, self.scope(anchor.definition)?))
    }

    pub(super) fn replay_scoped_source_identity(&self, identity: &ScopedSourceIdentity) -> Check {
        let reception = self.scoped_original_formal(identity)?;
        self.replay_scoped_member_schemas(&reception)
    }
}
