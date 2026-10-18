//! Replay immutable storage declarations and every actual assignment occurrence.
//! Source rows are duties, never a substitute for the ordinary access checker.
use super::*;
use crate::sema::source_reception::project_key as projection;
use crate::sema::{
    effect_identity::InvocationContext,
    facts::ScopeId,
    model::{BindingId, Callable, Constant, HandlerFact},
    source_reception::{self, Construction},
    storage_sources::{BindingSource, StorageDestination, StorageObservation},
};
use ril_syntax::ast::{Pattern, PatternKind};

impl Replay<'_> {
    pub(super) fn storage_binding_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        _context: InvocationContext,
        _sites: &super::explicit_named::SourceSites<'_>,
    ) -> Option<Check<ArgumentKey>> {
        let mut path = Vec::new();
        let name = expression_path(expression, &mut path, &mut 4096)?;
        if value.sources.len() != 1 {
            return None;
        }
        let id = *value.sources.first()?;
        let rows: Vec<_> = self
            .facts
            .binding_sources
            .iter()
            .filter(|row| row.binding == id)
            .collect();
        if rows.is_empty() {
            return None;
        }
        Some((|| {
            require(
                rows.len() == 1,
                "storage Name has duplicate declaration sources",
            )?;
            let binding = self
                .facts
                .bindings
                .get(id)
                .ok_or_else(|| "storage Name binding is absent".to_owned())?;
            require(
                binding.name == name,
                "storage source borrowed another named binding",
            )?;
            require(
                self.facts
                    .source_types
                    .validate_binding(id, rows[0].key.as_ref()),
                "storage source index differs from the original binding view",
            )?;
            self.facts
                .source_types
                .projected_binding_key(id, &path)
                .map_err(|error| {
                    format!("storage path has no original declared source coordinate: {error:?}")
                })
        })())
    }

    fn storage_observation(
        &self,
        observed: StorageObservation,
        syntax: &Expr,
        context: InvocationContext,
    ) -> Check<&Value> {
        let original = self
            .facts
            .expressions
            .get(observed.expression)
            .ok_or_else(|| "storage operand observation is outside its arena".to_owned())?;
        require(
            original.source_id.is_some()
                && original.source_id == syntax.hir_id
                && original.span == syntax.span
                && original.allocation_epoch == observed.allocation_epoch
                && observed.allocation_epoch <= self.facts.allocation_history.len()
                && self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| row.expression == observed.expression && row.context == context)
                    .count()
                    == 1,
            "storage operand belongs to another syntax, epoch or full invocation context",
        )?;
        Ok(&original.value)
    }

    /// Reconstruct only the guaranteed member from the genuine Type UID's
    /// source declaration. A bound never supplies a closed view of its parent
    /// or an access permission; those obligations belong to separate replay.
    fn storage_projection_source_key(
        &self,
        source: &ArgumentKey,
        slot: &Slot,
        context: InvocationContext,
    ) -> Check<Option<ArgumentKey>> {
        let (
            ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            },
            Slot::Field(label),
        ) = (source, slot)
        else {
            return Ok(projection(source, std::slice::from_ref(slot)).cloned());
        };
        self.type_binder(identity)?;
        let binder = &self.facts.generic_binders[identity];
        let declaration = self.function(binder.definition)?;
        let parameter = declaration
            .syntax
            .generics
            .get(binder.index as usize)
            .ok_or_else(|| "storage bound UID has no source parameter".to_owned())?;
        let Some(TypeExpr {
            kind: TypeKind::Record { fields, .. },
            ..
        }) = parameter.bound.as_ref()
        else {
            return Err("storage Type UID has no declared record constraint".into());
        };
        let declared: Vec<_> = fields.iter().filter(|field| field.name == *label).collect();
        let [declared] = declared.as_slice() else {
            return Err(
                "storage member is not uniquely guaranteed by its source constraint".into(),
            );
        };
        let bound = self
            .bounds
            .get(&(binder.definition, binder.index))
            .ok_or_else(|| "storage bound UID lost its registered declaration".to_owned())?;
        let scope = self.scope(binder.definition)?;
        require(
            bound.binder == *identity && bound.scope == scope,
            "storage member borrowed a different bound UID or declaration environment",
        )?;
        let recorded: Vec<_> = bound
            .fields
            .iter()
            .filter(|field| field.label == *label)
            .collect();
        let [recorded] = recorded.as_slice() else {
            return Err("storage member lost its unique recorded declaration".into());
        };
        let key = self.normalized_key(&declared.ty, &scope)?;
        require(
            recorded.mutable == declared.mutable
                && recorded.key == key
                && self.normalized_key(&recorded.syntax, &scope)? == key,
            "storage member changed the complete Source of its declared field",
        )?;
        let named = match context.owner {
            Some(CallableOwner::Function(owner)) => {
                let id = context
                    .invocation
                    .ok_or_else(|| "storage bound field has no actual named instance".to_owned())?;
                let call = self
                    .facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "storage bound field instance is absent".to_owned())?;
                require(
                    call.id == id && call.target == owner,
                    "storage bound field borrowed another named instance",
                )?;
                Some(call)
            }
            Some(CallableOwner::Lambda(site)) => {
                let invocation = context
                    .closure_invocation
                    .and_then(|id| {
                        self.facts
                            .closure_invocations
                            .get(id.0 as usize)
                            .filter(|call| call.id == id)
                    })
                    .ok_or_else(|| "storage bound field has no actual lambda entry".to_owned())?;
                let closure = self
                    .facts
                    .closures
                    .get(invocation.closure)
                    .filter(|closure| {
                        closure.site == Some(site) && context.closure == Some(invocation.closure)
                    })
                    .ok_or_else(|| {
                        "storage bound field borrowed another lambda object".to_owned()
                    })?;
                closure
                    .creation_invocation
                    .map(|id| {
                        self.facts
                            .copy_invocations
                            .get(id.0 as usize)
                            .filter(|call| call.id == id)
                            .ok_or_else(|| {
                                "storage bound field lost its captured instance".to_owned()
                            })
                    })
                    .transpose()?
            }
            _ => return Err("storage bound field has no callable declaration context".into()),
        };
        let selected = named
            .map(|call| self.input_selected_keys(call))
            .transpose()?
            .unwrap_or_default();
        let selected = super::call_input_source::input_select_key(&key, &selected, 0)?;
        require(
            source_reception::complete(&selected, &mut 4096).is_some(),
            "storage declared field has incomplete selected Source coordinates",
        )?;
        Ok(Some(selected))
    }

    fn storage_activation(&self, context: InvocationContext, activation: ScopeId) -> Check {
        require(
            self.facts.allocated_scopes.contains(&activation),
            "storage activation is not allocated",
        )?;
        if self.storage_handler(context, activation)?.is_some() {
            return Ok(());
        }
        // A named call inside a closure keeps the outer closure's dynamic
        // ancestry. Its current frame is nevertheless the named activation.
        if matches!(context.owner, Some(CallableOwner::Lambda(_))) {
            let id = context
                .closure_invocation
                .ok_or_else(|| "storage lambda has no actual closure invocation".to_owned())?;
            let call = self
                .facts
                .closure_invocations
                .get(id.0 as usize)
                .filter(|call| call.id == id)
                .ok_or_else(|| "storage closure activation is absent".to_owned())?;
            return require(
                call.activation == Some(activation)
                    && context.closure == Some(call.closure)
                    && context.invocation == call.parent_named
                    && context.budget_validation == call.budget_validation
                    && self
                        .facts
                        .closures
                        .get(call.closure)
                        .is_some_and(|closure| {
                            closure.site.map(CallableOwner::Lambda) == context.owner
                        }),
                "storage closure source borrowed another activation",
            );
        }
        if let Some(CallableOwner::Function(owner)) = context.owner {
            let call = context
                .invocation
                .and_then(|id| {
                    self.facts
                        .copy_invocations
                        .get(id.0 as usize)
                        .filter(|call| call.id == id)
                })
                .ok_or_else(|| "storage named activation has no actual invocation".to_owned())?;
            return require(
                call.target == owner
                    && call.caller_activation.is_none_or(|parent| {
                        self.facts.scope_parents.get(&activation) == Some(&parent)
                    })
                    && self.facts.invocations.iter().any(|summary| {
                        summary.activation == Some(activation) && summary.context == Some(context)
                    }),
                "storage named source borrowed another actual activation",
            );
        }
        require(
            context.owner == Some(CallableOwner::Global)
                && activation == ScopeId(0)
                && context.invocation.is_none()
                && context.closure.is_none()
                && context.closure_invocation.is_none()
                && context.default_use.is_none(),
            "storage source has no original global or callable activation",
        )
    }

    /// An operation frame is neither its surrounding named frame nor its
    /// surrounding closure frame. Only an actual operation/continuation receipt
    /// supplies its identity; lexical ancestry alone cannot choose an activation.
    fn storage_handler(
        &self,
        context: InvocationContext,
        activation: ScopeId,
    ) -> Check<Option<&HandlerFact>> {
        require(
            self.facts.operation_loan_starts.len() <= LIMIT
                && self.facts.resumption_steps.len() <= LIMIT
                && self.facts.invocations.len() <= LIMIT,
            "storage activation replay budget exhausted",
        )?;
        let mut handlers = BTreeSet::new();
        for entry in &self.facts.operation_loan_starts {
            if entry.activation == activation && entry.context == context {
                handlers.insert(entry.handler);
            }
        }
        for step in &self.facts.resumption_steps {
            if step.owner == activation && step.context == context {
                handlers.insert(step.handler);
            }
        }
        let Some(&id) = handlers.first() else {
            return Ok(None);
        };
        require(
            handlers.len() == 1,
            "storage operation frame belongs to multiple handlers",
        )?;
        let handler = self
            .facts
            .handlers
            .get(id)
            .filter(|handler| handler.id == id && handler.callable_owner == context.owner)
            .ok_or_else(|| "storage operation frame lost its actual handler owner".to_owned())?;
        require(
            self.facts
                .operation_loan_starts
                .iter()
                .filter(|entry| entry.activation == activation && entry.context == context)
                .all(|entry| {
                    entry.boundary == handler.boundary
                        && handler.operations.contains(&entry.operation)
                })
                && self
                    .facts
                    .resumption_steps
                    .iter()
                    .filter(|step| step.owner == activation && step.context == context)
                    .all(|step| {
                        step.boundary == handler.boundary
                            && handler.operations.contains(&step.operation)
                    }),
            "storage operation frame borrowed another handler operation or boundary",
        )?;
        Ok(Some(handler))
    }

    fn storage_named_environments(&self, context: InvocationContext) -> Check<Vec<&FunctionInfo>> {
        let Some(CallableOwner::Function(owner)) = context.owner else {
            return Err("storage named environment has another lexical owner".into());
        };
        let call = context
            .invocation
            .and_then(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == id && call.target == owner)
            })
            .ok_or_else(|| "storage environment lost its actual named invocation".to_owned())?;
        if let Some(id) = call.source_event {
            let event = self
                .facts
                .copy_call_events
                .get(id.0 as usize)
                .filter(|event| {
                    event.id == id
                        && event.parent == call.parent
                        && event.owner == call.caller_owner
                        && event.span == call.span
                })
                .ok_or_else(|| "storage environment lost its actual calling event".to_owned())?;
            let expression = event
                .callee_expression
                .ok_or_else(|| "storage environment lost its physical callee".to_owned())?;
            let value = self
                .facts
                .expressions
                .get(expression)
                .ok_or_else(|| "storage environment callee is absent".to_owned())?;
            let callers: Vec<_> = self
                .facts
                .invocation_calls
                .iter()
                .filter(|row| row.invocation == call.id)
                .collect();
            let [caller] = callers.as_slice() else {
                return Err("storage environment caller context is not unique".into());
            };
            require(
                caller.caller_owner == call.caller_owner
                    && self
                        .observations
                        .row(expression, &mut 4096)
                        .is_ok_and(|row| {
                            row.context.owner == caller.caller_owner
                                && row.context.invocation == call.parent
                                && row.context.closure == caller.caller_closure
                                && row.context.closure_invocation
                                    == caller.caller_closure_invocation
                                && row.context.default_use == caller.default_use
                                && row.context.budget_validation == context.budget_validation
                        }),
                "storage environment callee belongs to another caller context",
            )?;
            let mut selected = Vec::new();
            for callable in &value.value.callables {
                if let Callable::Named(index) = callable {
                    let function = self.facts.functions.get(*index).ok_or_else(|| {
                        "storage environment callee targets an absent function".to_owned()
                    })?;
                    if function.definition == owner {
                        selected.push(function);
                    }
                }
            }
            require(
                !selected.is_empty(),
                "storage environment has no actual matching named target",
            )?;
            return Ok(selected);
        }
        // A declaration probe has no call expression. An implicit invocation
        // may also lack one. Keep every possible instance: their binding IDs
        // must all agree rather than borrowing one convenient same-name copy.
        let selected: Vec<_> = self
            .facts
            .functions
            .iter()
            .filter(|function| function.definition == owner)
            .collect();
        require(
            !selected.is_empty(),
            "storage environment declaration is absent",
        )?;
        Ok(selected)
    }

    fn storage_captured_binding(
        &self,
        context: InvocationContext,
        activation: ScopeId,
        name: &str,
        id: BindingId,
        declaration: &BindingSource,
    ) -> Check<bool> {
        if let Some(handler) = self.storage_handler(context, activation)? {
            return Ok(handler.lexical.get(name) == Some(&id));
        }
        match context.owner {
            Some(CallableOwner::Lambda(site)) => {
                let call = context.closure_invocation.and_then(|id| {
                    self.facts
                        .closure_invocations
                        .get(id.0 as usize)
                        .filter(|call| call.id == id)
                });
                Ok(call.is_some_and(|call| {
                    call.activation == Some(activation)
                        && context.closure == Some(call.closure)
                        && self
                            .facts
                            .closures
                            .get(call.closure)
                            .is_some_and(|closure| {
                                closure.site == Some(site)
                                    && closure.lexical.get(name) == Some(&id)
                                    && closure.captures.contains(&id)
                            })
                }))
            }
            Some(CallableOwner::Function(_)) => {
                let global = declaration.activation == ScopeId(0)
                    && declaration.context.owner == Some(CallableOwner::Global)
                    && self
                        .facts
                        .bindings
                        .get(id)
                        .is_some_and(|binding| binding.owner == ScopeId(0));
                Ok(self
                    .storage_named_environments(context)?
                    .iter()
                    .all(|function| {
                        function.lexical.get(name) == Some(&id)
                            && (global || function.captures.contains(&id))
                    }))
            }
            _ => Ok(false),
        }
    }

    fn storage_declared_key(
        &self,
        row: &BindingSource,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<Option<ArgumentKey>> {
        let binding = self
            .facts
            .bindings
            .get(row.binding)
            .ok_or_else(|| "storage declaration binding is absent".to_owned())?;
        require(
            !binding.parameter && binding.owner == row.activation,
            "storage declaration borrowed a parameter or another frame",
        )?;
        self.storage_activation(row.context, row.activation)?;
        let declarations: Vec<_> = sites
            .bindings
            .iter()
            .filter(|site| {
                Some(site.owner) == row.context.owner
                    && site.binding.pattern.span == row.declaration
            })
            .collect();
        let [declaration] = declarations.as_slice() else {
            return Err("storage declaration is not a unique original binding AST".into());
        };
        let declaration = declaration.binding;
        require(
            row.declared == declaration.ty.is_some(),
            "storage declaration changed written/inferred origin",
        )?;
        let mut names = Vec::new();
        pattern_paths(
            &declaration.pattern,
            &mut Vec::new(),
            true,
            &mut names,
            &mut 4096,
        )?;
        let names: Vec<_> = names
            .iter()
            .filter(|(span, name, _, _)| *span == binding.span && *name == binding.name)
            .collect();
        let [(_, _, path, known)] = names.as_slice() else {
            return Err("storage binding does not belong to its original pattern".into());
        };
        require(
            row.path == *path,
            "storage binding changed its declared pattern projection",
        )?;
        let initial = self.storage_observation(row.initializer, &declaration.value, row.context)?;
        require(
            initial.ty != Ty::Never && initial.sources.iter().all(|source| *source < row.binding),
            "storage initializer is abrupt or creates a forward declaration cycle",
        )?;
        if !known {
            return Ok(None);
        }
        let key = if let Some(syntax) = &declaration.ty {
            let scope = self.lambda_input_scope(declarations[0].owner)?;
            let key = self.input_callable_source_key(syntax, &scope)?;
            super::call_input_source::input_select_key(
                &key,
                &self.binding_source_selections(binding, declarations[0].owner)?,
                0,
            )?
        } else {
            self.original_source_key(&declaration.value, initial, row.context, sites)?
        };
        Ok(projection(&key, path).cloned())
    }

    pub(super) fn storage_sources(&self) -> Result<(), Failure> {
        let fallback = self
            .facts
            .source_program
            .as_ref()
            .and_then(|program| program.statements.first())
            .map(|statement| statement.span)
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            });
        let run = || -> Check {
            let sites = super::explicit_named::source_sites(self.facts)?;
            require(
                self.facts.binding_sources.len() <= LIMIT
                    && self.facts.storage_writes.len() <= LIMIT,
                "storage source replay budget exhausted",
            )?;
            let mut declarations = BTreeMap::new();
            for row in &self.facts.binding_sources {
                require(
                    self.facts
                        .source_types
                        .validate_binding(row.binding, row.key.as_ref()),
                    "storage source index lost or changed its original binding schema",
                )?;
                require(
                    declarations.insert(row.binding, row).is_none(),
                    "storage declaration was recorded twice",
                )?;
                // An unresolved source stays conservative. A present key must
                // independently equal its actual source declaration/initializer.
                let reconstructed = self.storage_declared_key(row, &sites);
                if let Some(key) = &row.key {
                    require(
                        source_reception::complete(key, &mut 4096).is_some()
                            && reconstructed? == Some(key.clone()),
                        "storage declaration key differs from its original complete source",
                    )?;
                } else {
                    // Structural identity still has to validate even when the
                    // source key itself is legitimately unavailable.
                    let binding = self.facts.bindings.get(row.binding).ok_or_else(|| {
                        "unknown storage declaration binding is absent".to_owned()
                    })?;
                    require(
                        !binding.parameter && binding.owner == row.activation,
                        "unknown storage declaration borrowed another binding",
                    )?;
                    self.storage_activation(row.context, row.activation)?;
                    let originals: Vec<_> = sites
                        .bindings
                        .iter()
                        .filter(|site| {
                            Some(site.owner) == row.context.owner
                                && site.binding.pattern.span == row.declaration
                        })
                        .collect();
                    require(
                        originals.len() == 1 && row.declared == originals[0].binding.ty.is_some(),
                        "unknown storage declaration lost its original AST",
                    )?;
                    self.storage_observation(
                        row.initializer,
                        &originals[0].binding.value,
                        row.context,
                    )?;
                    let mut names = Vec::new();
                    pattern_paths(
                        &originals[0].binding.pattern,
                        &mut Vec::new(),
                        true,
                        &mut names,
                        &mut 4096,
                    )?;
                    require(
                        names.iter().any(|(span, name, path, _)| {
                            *span == binding.span && *name == binding.name && *path == row.path
                        }),
                        "unknown storage declaration changed its actual pattern path",
                    )?;
                }
            }
            // The original binding arena independently requires ledger rows.
            // Removing a ledger and every later write certificate cannot hide
            // a local declaration that was actually introduced by the program.
            for (id, binding) in self
                .facts
                .bindings
                .iter()
                .enumerate()
                .filter(|(_, binding)| !binding.parameter)
            {
                let mut matches = false;
                for site in &sites.bindings {
                    let mut names = Vec::new();
                    pattern_paths(
                        &site.binding.pattern,
                        &mut Vec::new(),
                        true,
                        &mut names,
                        &mut 4096,
                    )?;
                    matches |= names
                        .iter()
                        .any(|(span, name, _, _)| *span == binding.span && *name == binding.name);
                }
                if matches {
                    require(
                        declarations.contains_key(&id),
                        "an actual binding lost its immutable storage source",
                    )?;
                }
            }
            let mut covered = BTreeSet::new();
            for write in &self.facts.storage_writes {
                require(
                    covered.insert(write.rhs.expression),
                    "storage writes borrowed one RHS occurrence twice",
                )?;
                self.storage_activation(write.context, write.activation)?;
                let originals: Vec<_> = sites
                    .assignments
                    .iter()
                    .filter(|site| {
                        Some(site.owner) == write.context.owner
                            && site.target.span == write.span
                            && site.operator == write.operator
                    })
                    .collect();
                let [site] = originals.as_slice() else {
                    return Err("storage write is not an original assignment".into());
                };
                let input = self.storage_observation(write.rhs, site.value, write.context)?;
                require(
                    input.ty != Ty::Never,
                    "completed RHS storage receipt claims an abrupt expression",
                )?;
                let expected = match (&site.target.kind, &write.destination) {
                    (ExprKind::Name(name), StorageDestination::Binding(id)) => {
                        let binding = self
                            .facts
                            .bindings
                            .get(*id)
                            .ok_or_else(|| "storage target binding is absent".to_owned())?;
                        require(
                            binding.name == *name
                                && binding.mode.is_reassignable()
                                && write.completed,
                            "storage Name destination differs from its real assignable binding",
                        )?;
                        let declaration = declarations.get(id).ok_or_else(|| {
                            "storage target lost its declaration source".to_owned()
                        })?;
                        require(
                            declaration.initializer.expression < write.rhs.expression,
                            "storage target declaration is later than its write",
                        )?;
                        if binding.owner != write.activation {
                            require(
                                self.storage_captured_binding(
                                    write.context,
                                    write.activation,
                                    name,
                                    *id,
                                    declaration,
                                )?,
                                "storage target is not the actual captured lexical binding",
                            )?;
                        } else {
                            // Without a recorded target read, two simultaneously
                            // plausible same-named slots cannot prove a choice.
                            let alternatives = declarations
                                .values()
                                .filter(|candidate| {
                                    candidate.activation == write.activation
                                        && candidate.initializer.expression < write.rhs.expression
                                        && self.facts.bindings.get(candidate.binding).is_some_and(
                                            |other| {
                                                other.name == *name && other.mode.is_reassignable()
                                            },
                                        )
                                })
                                .count();
                            require(
                                alternatives == 1,
                                "storage target has ambiguous same-name declaration sources",
                            )?;
                        }
                        declaration.key.clone()
                    }
                    (
                        ExprKind::Field { base, field, .. },
                        StorageDestination::Projection {
                            receiver,
                            selector,
                            slot,
                        },
                    ) => {
                        require(
                            selector.is_none()
                                && *slot
                                    == field
                                        .parse()
                                        .map(Slot::Tuple)
                                        .unwrap_or_else(|_| Slot::Field(field.clone())),
                            "storage field destination changed its original projection",
                        )?;
                        self.storage_write_interval(
                            write.rhs,
                            *receiver,
                            site.value,
                            write.context,
                        )?;
                        let source = self.storage_observation(*receiver, base, write.context)?;
                        if source.ty == Ty::Never {
                            require(
                                !write.completed && write.expected.is_none(),
                                "abrupt storage receiver claims a completed write",
                            )?;
                            continue;
                        }
                        require(
                            write.completed,
                            "normal storage field write was marked aborted",
                        )?;
                        let key = self.original_observed_source_key(
                            base,
                            receiver.expression,
                            write.context,
                            &sites,
                        )?;
                        self.storage_projection_source_key(&key, slot, write.context)?
                    }
                    (
                        ExprKind::Index { base, index, .. },
                        StorageDestination::Projection {
                            receiver,
                            selector,
                            slot,
                        },
                    ) => {
                        self.storage_write_interval(
                            write.rhs,
                            *receiver,
                            site.value,
                            write.context,
                        )?;
                        let source = self.storage_observation(*receiver, base, write.context)?;
                        if source.ty == Ty::Never {
                            require(
                                !write.completed && selector.is_none() && write.expected.is_none(),
                                "abrupt indexed receiver claims a write",
                            )?;
                            continue;
                        }
                        let selector = selector
                            .ok_or_else(|| "storage index lost its actual selector".to_owned())?;
                        self.storage_write_interval(*receiver, selector, base, write.context)?;
                        let selected = self.storage_observation(selector, index, write.context)?;
                        if selected.ty == Ty::Never {
                            require(
                                !write.completed && write.expected.is_none(),
                                "abrupt storage selector claims a write",
                            )?;
                            continue;
                        }
                        require(
                            write.completed,
                            "normal storage index write was marked aborted",
                        )?;
                        let key = self.original_observed_source_key(
                            base,
                            receiver.expression,
                            write.context,
                            &sites,
                        )?;
                        let expected_slot = if matches!(key, ArgumentKey::Map { .. }) {
                            Slot::AnyIndex
                        } else if let Some(Constant::Integer(index)) = selected.constant {
                            Slot::Index(index as i64)
                        } else {
                            Slot::AnyIndex
                        };
                        require(
                            *slot == expected_slot,
                            "storage index changed its actual selected slot",
                        )?;
                        if let ArgumentKey::Map { key: map_key, .. } = &key {
                            let actual = self
                                .original_source_key(index, selected, write.context, &sites)
                                .ok();
                            let fresh = source_reception::construction(index, &mut 4096);
                            require(
                                storage_compatible(map_key, actual.as_ref(), fresh.as_ref())
                                    == Some(true),
                                "storage map selector does not fit its original key source",
                            )?;
                        }
                        self.storage_projection_source_key(&key, slot, write.context)?
                    }
                    _ => return Err("storage write changed its real destination form".into()),
                };
                require(
                    expected == write.expected,
                    "storage write borrowed a different expected source schema",
                )?;
                let expected = expected.ok_or_else(|| {
                    "storage write has an unresolved original destination source".to_owned()
                })?;
                let actual = self
                    .original_source_key(site.value, input, write.context, &sites)
                    .ok();
                let fresh = source_reception::construction(site.value, &mut 4096);
                let answer = if crate::sema::source_types::key_is_coordinate_free(&expected) {
                    Some(true)
                } else if write.operator != "=" {
                    Some(false)
                } else {
                    storage_compatible(&expected, actual.as_ref(), fresh.as_ref())
                };
                require(
                    answer == Some(true),
                    "storage original RHS does not prove the destination source coordinates",
                )?;
            }
            // Reverse coverage starts from actual RHS roots, not from a
            // supposedly complete list supplied by the write certificates.
            for site in &sites.assignments {
                for row in self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| row.context.owner == Some(site.owner))
                {
                    let value = self.facts.expressions.get(row.expression).ok_or_else(|| {
                        "storage reverse coverage expression is absent".to_owned()
                    })?;
                    if value.span == site.value.span && value.value.ty != Ty::Never {
                        require(
                            covered.contains(&row.expression),
                            "an actual assignment lost its storage reception receipt",
                        )?;
                    }
                }
            }
            Ok(())
        };
        run().map_err(|message| (fallback, None, message))
    }

    fn storage_write_interval(
        &self,
        before: StorageObservation,
        after: StorageObservation,
        before_syntax: &Expr,
        context: InvocationContext,
    ) -> Check {
        require(
            before.expression < after.expression
                && before.allocation_epoch <= after.allocation_epoch,
            "storage operand order or allocation epochs moved backwards",
        )?;
        require(
            !self.facts.invocation_expressions.iter().any(|row| {
                row.context == context
                    && before.expression < row.expression
                    && row.expression < after.expression
                    && self
                        .facts
                        .expressions
                        .get(row.expression)
                        .is_some_and(|value| value.span == before_syntax.span)
            }),
            "storage target borrowed a later repeated RHS occurrence",
        )
    }
}

pub(in crate::sema::record_bound_validation) fn storage_compatible(
    expected: &ArgumentKey,
    actual: Option<&ArgumentKey>,
    fresh: Option<&Construction>,
) -> Option<bool> {
    if contains_callable(expected, &mut 4096)? {
        return None;
    }
    if crate::sema::source_types::key_is_coordinate_free(expected) {
        return Some(true);
    }
    if let Some(actual) = actual {
        return source_reception::compatible(expected, actual, fresh, &mut 4096);
    }
    match (expected, fresh) {
        (ArgumentKey::Array { length, element }, Some(Construction::Array(items)))
            if items.is_empty() =>
        {
            source_reception::complete(element, &mut 4096)?;
            Some(
                length
                    .as_ref()
                    .is_none_or(|length| length == "const(int:0)"),
            )
        }
        _ => None,
    }
}

fn contains_callable(key: &ArgumentKey, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(1)?;
    let children: Vec<&ArgumentKey> = match key {
        ArgumentKey::Callable { .. } => return Some(true),
        ArgumentKey::Array { element, .. } => vec![element],
        ArgumentKey::Map { key, value } => vec![key, value],
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            arguments.iter().collect()
        }
        ArgumentKey::Record { fields, row } => fields
            .iter()
            .map(|field| &field.2)
            .chain(row.iter().map(|row| row.as_ref()))
            .collect(),
        ArgumentKey::Closed(_) => return None,
        ArgumentKey::Binder { .. } => vec![],
    };
    for child in children {
        if contains_callable(child, work)? {
            return Some(true);
        }
    }
    Some(false)
}

fn expression_path<'a>(
    expression: &'a Expr,
    path: &mut Vec<Slot>,
    work: &mut usize,
) -> Option<&'a str> {
    *work = work.checked_sub(1)?;
    match &expression.kind {
        ExprKind::Name(name) => Some(name),
        ExprKind::Field { base, field, .. } => {
            let root = expression_path(base, path, work)?;
            path.push(
                field
                    .parse()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone())),
            );
            Some(root)
        }
        ExprKind::Index { base, .. } => {
            let root = expression_path(base, path, work)?;
            path.push(Slot::AnyIndex);
            Some(root)
        }
        _ => None,
    }
}

fn pattern_paths(
    pattern: &Pattern,
    path: &mut Vec<Slot>,
    known: bool,
    out: &mut Vec<(Span, String, Vec<Slot>, bool)>,
    work: &mut usize,
) -> Check {
    *work = work
        .checked_sub(1)
        .ok_or_else(|| "storage pattern replay exceeds its budget".to_owned())?;
    match &pattern.kind {
        PatternKind::Name(name) => out.push((pattern.span, name.clone(), path.clone(), known)),
        PatternKind::Mode { pattern, .. } => pattern_paths(pattern, path, known, out, work)?,
        PatternKind::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                path.push(Slot::Tuple(index as u32));
                pattern_paths(item, path, known, out, work)?;
                path.pop();
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                path.push(Slot::Field(field.name.clone()));
                pattern_paths(&field.pattern, path, known, out, work)?;
                path.pop();
            }
            if let Some(name) = rest_binding {
                out.push((pattern.span, name.clone(), Vec::new(), false));
            }
        }
        PatternKind::Constructor { arguments, .. } | PatternKind::Alternative(arguments) => {
            for argument in arguments {
                pattern_paths(argument, &mut Vec::new(), false, out, work)?;
            }
        }
        PatternKind::Type {
            binder: Some(name), ..
        } => out.push((pattern.span, name.clone(), Vec::new(), false)),
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        copy_contract::{
            CopyCallEvent, CopyCallEventId, CopyInvocation, CopyInvocationStatus, CopyValueSnapshot,
        },
        copy_templates::InstanceId,
        effect_identity::{
            ClosureInvocation, ClosureInvocationId, InvocationCall, InvocationExpression,
        },
        facts::{LoanId, NodeId, RootId},
        model::{BindingInfo, ClosureInfo},
        summary::InvocationSummary,
    };
    use ril_compiler_core::{ids::ClosureSiteId, source::FileId};
    use ril_syntax::ast::{BindingMode, Function};

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 0,
            end: 1,
        }
    }
    fn context(owner: CallableOwner) -> InvocationContext {
        InvocationContext {
            invocation: None,
            owner: Some(owner),
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        }
    }
    fn function(binding: BindingId) -> FunctionInfo {
        FunctionInfo {
            hir_id: None,
            definition: DefinitionId(0),
            lexical_owner: Some(CallableOwner::Global),
            typing_environment: Default::default(),
            syntax: Function {
                visibility: Visibility::Private,
                is_meta: false,
                is_halt: false,
                name: "work".into(),
                generics: vec![],
                parameters: vec![],
                return_type: None,
                annotations: vec![],
                signature_where: vec![],
                body: None,
                span: span(),
            },
            lexical: [("counter".into(), binding)].into(),
            owner: None,
            handler_context: vec![],
            lexical_scope: 0,
            environment: None,
            captures: BTreeSet::new(),
            writes: BTreeSet::new(),
            environment_published: false,
        }
    }
    fn binding(id: BindingId) -> BindingInfo {
        BindingInfo {
            name: "counter".into(),
            value: Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
            mode: BindingMode::Var,
            owner: ScopeId(0),
            lexical_scope: 0,
            span: span(),
            root: RootId(id as u32),
            cell: None,
            alive: true,
            slot_used: true,
            write_used: false,
            used: true,
            forwarded: BTreeSet::new(),
            parameter: false,
        }
    }
    fn source(id: BindingId) -> BindingSource {
        BindingSource {
            binding: id,
            context: context(CallableOwner::Global),
            activation: ScopeId(0),
            declaration: span(),
            declared: false,
            initializer: StorageObservation {
                expression: 0,
                allocation_epoch: 0,
            },
            path: vec![],
            key: None,
        }
    }
    fn model() -> (SemanticFacts, InvocationContext) {
        let mut facts = SemanticFacts::default();
        let mut current = context(CallableOwner::Function(DefinitionId(0)));
        current.invocation = Some(InstanceId(0));
        facts
            .allocated_scopes
            .extend([ScopeId(0), ScopeId(10), ScopeId(20), ScopeId(30)]);
        facts.scope_parents.insert(ScopeId(20), ScopeId(0));
        facts.functions = vec![function(0), function(1)];
        facts.bindings = vec![binding(0), binding(1)];
        facts.copy_invocations.push(CopyInvocation {
            id: InstanceId(0),
            parent: None,
            caller: None,
            caller_owner: Some(CallableOwner::Global),
            caller_activation: Some(ScopeId(0)),
            entry_allocation_epoch: 0,
            target: DefinitionId(0),
            span: span(),
            declaration_probe: false,
            direct: true,
            source_event: Some(CopyCallEventId(0)),
            arguments: vec![],
            boundaries: BTreeSet::new(),
            result: None,
            resource_copies: vec![],
            status: CopyInvocationStatus::Completed,
        });
        let mut callee = Value::scalar(Ty::Unknown, None, CauseId(0));
        callee.callables.push(Callable::Named(1));
        facts.expressions.push(crate::sema::ExpressionFact {
            allocation_epoch: 0,
            source_id: None,
            span: span(),
            value: callee,
        });
        facts.invocation_expressions.push(InvocationExpression {
            context: context(CallableOwner::Global),
            expression: 0,
            argument_of: None,
        });
        facts.invocation_calls.push(InvocationCall {
            invocation: InstanceId(0),
            caller_owner: Some(CallableOwner::Global),
            caller_closure: None,
            caller_closure_invocation: None,
            default_use: None,
        });
        facts.copy_call_events.push(CopyCallEvent {
            source_id: None,
            id: CopyCallEventId(0),
            callee_expression: Some(0),
            result_expression: None,
            owner: Some(CallableOwner::Global),
            parent: None,
            span: span(),
            target: Some(DefinitionId(0)),
            direct: true,
            copy_operation: None,
            references: vec![],
        });
        facts.invocations.push(InvocationSummary {
            activation: Some(ScopeId(20)),
            context: Some(current),
            ..Default::default()
        });
        (facts, current)
    }
    fn replay(facts: &SemanticFacts) -> Replay<'_> {
        Replay {
            facts,
            observations: super::super::observation_index::ObservationIndex::new(facts).unwrap(),
            functions: BTreeMap::new(),
            bounds: BTreeMap::new(),
        }
    }

    #[test]
    fn current_named_activation_is_not_its_retained_outer_closure_context() {
        let (mut facts, mut current) = model();
        current.closure = Some(0);
        current.closure_invocation = Some(ClosureInvocationId(0));
        facts.invocations[0].context = Some(current);
        facts.closures.push(ClosureInfo {
            hir_id: None,
            site: Some(ClosureSiteId(0)),
            creation_invocation: None,
            creation_closure: None,
            creation_default: None,
            handler_context: vec![],
            parameters: vec![],
            body: Expr {
                hir_id: None,
                kind: ExprKind::Error,
                span: span(),
            },
            lexical: BTreeMap::new(),
            captures: BTreeSet::new(),
            writes: BTreeSet::new(),
            owner: ScopeId(0),
            node: NodeId(0),
        });
        facts.closure_invocations.push(ClosureInvocation {
            id: ClosureInvocationId(0),
            source_event: None,
            caller_activation: ScopeId(0),
            activation: Some(ScopeId(10)),
            closure: 0,
            parent_named: Some(InstanceId(0)),
            parent_closure: None,
            caller_owner: Some(CallableOwner::Global),
            site: span(),
            probe: false,
            budget_validation: false,
            status: CopyInvocationStatus::Completed,
        });
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(20))
                .is_ok()
        );
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(10))
                .is_err()
        );
        current.owner = Some(CallableOwner::Lambda(ClosureSiteId(0)));
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(10))
                .is_ok()
        );
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(20))
                .is_err()
        );
    }

    #[test]
    fn ambient_globals_and_retained_locals_use_the_actual_named_callee_binding_ids() {
        let (mut facts, current) = model();
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &source(1))
                .unwrap()
        );
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 0, &source(0))
                .unwrap()
        );
        facts.bindings[1].owner = ScopeId(10);
        let mut local = source(1);
        local.activation = ScopeId(10);
        local.context = current;
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        facts.functions[1].captures.insert(1);
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        // Without a physical callee no convenient same-definition copy can
        // select the environment; all remaining candidates must agree.
        facts.copy_invocations[0].source_event = None;
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
        facts.functions[0].lexical.insert("counter".into(), 1);
        facts.functions[0].captures.insert(1);
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(20), "counter", 1, &local)
                .unwrap()
        );
    }

    #[test]
    fn operation_frames_require_their_exact_entry_context_handler_and_operation() {
        let (mut facts, current) = model();
        facts.handlers.push(HandlerFact {
            site: None,
            callable_owner: current.owner,
            id: 0,
            boundary: 4,
            span: span(),
            operations: vec![7],
            arm_spans: vec![],
            lexical: [("counter".into(), 1)].into(),
            answer: None,
            arms: vec![],
            outer: vec![],
        });
        facts
            .operation_loan_starts
            .push(crate::sema::resumption::OperationLoanStart {
                loan: LoanId(0),
                activation: ScopeId(30),
                boundary: 4,
                handler: 0,
                operation: 7,
                parameter: 0,
                temporary: true,
                context: current,
                source: CopyValueSnapshot {
                    value: Value::scalar(Ty::Unit, None, CauseId(0)),
                    nodes: vec![],
                    relations: vec![],
                },
                allocation_epoch: 0,
                span: span(),
                cause: CauseId(0),
            });
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(30))
                .is_ok()
        );
        assert!(
            replay(&facts)
                .storage_captured_binding(current, ScopeId(30), "counter", 1, &source(1))
                .unwrap()
        );
        assert!(
            !replay(&facts)
                .storage_captured_binding(current, ScopeId(30), "counter", 0, &source(0))
                .unwrap()
        );
        let mut foreign = current;
        foreign.invocation = Some(InstanceId(99));
        assert!(
            replay(&facts)
                .storage_activation(foreign, ScopeId(30))
                .is_err()
        );
        facts.operation_loan_starts[0].operation = 8;
        assert!(
            replay(&facts)
                .storage_activation(current, ScopeId(30))
                .is_err()
        );
    }
}
