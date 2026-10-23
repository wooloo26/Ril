//! Original callable inputs are replayed from physical observations and value
//! derivations. An entry snapshot alone cannot invent an input Source schema.
use super::*;
use crate::sema::{
    application_effect::{CallableEntry, EntryOrigin},
    copy_contract::CopyInvocation,
    effect_identity::ClosureInvocation,
};
use ril_compiler_core::ids::ExprId;

use crate::sema::application_effect::generated_entries::{
    EntryArguments as Arguments, GeneratedEntryKey, GeneratedInput,
};

enum Input {
    Physical {
        source: ExprId,
        observation: usize,
        copy: Option<crate::sema::copy_contract::CopyBoundaryId>,
    },
    Scalar(crate::sema::application_effect::ScalarInput),
}

struct EntrySource<'a, 'p> {
    entry: &'a CallableEntry,
    key: GeneratedEntryKey,
    slot: usize,
    sites: &'a super::super::explicit_named::SourceSites<'p>,
    depth: usize,
}

impl Replay<'_> {
    fn signature_entry_graph(&self, entry: &CallableEntry, work: &mut usize) -> Check {
        let EntryOrigin::SignatureProbe(source) = &entry.origin else {
            return Ok(());
        };
        let scope = super::reception::environment_scope(&source.environment, work)?;
        let (root, _) =
            self.source_type_header_raw(&source.header, &scope, source.environment.clone(), work)?;
        let parameters = super::graph_sources::schema_work(work, |budget| {
            root.project_steps(&source.path, budget)?
                .callable_parameters(budget)
        })?;
        require(
            parameters.len() == entry.arguments.len(),
            "signature entry changed its original graph arity",
        )?;
        for (slot, (mode, _)) in parameters.iter().enumerate() {
            require(
                entry
                    .arguments
                    .argument(slot)
                    .is_some_and(|(actual, _)| actual == *mode),
                "signature entry changed its original graph parameter mode",
            )?;
        }
        Ok(())
    }

    pub(in crate::sema::record_bound_validation) fn inferred_lambda_receipt(
        &self,
        call: &ClosureInvocation,
        slot: usize,
        value: &Value,
        observation: usize,
        work: &mut usize,
    ) -> Check {
        use crate::sema::facts::{Participant, Permission};
        use ril_syntax::ast::ParameterMode;
        let &binding_id = value
            .sources
            .first()
            .ok_or("inferred formal has no original binding")?;
        let binding = self
            .facts
            .bindings
            .get(binding_id)
            .ok_or("inferred formal binding is absent")?;
        let argument = call
            .entry
            .arguments
            .get(slot)
            .ok_or("inferred formal has no actual input")?;
        let mode = argument.mode;
        let original = argument.value();
        let epoch = self.facts.expressions[observation].allocation_epoch;
        let origins = transported_origins(
            self.facts,
            &original.origins,
            call.entry.allocation_epoch,
            epoch,
            work,
        )?;
        require(
            value.sources == BTreeSet::from([binding_id])
                && binding.forwarded == original.sources
                && value.origins == origins
                && value.callables == original.callables
                && value.publication
                    == if mode == ParameterMode::Read {
                        original.publication
                    } else {
                        Publication::Live
                    },
            "inferred formal changed its actual input or receiving scope",
        )?;
        if mode == ParameterMode::Read {
            *work = work
                .checked_sub(original.participants.len() + 1)
                .ok_or("inferred read reception exceeds its work bound")?;
            let mut participants = original.participants.clone();
            if participants.is_empty() {
                participants.insert(Participant::Root(binding.root));
            }
            require(
                value.permission == Permission::Read
                    && !value.construction
                    && !value.marker
                    && value.participants == participants,
                "inferred formal recovered authority while receiving a read input",
            )?;
        } else {
            *work = work
                .checked_sub(self.facts.invocation_loan_starts.len())
                .ok_or("inferred loan reception exceeds its work bound")?;
            let mut loans = self.facts.invocation_loan_starts.iter().filter(|loan| {
                loan.closure == Some(call.id)
                    && loan.parameter as usize == slot
                    && loan.activation == binding.owner
                    && loan.bindings.contains(&binding_id)
            });
            let loan = loans
                .next()
                .ok_or("inferred formal has no original invocation loan")?;
            require(
                loans.next().is_none()
                    && loan.retained == (mode == ParameterMode::SharedMut)
                    && value.permission == Permission::Write
                    && value.participants == BTreeSet::from([Participant::Loan(loan.loan)]),
                "inferred formal changed its actual loan or parameter mode",
            )?;
            self.input_value_transport(
                original,
                &loan.source,
                call.entry.allocation_epoch,
                loan.allocation_epoch,
            )?;
        }
        Ok(())
    }

    fn entry_input(
        &self,
        entry: &CallableEntry,
        key: GeneratedEntryKey,
        slot: usize,
        work: &mut usize,
    ) -> Check<Input> {
        *work = work
            .checked_sub(1)
            .ok_or("callable input replay exceeds its work bound")?;
        let (_, argument) = entry
            .arguments
            .argument(slot)
            .ok_or("callable entry lost its input slot")?;
        let input = match &entry.origin {
            EntryOrigin::Application(id) => {
                *work = work
                    .checked_sub(self.facts.call_arguments.len())
                    .ok_or("callable preparation lookup exceeds its work bound")?;
                let mut rows = self
                    .facts
                    .call_arguments
                    .iter()
                    .filter(|row| row.source_event == *id);
                let row = rows
                    .next()
                    .ok_or("callable input has no physical preparation")?;
                require(
                    rows.next().is_none() && row.evaluation_complete,
                    "callable input preparation is incomplete or duplicated",
                )?;
                let token = match row.slots.get(slot) {
                    Some(ArgumentSource::Supplied) => row
                        .supplied
                        .get(&(slot as u32))
                        .map(|token| token.expression),
                    Some(ArgumentSource::Default(id)) => self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|receipt| {
                            receipt.id == *id
                                && receipt.origin == DefaultOrigin::Call(row.source_event)
                                && receipt.parameter as usize == slot
                        })
                        .and_then(|receipt| receipt.result_expression),
                    _ => None,
                }
                .ok_or("callable input lost its exact supplied/default observation")?;
                let fact = self
                    .facts
                    .expressions
                    .get(token)
                    .ok_or("callable input is outside its value arena")?;
                let evaluation = self
                    .facts
                    .evaluations
                    .get(token)
                    .ok_or("callable input has no actual evaluation")?;
                let parent = entry
                    .parent
                    .and_then(|id| self.facts.activations.get(id.0 as usize))
                    .ok_or("callable input has no owning activation")?;
                require(
                    evaluation.context
                        == if let Some(ArgumentSource::Default(id)) = row.slots.get(slot) {
                            let receipt = &self.facts.default_uses[id.0 as usize];
                            InvocationContext {
                                owner: receipt.owner,
                                default_use: Some(*id),
                                ..receipt.caller
                            }
                        } else {
                            entry.caller_context
                        }
                        && token >= parent.start_expression
                        && Some(token) < parent.result.map(|id| id.0 as usize),
                    "callable input borrowed another activation's observation",
                )?;
                self.input_value_transport(
                    &fact.value,
                    argument,
                    fact.allocation_epoch,
                    entry.allocation_epoch,
                )?;
                require(
                    fact.value.callables == argument.callables
                        && fact.value.permission == argument.permission
                        && fact.value.publication == argument.publication
                        && fact.value.participants == argument.participants,
                    "callable input changed its original authority or callable targets",
                )?;
                Input::Physical {
                    source: fact.source_id.ok_or("callable input lost its HIR source")?,
                    observation: token,
                    copy: None,
                }
            }
            EntryOrigin::Generated { .. } => {
                let authenticated = self.generated_entries.get(key, work)?;
                match authenticated.input(slot)? {
                    GeneratedInput::Copied {
                        source,
                        observation,
                        boundary: proof,
                    } => {
                        let fact = self
                            .facts
                            .expressions
                            .get(observation)
                            .ok_or("generated input is outside its arena")?;
                        require(
                            proof.source.ty == fact.value.ty
                                && proof.source.callables == fact.value.callables,
                            "generated input copy changed its source",
                        )?;
                        self.input_view_transport(
                            &fact.value,
                            &proof.source,
                            fact.allocation_epoch,
                            proof.input_allocation_epoch,
                        )?;
                        if proof.source.cause != fact.value.cause {
                            require(
                                fact.value.construction
                                    && proof.source.publication == Publication::Immutable
                                    && proof.source.permission
                                        == crate::sema::facts::Permission::Read
                                    && self
                                        .facts
                                        .explanations
                                        .causes
                                        .get(proof.source.cause.0 as usize)
                                        .is_some_and(|cause| cause.parents == [fact.value.cause]),
                                "generated input lost its original construction reception",
                            )?;
                        }
                        let output = proof
                            .output
                            .as_ref()
                            .ok_or("generated input has no established copy output")?;
                        let epoch = proof
                            .output_allocation_epoch
                            .ok_or("generated input copy output has no birth epoch")?;
                        require(
                            proof.input_allocation_epoch <= epoch
                                && output.callables == argument.callables
                                && output.permission == argument.permission
                                && output.publication == argument.publication,
                            "generated input changed its copying epoch or output authority",
                        )?;
                        self.input_value_transport(
                            output,
                            argument,
                            epoch,
                            entry.allocation_epoch,
                        )?;

                        Input::Physical {
                            source,
                            observation,
                            copy: Some(proof.id),
                        }
                    }
                    GeneratedInput::Widened {
                        source,
                        observation,
                        original,
                    } => {
                        let mut origins = transported_origins(
                            self.facts,
                            &original.value.origins,
                            original.allocation_epoch,
                            entry.allocation_epoch,
                            work,
                        )?;
                        origins.choices.clear();
                        require(
                            origins == argument.origins
                                && original.value.ty == argument.ty
                                && original.value.cause == argument.cause
                                && original.value.sources == argument.sources
                                && original.value.source_type_witness
                                    == argument.source_type_witness
                                && original.value.results == argument.results
                                && original.value.outer_results == argument.outer_results
                                && original.value.permission == argument.permission
                                && original.value.publication == argument.publication
                                && original.value.participants == argument.participants
                                && original.value.callables == argument.callables
                                && argument.temporary
                                && argument.constant.is_none(),
                            "record callback receiver changed during widening or borrowing",
                        )?;

                        Input::Physical {
                            source,
                            observation,
                            copy: None,
                        }
                    }
                    GeneratedInput::Scalar(kind) => {
                        use crate::sema::application_effect::ScalarInput;
                        if let ScalarInput::ByteSuffix(source) = kind {
                            let input = self
                                .facts
                                .expressions
                                .get(source.0 as usize)
                                .ok_or("byte suffix source is absent")?;
                            require(
                                input.value.ty == Ty::Bytes && input.value.cause == argument.cause,
                                "byte suffix borrowed another input cause or type",
                            )?;
                        }
                        require(
                            argument.ty
                                == match kind {
                                    ScalarInput::PositiveInt => Ty::Int("int".into()),
                                    ScalarInput::ByteSuffix(_) | ScalarInput::BufferedBytes(_) => {
                                        Ty::Bytes
                                    }
                                }
                                && argument.origins.nodes.is_empty()
                                && argument.sources.is_empty()
                                && argument.callables.is_empty()
                                && argument.participants.is_empty()
                                && argument.results.is_empty()
                                && argument.outer_results.is_empty()
                                && argument.scoped.is_empty()
                                && argument.constant.is_none()
                                && !argument.construction
                                && !argument.marker,
                            "record callback changed its declared generated scalar",
                        )?;

                        Input::Scalar(kind)
                    }
                }
            }
            _ => {
                return Err(
                    "inferred callable input needs its actual receiving Source origin".into(),
                );
            }
        };
        Ok(input)
    }

    pub(in crate::sema::record_bound_validation) fn closure_entry_source_schema_if_known(
        &self,
        call: &ClosureInvocation,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<OriginalSource>> {
        if matches!(call.entry.origin, EntryOrigin::SignatureProbe(_)) {
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("signature closure input has no original HIR")?;
            let auth = super::graph_sources::schema_work(work, |budget| {
                crate::sema::application_effect::closure_signature_assumption(
                    call,
                    slot,
                    hir,
                    &self.facts.bindings,
                    self.facts.allocation_history.len(),
                    budget,
                )
            })?;
            let scope = super::reception::environment_scope(auth.environment, work)?;
            let (root, environment) =
                self.source_type_header_raw(auth.header, &scope, auth.environment.clone(), work)?;
            let parameter = super::graph_sources::schema_work(work, |budget| {
                auth.parameter_schema(&root, budget)
            })?;
            let selected = self.source_selected_schemas(&environment, work)?;
            return self
                .source_substitute_schema(parameter, environment, &selected, work)
                .map(Some);
        }
        self.entry_source_schema_if_known(
            EntrySource {
                entry: &call.entry,
                key: GeneratedEntryKey::Closure(call.id),
                slot,
                sites,
                depth,
            },
            work,
        )
    }

    pub(super) fn named_entry_source_schema(
        &self,
        call: &CopyInvocation,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        self.function(call.target)?;
        self.entry_source_schema(
            &call.entry,
            GeneratedEntryKey::Named(call.id),
            slot,
            sites,
            work,
            0,
        )
    }

    pub(super) fn named_entry_source_schema_if_known(
        &self,
        call: &CopyInvocation,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        self.function(call.target)?;
        self.entry_source_schema_if_known(
            EntrySource {
                entry: &call.entry,
                key: GeneratedEntryKey::Named(call.id),
                slot,
                sites,
                depth: 0,
            },
            work,
        )
    }

    fn entry_source_schema(
        &self,
        entry: &CallableEntry,
        key: GeneratedEntryKey,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<OriginalSource> {
        self.entry_source_schema_if_known(
            EntrySource {
                entry,
                key,
                slot,
                sites,
                depth,
            },
            work,
        )?
        .ok_or_else(|| "callable input has no complete original graph".into())
    }

    fn entry_source_schema_if_known(
        &self,
        source: EntrySource<'_, '_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let EntrySource {
            entry,
            key,
            slot,
            sites,
            depth,
        } = source;
        require(
            depth < 64,
            "callable input Source ancestry exceeds its bound",
        )?;
        let input = self.entry_input(entry, key, slot, work)?;
        let Input::Physical {
            source,
            observation,
            copy,
        } = input
        else {
            let Input::Scalar(kind) = input else {
                unreachable!()
            };
            return self
                .source_header_schema(
                    &ArgumentKey::Name {
                        name: match kind {
                            crate::sema::application_effect::ScalarInput::PositiveInt => "int",
                            crate::sema::application_effect::ScalarInput::ByteSuffix(_)
                            | crate::sema::application_effect::ScalarInput::BufferedBytes(_) => {
                                "bytes"
                            }
                        }
                        .into(),
                        arguments: vec![],
                    },
                    FrozenEnvironment::default(),
                    work,
                )
                .map(Some);
        };
        let syntax = sites
            .expressions
            .get(&source)
            .ok_or("callable input lost its original indexed expression")?;
        let fact = &self.facts.expressions[observation];
        let context = self.observations.row(observation, work)?.context;
        let Some((schema, environment)) = self.original_source_schema_inner(
            syntax,
            &fact.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: depth + 1,
                observation: Some(observation),
            },
        )?
        else {
            return Ok(None);
        };
        if let Some(id) = copy {
            super::graph_sources::schema_work(work, |budget| {
                schema.copy_view(self.facts.copy_boundaries[id.0 as usize].mode, budget)
            })
            .map(|schema| Some((schema, environment)))
        } else {
            Ok(Some((schema, environment)))
        }
    }

    pub(in crate::sema::record_bound_validation) fn callable_inputs(&self) -> Check {
        let mut work = self.callable_input_work;
        let sites = super::super::explicit_named::source_sites_base(self.facts)?;
        work = work
            .checked_sub(self.facts.bindings.len())
            .ok_or("inferred formal coverage work exhausted")?;
        for (binding, info) in self.facts.bindings.iter().enumerate() {
            if info.parameter {
                self.inferred_closure_parameter_schema(binding, &sites, &mut work)?;
            }
        }
        for call in &self.facts.closure_invocations {
            self.signature_entry_graph(&call.entry, &mut work)?;
            if !matches!(
                call.entry.origin,
                EntryOrigin::Application(_) | EntryOrigin::Generated { .. }
            ) {
                continue;
            }
            for slot in 0..call.entry.arguments.len() {
                self.entry_input(
                    &call.entry,
                    GeneratedEntryKey::Closure(call.id),
                    slot,
                    &mut work,
                )?;
            }
        }
        for call in &self.facts.copy_invocations {
            self.signature_entry_graph(&call.entry, &mut work)?;
            if !matches!(
                call.entry.origin,
                EntryOrigin::Application(_) | EntryOrigin::Generated { .. }
            ) {
                continue;
            }
            self.function(call.target)?;
            for slot in 0..call.entry.arguments.len() {
                self.entry_input(
                    &call.entry,
                    GeneratedEntryKey::Named(call.id),
                    slot,
                    &mut work,
                )?;
            }
        }
        Ok(())
    }
}

fn transported_origins(
    facts: &SemanticFacts,
    original: &crate::sema::model::Origins,
    from: usize,
    to: usize,
    work: &mut usize,
) -> Check<crate::sema::model::Origins> {
    require(
        from <= to && to <= facts.allocation_history.len(),
        "formal input transport changed its birth epoch",
    )?;
    *work = work
        .checked_sub(original.nodes.len() + original.choices.len())
        .ok_or("formal input origin clone exceeds its work bound")?;
    let mut sets = 1usize;
    for branches in original.choices.values() {
        *work = work
            .checked_sub(branches.len())
            .ok_or("formal input choice clone exceeds its work bound")?;
        sets = sets
            .checked_add(branches.len())
            .ok_or("formal input choice count overflow")?;
        for branch in branches {
            *work = work
                .checked_sub(branch.len())
                .ok_or("formal input branch clone exceeds its work bound")?;
        }
    }
    *work = work
        .checked_sub(
            (to - from)
                .checked_mul(sets)
                .ok_or("formal input transport work overflow")?,
        )
        .ok_or("formal input epoch transport exceeds its work bound")?;
    let mut origins = original.clone();
    for &(recent, older) in &facts.allocation_history[from..to] {
        origins.remap(recent, older);
    }
    Ok(origins)
}
