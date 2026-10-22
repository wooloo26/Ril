//! Universal inputs are born at a particular original callable header. They
//! are assumptions about that header, never observations of concrete data.
use super::{EntryOrigin, InvocationContext};
use crate::hir::nodes::{self as h, HirProgram};
use crate::sema::{
    context::FrozenEnvironment,
    copy_contract::{CopyInvocation, CopyValueSnapshot},
    facts::{OriginKind, Permission, ScopeId},
    model::{BindingInfo, Callable, Constant, Mode, Value},
    source_types::{SourcePath, SourceSchema, SourceTypesError as Error, WorkLimit},
};
use ril_compiler_core::ids::TypeExprId;
use ril_syntax::ast::{self as a, ParameterMode, TypeExpr};
use std::{collections::BTreeSet, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignatureFormal {
    pub slot: u32,
    pub binding: usize,
}

#[derive(Debug, Clone)]
pub struct SignatureProbeSource {
    pub source: TypeExprId,
    pub header: Arc<TypeExpr>,
    pub path: Arc<Vec<SourcePath>>,
    pub environment: FrozenEnvironment,
    pub formals: Arc<Vec<SignatureFormal>>,
}

impl PartialEq for SignatureProbeSource {
    fn eq(&self, other: &Self) -> bool {
        self.source == other.source
            && self.environment.id() == other.environment.id()
            && self.path == other.path
            && self.formals == other.formals
    }
}
impl Eq for SignatureProbeSource {}

pub(crate) struct AuthenticatedSignatureInput<'a> {
    pub header: &'a TypeExpr,
    pub environment: &'a FrozenEnvironment,
    pub mode: ParameterMode,
    path: &'a [SourcePath],
    slot: usize,
    arity: usize,
}

impl AuthenticatedSignatureInput<'_> {
    pub(crate) fn parameter_schema(
        &self,
        root: &SourceSchema,
        work: &mut WorkLimit,
    ) -> Result<SourceSchema, Error> {
        parameter_schema(root, self.path, self.arity, self.slot, self.mode, work)
    }
}

fn parameter_schema(
    root: &SourceSchema,
    path: &[SourcePath],
    arity: usize,
    slot: usize,
    mode: ParameterMode,
    work: &mut WorkLimit,
) -> Result<SourceSchema, Error> {
    let callable = root.project_steps(path, work)?;
    let parameters = callable.callable_parameters(work)?;
    require(parameters.len() == arity)?;
    let (actual_mode, schema) = parameters.get(slot).ok_or(Error::MissingNode)?;
    require(*actual_mode == mode)?;
    Ok(schema.clone())
}

pub(super) struct SignatureInput<'a> {
    pub value: &'a Value,
    pub mode: ParameterMode,
    pub scope: Option<ScopeId>,
    pub context: InvocationContext,
}

fn require(condition: bool) -> Result<(), Error> {
    condition.then_some(()).ok_or(Error::Unresolved)
}

impl SignatureProbeSource {
    pub(crate) fn parameter_schema(
        &self,
        root: &SourceSchema,
        slot: usize,
        mode: ParameterMode,
        work: &mut WorkLimit,
    ) -> Result<SourceSchema, Error> {
        parameter_schema(root, &self.path, self.formals.len(), slot, mode, work)
    }
    pub(crate) fn validate_header(
        header: &TypeExpr,
        hir: &HirProgram,
        work: &mut WorkLimit,
    ) -> Result<(), Error> {
        let source = header.hir_id.ok_or(Error::MissingNode)?;
        hir.type_expression(source).ok_or(Error::MissingNode)?;
        // Admit the retained clone and the canonical pairing before either
        // traversal. The shared HIR visitor also checks every nested ID.
        for _ in 0..2 {
            let mut remaining = work.remaining();
            let admitted = crate::static_eval::charge_type_syntax_clone(header, &mut remaining);
            work.charge(work.remaining() - remaining)?;
            admitted.ok_or(Error::BudgetExceeded)?;
        }
        let mut original = header.clone();
        hir.validate_type_syntax(&mut original, source, h::HirLimits::default())
            .map_err(|error| match error {
                h::LowerError::Budget(_) => Error::BudgetExceeded,
                _ => Error::Unresolved,
            })
    }

    pub(super) fn validate(&self, hir: &HirProgram, work: &mut WorkLimit) -> Result<(), Error> {
        work.charge(1 + self.formals.len())?;
        require(!self.environment.is_poisoned() && self.header.hir_id == Some(self.source))?;
        Self::validate_header(&self.header, hir, work)?;
        work.charge(self.path.len())?;
        for step in self.path.iter() {
            match step {
                SourcePath::Field(label) => work.text(label)?,
                SourcePath::RecordRemainder(labels) => {
                    work.charge(labels.len())?;
                    for label in labels {
                        work.text(label)?;
                    }
                }
                _ => {}
            }
        }
        let mut unique = BTreeSet::new();
        for (position, formal) in self.formals.iter().enumerate() {
            require(formal.slot as usize == position && unique.insert(formal.binding))?;
        }
        Ok(())
    }

    pub(super) fn authenticate<'a>(
        &'a self,
        slot: usize,
        input: SignatureInput<'_>,
        hir: &HirProgram,
        bindings: &[BindingInfo],
        work: &mut WorkLimit,
    ) -> Result<AuthenticatedSignatureInput<'a>, Error> {
        self.validate(hir, work)?;
        let SignatureInput {
            value: input,
            mode,
            scope,
            context,
        } = input;
        universal_values(vec![input], None, work)?;
        let formal = self.formals.get(slot).ok_or(Error::MissingNode)?;
        let binding = bindings.get(formal.binding).ok_or(Error::MissingNode)?;
        require(
            formal.slot as usize == slot
                && context.owner.is_none()
                && input.sources == BTreeSet::from([formal.binding])
                && binding.parameter
                && binding.pattern.is_none()
                && binding.birth.is_none()
                && Some(binding.owner) == scope
                && binding.context == context
                && binding.forwarded.is_empty()
                && binding.typing_environment.id() == self.environment.id()
                && !binding.typing_environment.is_poisoned()
                && binding.mode
                    == if mode == ParameterMode::Read {
                        a::BindingMode::Let
                    } else {
                        a::BindingMode::LetMut
                    }
                && binding.value.origins == input.origins
                && binding.value.ty == input.ty
                && binding.value.permission == input.permission
                && (mode != ParameterMode::Read || input.permission == Permission::Read),
        )?;
        match (
            &input.source_type_witness,
            &binding.value.source_type_witness,
        ) {
            (None, None) => {}
            (Some(actual), Some(original)) => require(
                actual.validate_closed() && original.validate_closed() && actual == original,
            )?,
            _ => return Err(Error::Unresolved),
        }
        Ok(AuthenticatedSignatureInput {
            header: &self.header,
            environment: &self.environment,
            mode,
            path: &self.path,
            slot,
            arity: self.formals.len(),
        })
    }
}

pub(crate) fn signature_assumption<'a>(
    call: &'a CopyInvocation,
    slot: usize,
    hir: &HirProgram,
    bindings: &[BindingInfo],
    epoch_limit: usize,
    work: &mut WorkLimit,
) -> Result<AuthenticatedSignatureInput<'a>, Error> {
    let EntryOrigin::SignatureProbe(source) = &call.entry.origin else {
        return Err(Error::Unresolved);
    };
    require(
        call.source_event.is_none()
            && !call.declaration_probe
            && call.caller_owner.is_none()
            && call.entry.caller_context.owner == call.caller_owner
            && call.entry.allocation_epoch <= epoch_limit
            && call.entry.arguments.len() == source.formals.len(),
    )?;
    let (mode, input) = call.entry.arguments.get(slot).ok_or(Error::MissingNode)?;
    let mode = match mode {
        Mode::Read => ParameterMode::Read,
        Mode::Write => ParameterMode::Mut,
        Mode::Retain => ParameterMode::SharedMut,
    };
    let authenticated = source.authenticate(
        slot,
        SignatureInput {
            value: &input.value,
            mode,
            scope: call.caller_activation,
            context: call.entry.caller_context,
        },
        hir,
        bindings,
        work,
    )?;
    universal_graph(input, work)?;
    Ok(authenticated)
}

pub(crate) fn closure_signature_assumption<'a>(
    call: &'a crate::sema::effect_identity::ClosureInvocation,
    slot: usize,
    hir: &HirProgram,
    bindings: &[BindingInfo],
    epoch_limit: usize,
    work: &mut WorkLimit,
) -> Result<AuthenticatedSignatureInput<'a>, Error> {
    let EntryOrigin::SignatureProbe(source) = &call.entry.origin else {
        return Err(Error::Unresolved);
    };
    require(
        call.probe
            && call.source_event.is_none()
            && call.caller_owner.is_none()
            && call.entry.caller_context.owner == call.caller_owner
            && call.entry.allocation_epoch <= epoch_limit
            && call.entry.arguments.len() == source.formals.len(),
    )?;
    let (mode, input, _) = call.entry.arguments.get(slot).ok_or(Error::MissingNode)?;
    source.authenticate(
        slot,
        SignatureInput {
            value: input,
            mode: *mode,
            scope: Some(call.caller_activation),
            context: call.entry.caller_context,
        },
        hir,
        bindings,
        work,
    )
}

pub(super) fn requires_signature_origin(
    input: &Value,
    scope: Option<ScopeId>,
    context: InvocationContext,
    bindings: &[BindingInfo],
    work: &mut WorkLimit,
) -> Result<bool, Error> {
    work.charge(1 + input.sources.len())?;
    if context.owner.is_some() {
        return Ok(false);
    }
    for &source in &input.sources {
        let binding = bindings.get(source).ok_or(Error::MissingNode)?;
        if binding.parameter
            && binding.pattern.is_none()
            && binding.birth.is_none()
            && Some(binding.owner) == scope
            && binding.context == context
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn universal_graph(input: &CopyValueSnapshot, work: &mut WorkLimit) -> Result<(), Error> {
    work.charge(1 + input.nodes.len() + input.relations.len())?;
    require(!input.relations.iter().any(|(left, right, relation)| {
        left != right
            && (relation.equal == crate::sema::relations::Condition::TRUE
                || relation.disjoint == crate::sema::relations::Condition::TRUE)
    }))?;
    let nodes: BTreeSet<_> = input.nodes.iter().map(|node| node.origin).collect();
    require(nodes.len() == input.nodes.len())?;
    let mut values = vec![&input.value];
    for node in &input.nodes {
        require(matches!(node.fact.kind, OriginKind::Formal(_)))?;
        work.charge(node.fields.len())?;
        let mut slots = BTreeSet::new();
        require(node.fact.fields.len() == node.fields.len())?;
        for (slot, value) in &node.fields {
            require(
                slots.insert(slot) && node.fact.fields.get(slot) == Some(&value.origins.nodes),
            )?;
            values.push(value);
        }
    }
    universal_values(values, Some(&nodes), work)
}

fn universal_values(
    mut values: Vec<&Value>,
    nodes: Option<&BTreeSet<crate::sema::facts::NodeId>>,
    work: &mut WorkLimit,
) -> Result<(), Error> {
    while let Some(value) = values.pop() {
        work.charge(
            6 + value.variant_witnesses.len() + value.origins.nodes.len() + value.callables.len(),
        )?;
        require(
            nodes.is_none_or(|nodes| value.origins.nodes.is_subset(nodes))
                && (value.constant.is_none()
                    || value.constant == Some(Constant::Unit)
                        && value.ty == crate::sema::model::Ty::Unit)
                && !value.construction
                && !value.marker
                && !value.retention_result
                && value.option_tag.is_none()
                && value.result_tag.is_none()
                && value.variant_tag.is_none()
                && value.static_coordinate.is_none()
                && value.scoped.is_empty()
                && value
                    .callables
                    .iter()
                    .all(|callable| matches!(callable, Callable::Symbolic(..))),
        )?;
        values.extend(
            [
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .map(Box::as_ref),
        );
        values.extend(value.variant_witnesses.values().map(Box::as_ref));
    }
    Ok(())
}
