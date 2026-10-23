//! Values held across later evaluation must follow allocation-site recency.
//! Each wrapper belongs to one Checker's monotonically growing move history.
//! It must not be transferred between checkers or reused with a rolled-back log.
use crate::numeric_literals::NumberType;
use crate::sema::{
    application_effect::OccurrenceIdentity,
    context::{FrozenEnvId, FrozenEnvironment},
    effect_identity::InvocationContext,
    facts::NodeId,
    model::{Callable, CallableReturnBound, Value},
    numeric_selection::{NumericBirth, NumericResolution},
    source_reception::Construction,
    source_types::{
        LiveSourceTypes, SourceScalar, SourceSchema, SourceTypesError, SourceView, WorkLimit,
    },
    source_types_ref::SourceTypesRef,
};
use ril_compiler_core::ids::{NumericHoleId, TypeExprId};
use std::sync::{Arc, OnceLock};

#[path = "evaluated_current.rs"]
mod current;
pub(crate) use current::{CurrentValueStep, catalog_callable_bound, projected_value, read_handle};

pub(crate) type CheckedSource = Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SourceRef {
    pub(crate) view: SourceView,
    pub(crate) original: Option<TypeExprId>,
}

impl SourceRef {
    pub(crate) fn intern(
        schema: &SourceSchema,
        environment: FrozenEnvironment,
        types: &mut LiveSourceTypes,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        Ok(Self {
            view: types.intern_schema(schema, environment, work)?,
            original: schema.original(),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CapturedSource {
    Known(SourceRef),
    Unknown(FrozenEnvId),
}

#[derive(Clone, Debug)]
pub(crate) struct ResolvedSource {
    pub(crate) schema: Option<SourceSchema>,
    pub(crate) environment: FrozenEnvironment,
}

impl ResolvedSource {
    pub(crate) fn into_known(self) -> Option<(SourceSchema, FrozenEnvironment)> {
        self.schema.map(|schema| (schema, self.environment))
    }
}

impl CapturedSource {
    fn resolve(
        self,
        types: SourceTypesRef<'_>,
        work: &mut WorkLimit,
    ) -> Result<ResolvedSource, SourceTypesError> {
        match self {
            Self::Known(source) => {
                let (schema, environment) =
                    types.view_schema(source.view, source.original, work)?;
                Ok(ResolvedSource {
                    schema: Some(schema),
                    environment,
                })
            }
            Self::Unknown(id) => Ok(ResolvedSource {
                schema: None,
                environment: types.environment(id, work)?,
            }),
        }
    }
}

pub(crate) fn numeric_source_scalar(number: NumberType) -> SourceScalar {
    match number {
        NumberType::Int => SourceScalar::Int,
        NumberType::I8 => SourceScalar::I8,
        NumberType::I16 => SourceScalar::I16,
        NumberType::I32 => SourceScalar::I32,
        NumberType::I64 => SourceScalar::I64,
        NumberType::U8 => SourceScalar::U8,
        NumberType::U16 => SourceScalar::U16,
        NumberType::U32 => SourceScalar::U32,
        NumberType::U64 => SourceScalar::U64,
        NumberType::BigInt => SourceScalar::BigInt,
        NumberType::F32 => SourceScalar::F32,
        NumberType::F64 => SourceScalar::F64,
    }
}

fn opaque_construction() -> &'static Construction {
    static OPAQUE: std::sync::OnceLock<Construction> = std::sync::OnceLock::new();
    OPAQUE.get_or_init(|| Construction::Opaque)
}

/// Read-only birth coordinates stay coupled to the captured Source basis.
/// Deref exposes these coordinates without permitting callers to restamp them.
#[derive(Debug)]
pub struct EvaluationBirth {
    pub(crate) observation: Option<usize>,
    pub(crate) allocation_epoch: usize,
    pub(crate) identity: Option<OccurrenceIdentity>,
    pub(crate) birth_context: Option<InvocationContext>,
    pub(crate) environment: Option<FrozenEnvId>,
    source: OnceLock<SourceCapture>,
}

#[derive(Clone, Debug)]
enum SourceCapture {
    Captured(Arc<BirthSource>),
    NumericPending(Arc<NumericSourceBasis>),
}

#[derive(Debug)]
struct BirthSource {
    result: Result<CapturedSource, SourceTypesError>,
    fresh: Option<Arc<Construction>>,
}

#[derive(Debug)]
struct NumericSourceBasis {
    hole: NumericHoleId,
    birth: NumericBirth,
    environment: FrozenEnvId,
    fresh: Option<Arc<Construction>>,
}

#[derive(Debug)]
pub(crate) struct NumericSourceDerivation {
    basis: Arc<NumericSourceBasis>,
    resolution: Arc<NumericResolution>,
    source: SourceRef,
}

#[derive(Clone, Debug)]
enum CurrentSource {
    Birth,
    Numeric(Arc<NumericSourceDerivation>),
    Derived(Arc<CurrentValueDerivation>),
    Pending,
    Failed(SourceTypesError),
}

#[derive(Debug)]
struct CurrentValueDerivation {
    input: Arc<EvaluatedValue>,
    step: CurrentValueStep,
    source: SourceRef,
}

/// Public observations never grant a mutable interface to the birth receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvaluationBirthCoordinates {
    pub observation: Option<usize>,
    pub allocation_epoch: usize,
    pub identity: Option<OccurrenceIdentity>,
    pub context: Option<InvocationContext>,
    pub environment: Option<FrozenEnvId>,
}

/// Borrow the complete capture state for independent checking and Core export.
/// Unknown retains its actual environment; a failed capture is never unknown.
#[derive(Clone, Copy, Debug)]
pub(crate) enum SourceCaptureView<'a> {
    Uncaptured,
    Captured {
        result: Result<CapturedSource, &'a SourceTypesError>,
        fresh: Option<&'a Construction>,
    },
    NumericPending {
        hole: NumericHoleId,
        birth: &'a NumericBirth,
        environment: FrozenEnvId,
        fresh: Option<&'a Construction>,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum CurrentSourceView<'a> {
    Birth,
    Derived {
        input: &'a Arc<EvaluatedValue>,
        step: &'a CurrentValueStep,
        source: SourceRef,
    },
    Numeric {
        hole: NumericHoleId,
        birth: &'a NumericBirth,
        environment: FrozenEnvId,
        resolution: &'a Arc<NumericResolution>,
        source: SourceRef,
    },
    Pending,
    Failed(&'a SourceTypesError),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PacketEvidenceView<'a> {
    pub(crate) birth: EvaluationBirthCoordinates,
    pub(crate) current_epoch: usize,
    pub(crate) capture: SourceCaptureView<'a>,
    pub(crate) current: CurrentSourceView<'a>,
    pub(crate) source_valid: bool,
}

#[derive(Clone, Debug)]
pub struct EvaluatedValue {
    pub(crate) value: Value,
    recency: usize,
    pub(crate) source_valid: bool,
    birth: Arc<EvaluationBirth>,
    current_source: CurrentSource,
}

/// The physical arena owns one immutable packet. Cloning an observation only
/// shares that packet; later views must explicitly pay for a derived value.
#[derive(Debug, Clone)]
pub struct PhysicalValue {
    packet: Arc<EvaluatedValue>,
}

impl PhysicalValue {
    pub fn packet(&self) -> &Arc<EvaluatedValue> {
        &self.packet
    }

    pub fn value(&self) -> &Value {
        self.packet.value()
    }

    pub(crate) fn from_packet(packet: Arc<EvaluatedValue>) -> Self {
        Self { packet }
    }

    #[cfg(test)]
    pub(crate) fn unobserved_fixture(value: Value, epoch: usize) -> Self {
        Self::from_packet(Arc::new(EvaluatedValue::unobserved(value, epoch, false)))
    }

    /// Fault injection keeps the old claim deliberately intact so independent
    /// validation must detect the changed payload, rather than a poison flag.
    #[cfg(test)]
    pub(crate) fn corrupt_value(
        &mut self,
        work: &mut usize,
    ) -> Result<&mut Value, SourceTypesError> {
        let copy = self.packet.try_clone(work)?;
        *work = work
            .checked_sub(1)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        self.packet = Arc::new(copy);
        Ok(&mut Arc::get_mut(&mut self.packet)
            .expect("new model packet")
            .value)
    }
}

impl std::ops::Deref for PhysicalValue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.value()
    }
}

impl PartialEq for PhysicalValue {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl PartialEq<Value> for PhysicalValue {
    fn eq(&self, other: &Value) -> bool {
        self.value() == other
    }
}

impl std::ops::Deref for EvaluatedValue {
    type Target = EvaluationBirth;

    fn deref(&self) -> &Self::Target {
        &self.birth
    }
}

impl EvaluatedValue {
    pub fn current_epoch(&self) -> usize {
        self.recency
    }

    pub fn birth_coordinates(&self) -> EvaluationBirthCoordinates {
        EvaluationBirthCoordinates {
            observation: self.observation,
            allocation_epoch: self.allocation_epoch,
            identity: self.identity,
            context: self.birth_context,
            environment: self.environment,
        }
    }

    pub(crate) fn evidence_view(&self) -> PacketEvidenceView<'_> {
        let capture = match self.birth.source.get() {
            None => SourceCaptureView::Uncaptured,
            Some(SourceCapture::Captured(basis)) => SourceCaptureView::Captured {
                result: basis.result.as_ref().copied(),
                fresh: basis.fresh.as_deref(),
            },
            Some(SourceCapture::NumericPending(basis)) => SourceCaptureView::NumericPending {
                hole: basis.hole,
                birth: &basis.birth,
                environment: basis.environment,
                fresh: basis.fresh.as_deref(),
            },
        };
        let current = match &self.current_source {
            CurrentSource::Birth => CurrentSourceView::Birth,
            CurrentSource::Numeric(derived) => CurrentSourceView::Numeric {
                hole: derived.basis.hole,
                birth: &derived.basis.birth,
                environment: derived.basis.environment,
                resolution: &derived.resolution,
                source: derived.source,
            },
            CurrentSource::Derived(derived) => CurrentSourceView::Derived {
                input: &derived.input,
                step: &derived.step,
                source: derived.source,
            },
            CurrentSource::Pending => CurrentSourceView::Pending,
            CurrentSource::Failed(error) => CurrentSourceView::Failed(error),
        };
        PacketEvidenceView {
            birth: self.birth_coordinates(),
            current_epoch: self.current_epoch(),
            capture,
            current,
            source_valid: self.source_valid,
        }
    }

    pub(crate) fn preflight_source_capture(&self) -> Result<(), SourceTypesError> {
        if self.birth.source.get().is_some() {
            return Err(SourceTypesError::AlreadyDefined);
        }
        if !matches!(self.current_source, CurrentSource::Birth) {
            return Err(SourceTypesError::SourceViewPending);
        }
        Ok(())
    }
    /// Capture is single-assignment. Neither mutation nor a failed capture can
    /// replace the original schema, environment, construction or birth identity.
    pub(crate) fn capture_birth_source(
        &mut self,
        result: Result<CapturedSource, SourceTypesError>,
        fresh: Option<Arc<Construction>>,
    ) -> Result<(), SourceTypesError> {
        self.preflight_source_capture()?;
        let invalid_environment = matches!(result, Ok(CapturedSource::Unknown(environment))
            if self.observation.is_some() && self.environment != Some(environment));
        let result = if invalid_environment {
            Err(SourceTypesError::Unresolved)
        } else {
            result
        };
        self.birth
            .source
            .set(SourceCapture::Captured(Arc::new(BirthSource {
                result,
                fresh,
            })))
            .map_err(|_| SourceTypesError::AlreadyDefined)?;
        if invalid_environment {
            Err(SourceTypesError::Unresolved)
        } else {
            Ok(())
        }
    }

    #[cfg(test)]
    pub(crate) fn has_captured_source(&self) -> bool {
        self.birth.source.get().is_some()
    }

    pub(crate) fn capture_numeric_birth_source(
        &mut self,
        hole: NumericHoleId,
        birth: NumericBirth,
        environment: FrozenEnvId,
        fresh: Option<Arc<Construction>>,
    ) -> Result<(), SourceTypesError> {
        self.preflight_source_capture()?;
        if self.observation.is_none()
            || self.identity.is_none()
            || self.birth_context.is_none()
            || self.environment != Some(environment)
            || self.value.ty != super::model::Ty::NumericHole(hole)
            || birth.allocation_epoch > self.allocation_epoch
        {
            self.birth
                .source
                .set(SourceCapture::Captured(Arc::new(BirthSource {
                    result: Err(SourceTypesError::Unresolved),
                    fresh,
                })))
                .map_err(|_| SourceTypesError::AlreadyDefined)?;
            return Err(SourceTypesError::Unresolved);
        }
        self.birth
            .source
            .set(SourceCapture::NumericPending(Arc::new(
                NumericSourceBasis {
                    hole,
                    birth,
                    environment,
                    fresh,
                },
            )))
            .map_err(|_| SourceTypesError::AlreadyDefined)
    }

    pub(crate) fn apply_numeric_resolution(
        &mut self,
        hole: NumericHoleId,
        resolution: Arc<NumericResolution>,
        types: &mut LiveSourceTypes,
        work: &mut usize,
    ) -> Result<(), SourceTypesError> {
        let basis = match self.birth.source.get() {
            Some(SourceCapture::NumericPending(basis)) if basis.hole == hole => basis,
            Some(SourceCapture::Captured(basis)) => {
                return Err(match &basis.result {
                    Err(error) => error.clone(),
                    _ => SourceTypesError::Unresolved,
                });
            }
            None => return Err(SourceTypesError::SourceNotCaptured),
            _ => return Err(SourceTypesError::Unresolved),
        };
        match &self.current_source {
            CurrentSource::Birth => {}
            CurrentSource::Numeric(previous) => {
                if !Arc::ptr_eq(&previous.basis, basis)
                    || !Arc::ptr_eq(&previous.resolution, &resolution)
                {
                    return Err(SourceTypesError::Unresolved);
                }
            }
            CurrentSource::Derived(_) => return Err(SourceTypesError::SourceViewPending),
            CurrentSource::Pending => return Err(SourceTypesError::SourceViewPending),
            CurrentSource::Failed(error) => return Err(error.clone()),
        }
        *work = work
            .checked_sub(3)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        if !resolution.matches_value(&self.value, work)? {
            return Err(SourceTypesError::Unresolved);
        }
        let mut graph_work = WorkLimit::new(*work);
        let source = (|| {
            let environment = types.environment(basis.environment, &mut graph_work)?;
            let schema = SourceSchema::scalar(
                numeric_source_scalar(resolution.number_type),
                None,
                &mut graph_work,
            )?;
            SourceRef::intern(&schema, environment, types, &mut graph_work)
        })();
        *work = graph_work.remaining();
        let source = source?;
        self.current_source = CurrentSource::Numeric(Arc::new(NumericSourceDerivation {
            basis: basis.clone(),
            resolution,
            source,
        }));
        Ok(())
    }

    pub(crate) fn numeric_source_derivation(
        &self,
    ) -> Option<(NumericHoleId, &NumericBirth, &Arc<NumericResolution>)> {
        match &self.current_source {
            CurrentSource::Numeric(derived) => Some((
                derived.basis.hole,
                &derived.basis.birth,
                &derived.resolution,
            )),
            _ => None,
        }
    }

    pub(crate) fn shares_birth(&self, other: &Self) -> bool {
        self.observation == other.observation
            && self.identity == other.identity
            && self.birth_context == other.birth_context
            && self.environment == other.environment
            && self.allocation_epoch == other.allocation_epoch
            && Arc::ptr_eq(&self.birth, &other.birth)
    }

    /// A numeric selection is the original input's explicit pending choice.
    /// An ordinary receiving change still consumes only its birth schema.
    pub(crate) fn input_source(
        &self,
        types: SourceTypesRef<'_>,
        work: &mut WorkLimit,
    ) -> Result<ResolvedSource, SourceTypesError> {
        match self.current_source {
            CurrentSource::Numeric(_) | CurrentSource::Derived(_) | CurrentSource::Failed(_) => {
                self.current_source(types, work)
            }
            _ => self.birth_source(types, work),
        }
    }

    /// Only an authenticated original-input role may consume this basis. The
    /// current Value may have undergone a separately pending receiving change.
    pub(crate) fn birth_source(
        &self,
        types: SourceTypesRef<'_>,
        work: &mut WorkLimit,
    ) -> Result<ResolvedSource, SourceTypesError> {
        match self.birth.source.get() {
            None => Err(SourceTypesError::SourceNotCaptured),
            Some(SourceCapture::Captured(basis)) => basis
                .result
                .as_ref()
                .map_err(Clone::clone)?
                .resolve(types, work),
            Some(SourceCapture::NumericPending(_)) => Err(SourceTypesError::SourceViewPending),
        }
    }

    pub(crate) fn current_source(
        &self,
        types: SourceTypesRef<'_>,
        work: &mut WorkLimit,
    ) -> Result<ResolvedSource, SourceTypesError> {
        match &self.current_source {
            CurrentSource::Birth => self.birth_source(types, work),
            CurrentSource::Numeric(derived) => {
                CapturedSource::Known(derived.source).resolve(types, work)
            }
            CurrentSource::Derived(derived) => {
                CapturedSource::Known(derived.source).resolve(types, work)
            }
            CurrentSource::Pending => Err(SourceTypesError::SourceViewPending),
            CurrentSource::Failed(error) => Err(error.clone()),
        }
    }

    pub(crate) fn fresh(&self) -> &Construction {
        match self.birth.source.get() {
            Some(SourceCapture::Captured(basis)) => match basis.fresh.as_deref() {
                Some(fresh) => fresh,
                None => opaque_construction(),
            },
            Some(SourceCapture::NumericPending(basis)) => match basis.fresh.as_deref() {
                Some(fresh) => fresh,
                None => opaque_construction(),
            },
            None => opaque_construction(),
        }
    }

    pub fn value(&self) -> &Value {
        &self.value
    }

    pub(crate) fn invalidate_current_source(&mut self) {
        if !matches!(self.current_source, CurrentSource::Failed(_)) {
            self.current_source = CurrentSource::Pending;
        }
    }

    pub(crate) fn fail_current_source(&mut self, error: SourceTypesError) {
        if !matches!(self.current_source, CurrentSource::Failed(_)) {
            self.current_source = CurrentSource::Failed(error);
        }
        self.source_valid = false;
    }

    pub(crate) fn try_clone(&self, work: &mut usize) -> Result<Self, SourceTypesError> {
        charge_value_clone(&self.value, work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
        *work = work
            .checked_sub(3)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        Ok(self.clone())
    }
    /// Call after evaluation: the new result already belongs to this epoch.
    pub(crate) fn new(value: Value, recency: usize) -> Self {
        Self {
            value,
            recency,
            source_valid: true,
            birth: Arc::new(EvaluationBirth {
                observation: None,
                allocation_epoch: recency,
                identity: None,
                birth_context: None,
                environment: None,
                source: OnceLock::new(),
            }),
            current_source: CurrentSource::Birth,
        }
    }

    pub(crate) fn unobserved(value: Value, recency: usize, source_valid: bool) -> Self {
        let mut packet = Self::new(value, recency);
        packet.source_valid = source_valid;
        packet
    }

    pub(crate) fn observed(
        value: Value,
        observation: usize,
        record: &crate::sema::application_effect::EvaluationRecord,
    ) -> Self {
        Self {
            value,
            recency: record.allocation_epoch,
            source_valid: true,
            birth: Arc::new(EvaluationBirth {
                observation: Some(observation),
                allocation_epoch: record.allocation_epoch,
                identity: record.identity,
                birth_context: Some(record.context),
                environment: record.environment,
                source: OnceLock::new(),
            }),
            current_source: CurrentSource::Birth,
        }
    }

    pub(crate) fn transport(&mut self, moves: &[(NodeId, NodeId)]) {
        for &(recent, older) in &moves[self.recency..] {
            self.value.remap_origins(recent, older);
        }
        self.recency = moves.len();
    }

    pub(crate) fn current_mut(&mut self, moves: &[(NodeId, NodeId)]) -> &mut Value {
        // Only node references change. Permission, loan/root participants,
        // copy/Result/condition/numeric identities retain their existing duties.
        // remap_value_origins also transports every nested payload witness.
        self.transport(moves);
        // A mutable interface may install another type or callable view. Only
        // an independently checked selection/reception may give it a new Source.
        self.invalidate_current_source();
        &mut self.value
    }
    pub(crate) fn current(&mut self, moves: &[(NodeId, NodeId)]) -> Value {
        self.transport(moves);
        self.value.clone()
    }
    pub(crate) fn current_read(
        &self,
        moves: &[(NodeId, NodeId)],
        work: &mut usize,
    ) -> Result<Value, SourceTypesError> {
        transport_value_at(&self.value, moves, self.recency, moves.len(), work)
    }
    pub(crate) fn transport_checked(
        &mut self,
        moves: &[(NodeId, NodeId)],
        work: &mut usize,
    ) -> Result<(), SourceTypesError> {
        let count = moves
            .len()
            .checked_sub(self.recency)
            .ok_or(SourceTypesError::Unresolved)?;
        if count != 0 {
            charge_transport(&self.value, count, work, 0)
                .ok_or(SourceTypesError::BudgetExceeded)?;
        }
        self.transport(moves);
        Ok(())
    }
    pub(crate) fn into_current(mut self, moves: &[(NodeId, NodeId)]) -> Value {
        self.transport(moves);
        self.value
    }
}

/// Export uses the same admission as an owned value clone, without allocating
/// an intermediate clone or turning equality into an allocation allowance.
pub(crate) fn charge_value_export(value: &Value, work: &mut usize) -> Result<(), SourceTypesError> {
    charge_value_clone(value, work, 0).ok_or(SourceTypesError::BudgetExceeded)
}

fn charge_value_clone(value: &Value, work: &mut usize, depth: usize) -> Option<()> {
    {
        if depth > 128 {
            return None;
        }
        *work = work.checked_sub(1)?;
        super::clone_work::ty(work, &value.ty, depth)?;
        for count in [
            value.numeric.uses.len(),
            value.numeric.selections.len(),
            value.pending_copies.len(),
            value.origins.nodes.len(),
            value.origins.choices.len(),
            value.callables.len(),
            value.callable_bounds.len(),
            value.callable_returns.len(),
            value.participants.len(),
            value.sources.len(),
            value.callback_parameters.len(),
            value.scoped.len(),
            value.pending_inference.len(),
            value.results.len(),
            value.outer_results.len(),
            value.must_outer_results.len(),
            value.must_results.len(),
            value.condition_inspections.when_true.len(),
            value.condition_inspections.when_false.len(),
            value.condition_inspections.versions.len(),
            value.condition_inspections.evaluations.len(),
            value.variant_witnesses.len(),
        ] {
            *work = work.checked_sub(count)?;
        }
        for guard in [
            &value.condition_inspections.channel_when_true,
            &value.condition_inspections.channel_when_false,
        ] {
            *work = work.checked_sub(guard.terms.len())?;
            for term in &guard.terms {
                *work = work.checked_sub(term.len())?;
            }
        }
        for branches in value.origins.choices.values() {
            *work = work.checked_sub(branches.len())?;
            for branch in branches {
                *work = work.checked_sub(branch.len())?;
            }
        }
        for callable in &value.callables {
            match callable {
                Callable::Builtin(name) | Callable::Constructor(name) => {
                    *work = work.checked_sub(name.len())?;
                }
                Callable::Symbolic(_, path) => {
                    for label in path {
                        *work = work.checked_sub(1 + label.len())?;
                    }
                }
                _ => {}
            }
        }
        for bound in &value.callable_bounds {
            for annotation in &bound.annotations {
                *work = work.checked_sub(1 + annotation.text.len())?;
            }
        }
        if let Some(parameters) = &value.signature {
            for parameter in parameters {
                crate::static_eval::charge_parameter_syntax_clone(parameter, work)?;
            }
        }
        for identity in &value.pending_inference {
            *work = work.checked_sub(identity.len())?;
        }
        if let Some(crate::sema::model::StaticCoordinate::Label(label)) = &value.static_coordinate {
            *work = work.checked_sub(label.len())?;
        }
        if let Some(tag) = &value.variant_tag {
            *work = work.checked_sub(tag.len())?;
        }
        for (tag, payload) in &value.variant_witnesses {
            *work = work.checked_sub(tag.len())?;
            charge_value_clone(payload, work, depth + 1)?;
        }
        for payload in [
            &value.option_payload,
            &value.result_payload,
            &value.result_success,
            &value.result_error,
            &value.variant_payload,
        ]
        .into_iter()
        .flatten()
        {
            charge_value_clone(payload, work, depth + 1)?;
        }
        Some(())
    }
}

pub(crate) fn same_birth_value(
    left: &Value,
    right: &Value,
    work: &mut usize,
) -> Result<bool, SourceTypesError> {
    charge_value_clone(left, work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    charge_value_clone(right, work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    if !shared_value_equality(left, right, work, 0)? {
        return Ok(false);
    }
    Ok(left == right)
}

/// Source forwarding checks the complete public callable/type interface.
/// Storage authority and duties remain inputs of their own transfer checks.
pub(crate) fn same_source_public_view(
    left: &Value,
    right: &Value,
    work: &mut usize,
) -> Result<bool, SourceTypesError> {
    charge_value_export(left, work)?;
    charge_value_export(right, work)?;
    Ok(left.cause == right.cause
        && left.ty == right.ty
        && left.source_type_witness == right.source_type_witness
        && left.callables == right.callables
        && left.callable_bounds == right.callable_bounds
        && left.callable_returns == right.callable_returns
        && left.signature == right.signature)
}

/// A bounded diagnostic after full equality rejects a receipt. Field labels
/// reveal the missing transfer without dumping program values or large graphs.
pub(crate) fn value_difference(
    expected: &Value,
    actual: &Value,
    work: &mut usize,
) -> Result<&'static str, SourceTypesError> {
    charge_value_export(expected, work)?;
    charge_value_export(actual, work)?;
    macro_rules! fields {
        ($($field:ident),* $(,)?) => {$(
            if expected.$field != actual.$field { return Ok(stringify!($field)); }
        )*};
    }
    fields!(
        numeric,
        pending_copies,
        ty,
        source_type_witness,
        origins,
        permission,
        publication,
        constant,
        static_coordinate,
        unsuffixed_numeric,
        literal_number,
        callables,
        callable_bounds,
        callable_returns,
        signature,
        participants,
        sources,
        callback_parameters,
        scoped,
        stable,
        marker,
        retention_result,
        through_return,
        readonly_spread,
        temporary,
        requires_inference,
        pending_inference,
        construction,
        internal_aliases,
        mutable_environment,
        observer_environment,
        cause,
        results,
        outer_results,
        must_outer_results,
        must_results,
        condition_inspections,
        result_payload,
        result_success,
        result_error,
        result_tag,
        option_payload,
        option_tag,
        option_identity,
        abnormal,
        variant_tag,
        variant_payload,
        variant_witnesses
    );
    Ok("shared Source syntax or frozen callable environment")
}

fn shared_value_equality(
    left: &Value,
    right: &Value,
    work: &mut usize,
    depth: usize,
) -> Result<bool, SourceTypesError> {
    *work = work
        .checked_sub(1)
        .ok_or(SourceTypesError::BudgetExceeded)?;
    if depth > 128 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    // Abstract fixed-point equality intentionally forgets physical Boolean
    // evaluation identities. A birth receipt must preserve them exactly,
    // including guards with no channel-dependent literals and poison state.
    if left.condition_inspections.evaluations != right.condition_inspections.evaluations
        || left.condition_inspections.channel_when_true
            != right.condition_inspections.channel_when_true
        || left.condition_inspections.channel_when_false
            != right.condition_inspections.channel_when_false
    {
        return Ok(false);
    }
    if let (Some(left), Some(right)) = (&left.source_type_witness, &right.source_type_witness)
        && !Arc::ptr_eq(left, right)
    {
        if left.syntax.hir_id != right.syntax.hir_id {
            return Ok(false);
        }
        *work = work
            .checked_sub(left.key.len())
            .and_then(|n| n.checked_sub(right.key.len()))
            .ok_or(SourceTypesError::BudgetExceeded)?;
        crate::static_eval::charge_type_syntax_clone(&left.syntax, work)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        crate::static_eval::charge_type_syntax_clone(&right.syntax, work)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        if left.syntax != right.syntax {
            return Ok(false);
        }
    }
    if left.callable_bounds.len() != right.callable_bounds.len()
        || left.callable_returns.len() != right.callable_returns.len()
    {
        return Ok(false);
    }
    for (a, b) in left.callable_bounds.iter().zip(&right.callable_bounds) {
        if a.typing_environment.id() != b.typing_environment.id() {
            return Ok(false);
        }
    }
    for (a, b) in left.callable_returns.iter().zip(&right.callable_returns) {
        if !return_bound_equality(a, b, work, depth + 1)? {
            return Ok(false);
        }
    }
    for (a, b) in [
        &left.option_payload,
        &left.result_payload,
        &left.result_success,
        &left.result_error,
        &left.variant_payload,
    ]
    .into_iter()
    .zip([
        &right.option_payload,
        &right.result_payload,
        &right.result_success,
        &right.result_error,
        &right.variant_payload,
    ]) {
        if let (Some(a), Some(b)) = (a, b)
            && !shared_value_equality(a, b, work, depth + 1)?
        {
            return Ok(false);
        }
    }
    if left.variant_witnesses.len() != right.variant_witnesses.len() {
        return Ok(false);
    }
    for ((a_key, a), (b_key, b)) in left.variant_witnesses.iter().zip(&right.variant_witnesses) {
        if a_key != b_key || !shared_value_equality(a, b, work, depth + 1)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn return_bound_equality(
    left: &Arc<CallableReturnBound>,
    right: &Arc<CallableReturnBound>,
    work: &mut usize,
    depth: usize,
) -> Result<bool, SourceTypesError> {
    *work = work
        .checked_sub(1)
        .ok_or(SourceTypesError::BudgetExceeded)?;
    if Arc::ptr_eq(left, right) {
        return Ok(true);
    }
    if depth > 128 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    if left.typing_environment.id() != right.typing_environment.id()
        || left.predecessors.len() != right.predecessors.len()
        || left.syntax.hir_id != right.syntax.hir_id
    {
        return Ok(false);
    }
    for bound in [left, right] {
        super::clone_work::ty(work, &bound.target, depth)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        crate::static_eval::charge_type_syntax_clone(&bound.syntax, work)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        *work = work
            .checked_sub(bound.callables.len())
            .ok_or(SourceTypesError::BudgetExceeded)?;
        for callable in &bound.callables {
            match callable {
                Callable::Builtin(name) | Callable::Constructor(name) => {
                    *work = work
                        .checked_sub(name.len())
                        .ok_or(SourceTypesError::BudgetExceeded)?;
                }
                Callable::Symbolic(_, path) => {
                    for label in path {
                        *work = work
                            .checked_sub(1 + label.len())
                            .ok_or(SourceTypesError::BudgetExceeded)?;
                    }
                }
                _ => {}
            }
        }
    }
    for (a, b) in left.predecessors.iter().zip(&right.predecessors) {
        if !return_bound_equality(a, b, work, depth + 1)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn charge_transport(value: &Value, epochs: usize, work: &mut usize, depth: usize) -> Option<()> {
    if epochs == 0 {
        return Some(());
    }
    if depth > 128 {
        return None;
    }
    // Pay before traversing each collection, rather than first scanning an
    // arbitrarily large alternatives table to compute a final bulk charge.
    *work =
        work.checked_sub(epochs.checked_mul(1usize.checked_add(value.origins.nodes.len())?)?)?;
    *work = work.checked_sub(epochs.checked_mul(value.origins.choices.len())?)?;
    for branches in value.origins.choices.values() {
        *work = work.checked_sub(epochs.checked_mul(branches.len())?)?;
        for branch in branches {
            *work = work.checked_sub(epochs.checked_mul(branch.len())?)?;
        }
    }
    for payload in [
        &value.option_payload,
        &value.result_payload,
        &value.result_success,
        &value.result_error,
        &value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values())
    {
        charge_transport(payload, epochs, work, depth + 1)?;
    }
    Some(())
}

/// Pure bounded transport between explicit epochs. This does not mint an
/// observation, a Source schema, or authority from the copied runtime shape.
pub(crate) fn transport_value_at(
    value: &Value,
    moves: &[(NodeId, NodeId)],
    from: usize,
    to: usize,
    work: &mut usize,
) -> Result<Value, SourceTypesError> {
    let history = moves.get(from..to).ok_or(SourceTypesError::Unresolved)?;
    charge_value_clone(value, work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    if !history.is_empty() {
        charge_transport(value, history.len(), work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    }
    let mut value = value.clone();
    for &(recent, older) in history {
        value.remap_origins(recent, older);
    }
    Ok(value)
}

/// Prove that a held value has only followed the actual allocation history.
/// This is required before a numeric choice changes any current projection.
pub(crate) fn same_transported_birth(
    birth: &Value,
    birth_epoch: usize,
    current: &Value,
    current_epoch: usize,
    moves: &[(NodeId, NodeId)],
    work: &mut usize,
) -> Result<bool, SourceTypesError> {
    let expected = transport_value_at(birth, moves, birth_epoch, current_epoch, work)?;
    same_birth_value(&expected, current, work)
}

#[cfg(test)]
mod packet_tests {
    use super::*;
    use crate::sema::{
        application_effect::EvaluationRecord,
        effect_identity::ArgumentKey,
        facts::{LoanId, Participant, Permission, ScopeId},
        model::{SourceTypeWitness, Ty},
        source_types::{LiveSourceTypes, WorkLimit},
    };
    use ril_compiler_core::ids::{
        ActivationEpochId, EvaluationOccurrenceId, ExprId, OptionalTagId,
    };
    use ril_compiler_core::{
        diagnostic::CauseId,
        source::{FileId, Span},
    };
    use std::collections::BTreeSet;

    fn unknown_source(types: &mut LiveSourceTypes) -> CapturedSource {
        CapturedSource::Unknown(
            types
                .intern_environment(FrozenEnvironment::default(), &mut WorkLimit::new(4096))
                .unwrap(),
        )
    }

    fn resolve_birth(packet: &EvaluatedValue, types: &LiveSourceTypes) -> CheckedSource {
        packet
            .birth_source(SourceTypesRef::Live(types), &mut WorkLimit::new(4096))
            .map(ResolvedSource::into_known)
    }

    fn resolve_current(packet: &EvaluatedValue, types: &LiveSourceTypes) -> CheckedSource {
        packet
            .current_source(SourceTypesRef::Live(types), &mut WorkLimit::new(4096))
            .map(ResolvedSource::into_known)
    }

    fn packet(types: &mut LiveSourceTypes) -> EvaluatedValue {
        let mut value = Value::reference(
            Ty::Optional(Box::new(Ty::Int("int".into()))),
            NodeId(1),
            CauseId(0),
        );
        value.permission = Permission::Read;
        value.participants.insert(Participant::Loan(LoanId(3)));
        value.results.insert(7);
        value.outer_results.insert(7);
        value.option_identity = Some(OptionalTagId(9));
        value.option_payload = Some(Box::new(Value::reference(
            Ty::Int("int".into()),
            NodeId(1),
            CauseId(0),
        )));
        let context = crate::sema::effect_identity::InvocationContext {
            owner: None,
            invocation: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        };
        let environment = FrozenEnvironment::default();
        let environment_id = types
            .intern_environment(environment.clone(), &mut WorkLimit::new(4096))
            .unwrap();
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: Some(OccurrenceIdentity {
                source: ExprId(4),
                activation: ActivationEpochId(5),
            }),
            scope: ScopeId(0),
            context,
            allocation_epoch: 0,
            environment: Some(environment_id),
        };
        let mut packet = EvaluatedValue::observed(value, 2, &record);
        packet
            .capture_birth_source(
                Ok(CapturedSource::Known(
                    SourceRef::intern(
                        &SourceSchema::import(
                            &ArgumentKey::Name {
                                name: "Option".into(),
                                arguments: vec![ArgumentKey::Name {
                                    name: "int".into(),
                                    arguments: vec![],
                                }],
                            },
                            None,
                            &mut WorkLimit::new(256),
                        )
                        .unwrap(),
                        environment,
                        types,
                        &mut WorkLimit::new(4096),
                    )
                    .unwrap(),
                )),
                None,
            )
            .unwrap();
        packet
    }

    #[test]
    fn entry_heap_views_use_current_epochs_and_keep_one_shared_root() {
        use crate::sema::{application_effect::EntryArgument, copy_contract::CopyHeapSnapshot};
        let mut types = LiveSourceTypes::default();
        let original = Arc::new(packet(&mut types));
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let mut argument = EntryArgument {
            mode: ril_syntax::ast::ParameterMode::Read,
            packet: original.clone(),
            span,
            heap: Some(Arc::new(CopyHeapSnapshot {
                allocation_epoch: 0,
                nodes: vec![],
                relations: vec![],
            })),
        };
        assert!(Arc::ptr_eq(&argument.packet, &original));
        assert!(matches!(
            argument.snapshot_view(&mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut work = WorkLimit::new(1);
        let view = argument.snapshot_view(&mut work).unwrap();
        assert_eq!(work.remaining(), 0);
        assert!(std::ptr::eq(view.value, original.value()));

        let moves = [(NodeId(1), NodeId(6)), (NodeId(6), NodeId(8))];
        for (epoch, expected_origin) in [(1, NodeId(6)), (2, NodeId(8))] {
            let previous = argument.packet.clone();
            let mut transported = previous.try_clone(&mut 4096).unwrap();
            transported
                .transport_checked(&moves[..epoch], &mut 4096)
                .unwrap();
            argument.packet = Arc::new(transported);
            assert!(argument.packet.shares_birth(&original));
            assert!(matches!(
                argument.snapshot_view(&mut WorkLimit::new(1)),
                Err(SourceTypesError::Unresolved)
            ));
            argument.heap = Some(Arc::new(CopyHeapSnapshot {
                allocation_epoch: epoch,
                nodes: vec![],
                relations: vec![],
            }));
            let view = argument.snapshot_view(&mut WorkLimit::new(1)).unwrap();
            assert!(std::ptr::eq(view.value, argument.packet.value()));
            assert_eq!(view.value.origins.nodes, BTreeSet::from([expected_origin]));
            assert_eq!(
                view.value.option_payload.as_ref().unwrap().origins.nodes,
                BTreeSet::from([expected_origin])
            );
            assert_eq!(
                argument.packet.birth_coordinates(),
                original.birth_coordinates()
            );
            assert_eq!(argument.packet.current_epoch(), epoch);
            assert_eq!(argument.packet.value.results, original.value.results);
            assert_eq!(
                argument.packet.value.participants,
                original.value.participants
            );
            assert_eq!(previous.current_epoch(), epoch - 1);
        }
        argument.heap = None;
        assert!(matches!(
            argument.snapshot_view(&mut WorkLimit::new(1)),
            Err(SourceTypesError::MissingNode)
        ));
        assert_eq!(original.current_epoch(), 0);
        assert_eq!(original.value.origins.nodes, BTreeSet::from([NodeId(1)]));
    }

    #[test]
    fn packet_evidence_keeps_capture_failure_unknown_and_current_failure_distinct() {
        let mut types = LiveSourceTypes::default();
        let known = packet(&mut types);
        let evidence = known.evidence_view();
        assert_eq!(evidence.birth, known.birth_coordinates());
        assert_eq!(evidence.current_epoch, 0);
        assert!(matches!(
            evidence.capture,
            SourceCaptureView::Captured {
                result: Ok(CapturedSource::Known(_)),
                fresh: None,
            }
        ));
        assert!(matches!(evidence.current, CurrentSourceView::Birth));

        let mut unknown = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        assert!(matches!(
            unknown.evidence_view().capture,
            SourceCaptureView::Uncaptured
        ));
        let captured = unknown_source(&mut types);
        unknown.capture_birth_source(Ok(captured), None).unwrap();
        assert!(
            matches!(unknown.evidence_view().capture, SourceCaptureView::Captured {
            result: Ok(actual), fresh: None,
        } if actual == captured)
        );
        unknown.invalidate_current_source();
        assert!(matches!(
            unknown.evidence_view().current,
            CurrentSourceView::Pending
        ));
        unknown.fail_current_source(SourceTypesError::BudgetExceeded);
        let evidence = unknown.evidence_view();
        assert!(matches!(
            evidence.current,
            CurrentSourceView::Failed(SourceTypesError::BudgetExceeded)
        ));
        assert!(!evidence.source_valid);
        assert!(matches!(evidence.capture, SourceCaptureView::Captured {
            result: Ok(actual), ..
        } if actual == captured));

        let mut failed = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        failed
            .capture_birth_source(Err(SourceTypesError::ForeignIdentity), None)
            .unwrap();
        assert!(matches!(
            failed.evidence_view().capture,
            SourceCaptureView::Captured {
                result: Err(SourceTypesError::ForeignIdentity),
                fresh: None,
            }
        ));
        assert!(matches!(
            failed.evidence_view().current,
            CurrentSourceView::Birth
        ));
    }

    #[test]
    fn packet_evidence_retains_numeric_birth_and_the_complete_resolution() {
        let mut types = LiveSourceTypes::default();
        let mut packet = pending_numeric_packet(&mut types);
        let birth = packet.birth_coordinates();
        let environment = match packet.evidence_view().capture {
            SourceCaptureView::NumericPending {
                hole,
                birth: numeric_birth,
                environment,
                fresh: Some(Construction::Opaque),
            } => {
                assert_eq!(hole, NumericHoleId(3));
                assert_eq!(Some(numeric_birth.occurrence), birth.identity);
                environment
            }
            other => panic!("missing numeric basis: {other:?}"),
        };
        let resolution = numeric_resolution();
        resolution.apply(&mut packet.value, &mut 4096).unwrap();
        packet
            .apply_numeric_resolution(NumericHoleId(3), resolution.clone(), &mut types, &mut 4096)
            .unwrap();
        let evidence = packet.evidence_view();
        assert_eq!(evidence.birth, birth);
        assert!(
            matches!(evidence.capture, SourceCaptureView::NumericPending {
            environment: actual, ..
        } if actual == environment)
        );
        match evidence.current {
            CurrentSourceView::Numeric {
                hole,
                birth: numeric_birth,
                environment: actual,
                resolution: actual_resolution,
                source,
            } => {
                assert_eq!(hole, NumericHoleId(3));
                assert_eq!(actual, environment);
                assert_eq!(Some(numeric_birth.occurrence), birth.identity);
                assert!(Arc::ptr_eq(actual_resolution, &resolution));
                assert_eq!(source.view.environment, environment);
            }
            other => panic!("missing complete numeric derivation: {other:?}"),
        }
    }

    #[test]
    fn physical_birth_environment_is_independent_of_source_and_rejects_relabelling() {
        let mut types = LiveSourceTypes::default();
        let original = packet(&mut types);
        let physical = original.environment.unwrap();
        let declaration = FrozenEnvironment::default();
        let declared = types
            .intern_environment(declaration.clone(), &mut WorkLimit::new(4096))
            .unwrap();
        assert_ne!(physical, declared);
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: original.identity,
            scope: ScopeId(0),
            context: original.birth_context.unwrap(),
            allocation_epoch: 0,
            environment: Some(physical),
        };
        let schema =
            SourceSchema::scalar(SourceScalar::Int, None, &mut WorkLimit::new(4096)).unwrap();
        let source =
            SourceRef::intern(&schema, declaration, &mut types, &mut WorkLimit::new(4096)).unwrap();
        let mut known = EvaluatedValue::observed(
            Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
            2,
            &record,
        );
        known
            .capture_birth_source(Ok(CapturedSource::Known(source)), None)
            .unwrap();
        assert_eq!(known.birth_coordinates().environment, Some(physical));
        assert_eq!(
            resolve_birth(&known, &types).unwrap().unwrap().1.id(),
            declared
        );
        let mut changed = known.try_clone(&mut 4096).unwrap();
        assert!(changed.shares_birth(&known));
        assert!(Arc::get_mut(&mut changed.birth).is_none());
        let changed_record = EvaluationRecord {
            environment: Some(declared),
            ..record.clone()
        };
        changed = EvaluatedValue::observed(known.value.clone(), 2, &changed_record);
        changed
            .capture_birth_source(Ok(CapturedSource::Known(source)), None)
            .unwrap();
        assert!(!changed.shares_birth(&known));

        let mut unknown =
            EvaluatedValue::observed(Value::scalar(Ty::Unknown, None, CauseId(0)), 2, &record);
        assert_eq!(
            unknown.capture_birth_source(Ok(CapturedSource::Unknown(declared)), None),
            Err(SourceTypesError::Unresolved)
        );
        assert!(unknown.has_captured_source());
        assert_eq!(
            resolve_birth(&unknown, &types).unwrap_err(),
            SourceTypesError::Unresolved
        );
        assert_eq!(
            unknown.capture_birth_source(Ok(CapturedSource::Unknown(physical)), None),
            Err(SourceTypesError::AlreadyDefined)
        );
        assert_eq!(unknown.birth_coordinates().environment, Some(physical));
    }

    #[test]
    fn an_early_packet_clone_observes_the_same_single_capture_completion() {
        let mut types = LiveSourceTypes::default();
        let completed = packet(&mut types);
        let Some(SourceCapture::Captured(source)) = completed.birth.source.get() else {
            panic!("known fixture")
        };
        let source = *source.result.as_ref().unwrap();
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: completed.identity,
            scope: ScopeId(0),
            context: completed.birth_context.unwrap(),
            allocation_epoch: 0,
            environment: completed.environment,
        };
        let mut original = EvaluatedValue::observed(completed.value.clone(), 2, &record);
        let mut early = original.try_clone(&mut 4096).unwrap();
        assert!(original.shares_birth(&early));
        for _ in 0..8 {
            assert_eq!(
                resolve_birth(&early, &types).unwrap_err(),
                SourceTypesError::SourceNotCaptured
            );
        }
        original.capture_birth_source(Ok(source), None).unwrap();
        assert!(early.has_captured_source());
        assert_eq!(
            resolve_birth(&early, &types).unwrap().unwrap().0.root_id(),
            resolve_birth(&original, &types)
                .unwrap()
                .unwrap()
                .0
                .root_id()
        );
        assert_eq!(
            early.capture_birth_source(Ok(source), None),
            Err(SourceTypesError::AlreadyDefined)
        );
        early
            .transport_checked(&[(NodeId(1), NodeId(6))], &mut 4096)
            .unwrap();
        assert!(early.shares_birth(&original));
        assert_eq!(original.current_epoch(), 0);
        assert_eq!(original.value.origins.nodes, BTreeSet::from([NodeId(1)]));
    }

    #[test]
    fn a_derived_read_keeps_its_original_birth_and_source() {
        let mut types = LiveSourceTypes::default();
        let mut original = packet(&mut types);
        original.value.permission = Permission::Write;
        let original = Arc::new(original);
        let mut value = transport_value_at(original.value(), &[], 0, 0, &mut 4096).unwrap();
        read_handle(&mut value);
        let derived = EvaluatedValue::derive_current(
            original.clone(),
            CurrentValueStep::ReadHandle,
            value,
            &mut types,
            &mut 4096,
        )
        .unwrap();
        assert!(derived.shares_birth(&original));
        assert_eq!(original.value.permission, Permission::Write);
        assert_eq!(derived.value.permission, Permission::Read);
        assert_eq!(derived.value.participants, original.value.participants);
        assert_eq!(
            derived.value.option_identity,
            original.value.option_identity
        );
        assert_eq!(derived.value.results, original.value.results);
        let CurrentSourceView::Derived { input, step, .. } = derived.evidence_view().current else {
            panic!("a read must retain its derivation")
        };
        assert!(Arc::ptr_eq(input, &original));
        assert!(matches!(step, CurrentValueStep::ReadHandle));
        let birth = resolve_birth(&original, &types).unwrap().unwrap();
        let current = resolve_current(&derived, &types).unwrap().unwrap();
        assert_eq!(birth.1.id(), current.1.id());
        assert!(
            birth
                .0
                .equivalent(&current.0, &mut WorkLimit::new(4096))
                .unwrap()
        );
    }

    #[test]
    fn an_unknown_capture_cannot_replace_an_independently_known_input() {
        let source = ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::entry-packets-after-allocating-default",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        crate::sema::application_effect::validate(facts).unwrap();
        let (call, slot) =
            facts
                .copy_invocations
                .iter()
                .enumerate()
                .find_map(|(call, invocation)| {
                    matches!(
                        invocation.entry.origin,
                        crate::sema::application_effect::EntryOrigin::Application(_)
                    )
                    .then(|| {
                        invocation.entry.arguments.iter().enumerate().find_map(
                            |(slot, argument)| {
                                (matches!(
                                    argument.packet.evidence_view().current,
                                    CurrentSourceView::Birth
                                ) && matches!(
                                    argument.packet.evidence_view().capture,
                                    SourceCaptureView::Captured {
                                        result: Ok(CapturedSource::Known(_)),
                                        ..
                                    }
                                ))
                                .then_some((call, slot))
                            },
                        )
                    })
                    .flatten()
                })
                .expect("an actual argument has a known Source");
        let original = &facts.copy_invocations[call].entry.arguments[slot].packet;
        let observation = original.observation.unwrap();
        let physical = facts.expressions[observation].value.packet();
        let record = &facts.evaluations[observation];
        let Some(SourceCapture::Captured(basis)) = physical.birth.source.get() else {
            unreachable!()
        };
        let mut downgraded = EvaluatedValue::observed(
            transport_value_at(physical.value(), &[], 0, 0, &mut 1_000_000).unwrap(),
            observation,
            record,
        );
        downgraded
            .capture_birth_source(
                Ok(CapturedSource::Unknown(record.environment.unwrap())),
                basis.fresh.clone(),
            )
            .unwrap();
        let downgraded = Arc::new(downgraded);
        let mut entry_view = original.try_clone(&mut 1_000_000).unwrap();
        entry_view.birth = downgraded.birth.clone();
        assert!(entry_view.shares_birth(&downgraded));
        assert!(same_birth_value(entry_view.value(), original.value(), &mut 1_000_000).unwrap());
        let mut changed = facts.clone();
        changed.expressions[observation].value = PhysicalValue::from_packet(downgraded);
        Arc::make_mut(&mut changed.copy_invocations[call].entry.arguments)[slot].packet =
            Arc::new(entry_view);
        let (_, message) = crate::sema::application_effect::validate(&changed).unwrap_err();
        assert!(
            message.contains("unknown packet contradicts an independently known Source"),
            "{message}"
        );
    }

    #[test]
    fn a_derived_view_cannot_restart_a_failed_or_unfilled_capture() {
        let mut types = LiveSourceTypes::default();
        let mut original = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        let early = Arc::new(original.try_clone(&mut 4096).unwrap());
        let result = EvaluatedValue::derive_current(
            early.clone(),
            CurrentValueStep::ReadHandle,
            original.value.clone(),
            &mut types,
            &mut 4096,
        );
        assert_eq!(result.unwrap_err(), SourceTypesError::SourceNotCaptured);
        assert!(!early.has_captured_source());
        original
            .capture_birth_source(Err(SourceTypesError::BudgetExceeded), None)
            .unwrap();
        let result = EvaluatedValue::derive_current(
            early.clone(),
            CurrentValueStep::ReadHandle,
            original.value.clone(),
            &mut types,
            &mut 4096,
        );
        assert_eq!(result.unwrap_err(), SourceTypesError::BudgetExceeded);
        assert!(early.shares_birth(&original));
        assert_eq!(
            resolve_birth(&early, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
    }

    #[test]
    fn capture_failure_completes_every_birth_handle_and_cannot_be_retried() {
        let mut types = LiveSourceTypes::default();
        let mut original = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        let mut early = original.try_clone(&mut 4096).unwrap();
        original
            .capture_birth_source(Err(SourceTypesError::BudgetExceeded), None)
            .unwrap();
        assert_eq!(
            resolve_birth(&early, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(
            early.capture_birth_source(Ok(unknown_source(&mut types)), None),
            Err(SourceTypesError::AlreadyDefined)
        );
        assert_eq!(
            resolve_birth(&original, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert!(early.shares_birth(&original));
    }

    #[test]
    fn numeric_capture_completion_and_current_resolution_share_the_original_basis() {
        let mut types = LiveSourceTypes::default();
        let template = pending_numeric_packet(&mut types);
        let Some(SourceCapture::NumericPending(basis)) = template.birth.source.get() else {
            panic!("numeric fixture")
        };
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: template.identity,
            scope: ScopeId(0),
            context: template.birth_context.unwrap(),
            allocation_epoch: 0,
            environment: template.environment,
        };
        let mut original = EvaluatedValue::observed(template.value.clone(), 2, &record);
        let mut early = original.try_clone(&mut 4096).unwrap();
        original
            .capture_numeric_birth_source(
                basis.hole,
                basis.birth,
                basis.environment,
                basis.fresh.clone(),
            )
            .unwrap();
        assert_eq!(
            resolve_birth(&early, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );
        let resolution = numeric_resolution();
        resolution.apply(&mut early.value, &mut 4096).unwrap();
        early
            .apply_numeric_resolution(basis.hole, resolution.clone(), &mut types, &mut 4096)
            .unwrap();
        assert!(early.shares_birth(&original));
        assert_eq!(original.value.ty, Ty::NumericHole(basis.hole));
        assert_eq!(
            resolve_birth(&original, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );
        let Some(SourceCapture::NumericPending(actual_basis)) = original.birth.source.get() else {
            panic!("shared pending basis")
        };
        let CurrentSource::Numeric(derived) = &early.current_source else {
            panic!("derived numeric source")
        };
        assert!(Arc::ptr_eq(actual_basis, &derived.basis));
        assert!(Arc::ptr_eq(&resolution, &derived.resolution));
    }

    #[test]
    fn value_export_admission_is_prepaid_and_leaves_the_original_packet_unchanged() {
        let mut types = LiveSourceTypes::default();
        let packet = packet(&mut types);
        let original = packet.try_clone(&mut 4096).unwrap();
        let mut allowance = 4096;
        charge_value_export(packet.value(), &mut allowance).unwrap();
        let cost = 4096 - allowance;
        assert!(cost > 1);
        for units in 0..=cost {
            let mut work = units;
            let result = charge_value_export(packet.value(), &mut work);
            if units < cost {
                assert_eq!(result, Err(SourceTypesError::BudgetExceeded));
            } else {
                assert_eq!(result, Ok(()));
                assert_eq!(work, 0);
            }
            assert_eq!(
                same_birth_value(packet.value(), original.value(), &mut 4096),
                Ok(true)
            );
            assert_eq!(packet.birth_coordinates(), original.birth_coordinates());
            assert!(packet.shares_birth(&original));
        }
    }

    #[test]
    fn pure_epoch_transport_preserves_birth_source_permissions_and_duties() {
        let mut types = LiveSourceTypes::default();
        let mut packet = packet(&mut types);
        let (schema, environment) = resolve_birth(&packet, &types).unwrap().unwrap();
        let (root, environment) = (schema.root_id(), environment.id());
        let moves = [(NodeId(1), NodeId(6))];
        packet.transport_checked(&moves, &mut 4096).unwrap();
        let value = packet.current_read(&moves, &mut 4096).unwrap();
        assert_eq!(value.origins.nodes, BTreeSet::from([NodeId(6)]));
        assert_eq!(
            value.option_payload.as_ref().unwrap().origins.nodes,
            value.origins.nodes
        );
        assert_eq!(value.permission, Permission::Read);
        assert_eq!(
            value.participants,
            BTreeSet::from([Participant::Loan(LoanId(3))])
        );
        assert_eq!(value.results, BTreeSet::from([7]));
        assert_eq!(value.outer_results, BTreeSet::from([7]));
        assert_eq!(value.option_identity, Some(OptionalTagId(9)));
        assert_eq!(packet.allocation_epoch, 0);
        assert_eq!(packet.observation, Some(2));
        let (schema, frozen) = resolve_birth(&packet, &types).unwrap().unwrap();
        assert_eq!(schema.root_id(), root);
        assert_eq!(frozen.id(), environment);
    }

    #[test]
    fn mutable_current_view_cannot_reuse_the_immutable_input_schema() {
        let mut types = LiveSourceTypes::default();
        let original = Arc::new(packet(&mut types));
        let mut current = original.try_clone(&mut 4096).unwrap();
        current.current_mut(&[]).ty = Ty::Str;
        assert!(matches!(
            resolve_current(&current, &types),
            Err(SourceTypesError::SourceViewPending)
        ));
        assert!(matches!(resolve_birth(&current, &types), Ok(Some(_))));
        assert!(matches!(resolve_current(&original, &types), Ok(Some(_))));
        let (birth, _) = resolve_birth(&current, &types).unwrap().unwrap();
        let (original_birth, _) = resolve_birth(&original, &types).unwrap().unwrap();
        assert_eq!(birth.root_id(), original_birth.root_id());
        assert_eq!(current.observation, original.observation);
        assert_eq!(current.allocation_epoch, original.allocation_epoch);
    }

    #[test]
    fn packet_clone_admits_owned_values_without_conflating_unknown_and_error() {
        let mut types = LiveSourceTypes::default();
        let mut packet = packet(&mut types);
        assert!(matches!(
            packet.current_read(&[], &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            packet.transport_checked(&[(NodeId(1), NodeId(6))], &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert_eq!(packet.value.origins.nodes, BTreeSet::from([NodeId(1)]));
        assert!(matches!(
            packet.try_clone(&mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut unknown = EvaluatedValue::new(packet.value.clone(), 0);
        unknown
            .capture_birth_source(Ok(unknown_source(&mut types)), None)
            .unwrap();
        assert!(matches!(
            unknown
                .try_clone(&mut 4096)
                .unwrap()
                .birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
                .map(ResolvedSource::into_known),
            Ok(None)
        ));
        let mut failed = EvaluatedValue::new(packet.value.clone(), 0);
        failed
            .capture_birth_source(Err(SourceTypesError::MissingNode), None)
            .unwrap();
        assert!(matches!(
            failed
                .try_clone(&mut 4096)
                .unwrap()
                .birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
                .map(ResolvedSource::into_known),
            Err(SourceTypesError::MissingNode)
        ));
    }

    #[test]
    fn uncaptured_source_is_distinct_from_unknown_and_attempted_failure() {
        let mut types = LiveSourceTypes::default();
        let mut uncaptured = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        assert!(!uncaptured.has_captured_source());
        assert_eq!(
            resolve_current(&uncaptured, &types).unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        let cloned = uncaptured.try_clone(&mut 100).unwrap();
        assert!(!cloned.has_captured_source());
        assert_eq!(
            resolve_birth(&cloned, &types).unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        uncaptured
            .capture_birth_source(Ok(unknown_source(&mut types)), None)
            .unwrap();
        assert!(uncaptured.has_captured_source());
        assert!(matches!(resolve_current(&uncaptured, &types), Ok(None)));

        for error in [
            SourceTypesError::MissingNode,
            SourceTypesError::BudgetExceeded,
            SourceTypesError::SourceNotCaptured,
        ] {
            let mut attempted = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
            attempted
                .capture_birth_source(Err(error.clone()), None)
                .unwrap();
            assert!(attempted.has_captured_source());
            assert_eq!(resolve_birth(&attempted, &types).unwrap_err(), error);
        }
    }

    #[test]
    fn birth_source_cannot_be_replaced_or_installed_after_a_current_view_change() {
        let mut types = LiveSourceTypes::default();
        let mut packet = packet(&mut types);
        let root = resolve_birth(&packet, &types).unwrap().unwrap().0.root_id();
        packet.invalidate_current_source();
        assert_eq!(
            packet.capture_birth_source(Ok(unknown_source(&mut types)), None),
            Err(SourceTypesError::AlreadyDefined)
        );
        assert_eq!(
            resolve_birth(&packet, &types).unwrap().unwrap().0.root_id(),
            root
        );
        assert_eq!(
            resolve_current(&packet, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );

        let mut pending = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        pending.current_mut(&[]).ty = Ty::Str;
        assert_eq!(
            pending.capture_birth_source(Ok(unknown_source(&mut types)), None),
            Err(SourceTypesError::SourceViewPending)
        );
        assert!(!pending.has_captured_source());
        assert_eq!(
            resolve_birth(&pending, &types).unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        assert_eq!(
            resolve_current(&pending, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );
    }

    #[test]
    fn failed_current_view_keeps_the_original_source_and_duties() {
        let mut types = LiveSourceTypes::default();
        let mut packet = packet(&mut types);
        let environment = resolve_birth(&packet, &types).unwrap().unwrap().1.id();
        packet.fail_current_source(SourceTypesError::BudgetExceeded);
        packet.value.ty = Ty::Unknown;
        assert_eq!(
            resolve_current(&packet, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(
            resolve_birth(&packet, &types).unwrap().unwrap().1.id(),
            environment
        );
        assert_eq!(packet.value.results, BTreeSet::from([7]));
        packet.current_mut(&[]).ty = Ty::Str;
        packet.invalidate_current_source();
        packet.fail_current_source(SourceTypesError::Unresolved);
        assert_eq!(
            resolve_current(&packet, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(packet.value.results, BTreeSet::from([7]));
        assert_eq!(
            resolve_birth(&packet, &types).unwrap().unwrap().1.id(),
            environment
        );
        packet
            .transport_checked(&[(NodeId(1), NodeId(6))], &mut 4096)
            .unwrap();
        assert_eq!(
            resolve_current(&packet, &types).unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(
            resolve_birth(&packet, &types).unwrap().unwrap().1.id(),
            environment
        );
    }

    fn pending_numeric_packet(types: &mut LiveSourceTypes) -> EvaluatedValue {
        let original = packet(types);
        let mut value = Value::scalar(Ty::NumericHole(NumericHoleId(3)), None, CauseId(0));
        value
            .numeric
            .uses
            .insert(ril_compiler_core::ids::NumericUseId(1));
        value.results.insert(7);
        value.outer_results.insert(7);
        value.participants.insert(Participant::Loan(LoanId(3)));
        let environment = types
            .intern_environment(FrozenEnvironment::default(), &mut WorkLimit::new(4096))
            .unwrap();
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: original.identity,
            scope: ScopeId(0),
            context: original.birth_context.unwrap(),
            allocation_epoch: 0,
            environment: Some(environment),
        };
        let mut packet = EvaluatedValue::observed(value, 2, &record);
        packet
            .capture_numeric_birth_source(
                NumericHoleId(3),
                NumericBirth {
                    occurrence: record.identity.unwrap(),
                    scope: record.scope,
                    context: record.context,
                    allocation_epoch: 0,
                },
                environment,
                Some(Arc::new(Construction::Opaque)),
            )
            .unwrap();
        packet
    }

    fn numeric_resolution() -> Arc<NumericResolution> {
        let encoded = crate::numeric_literals::ExactLiteral::integer(
            "16777217",
            false,
            crate::numeric_literals::ParseLimit { max_bytes: 64 },
        )
        .unwrap()
        .select(
            NumberType::F32,
            ril_compiler_core::target::TargetLayout::POINTER64,
        )
        .unwrap();
        Arc::new(NumericResolution {
            number_type: NumberType::F32,
            constant: None,
            encoded: Some(encoded),
            dependencies: crate::sema::numeric_selection::NumericDependencies {
                uses: BTreeSet::from([ril_compiler_core::ids::NumericUseId(1)]),
                selections: BTreeSet::from([ril_compiler_core::ids::NumericSelectionId(2)]),
            },
        })
    }

    #[test]
    fn numeric_source_keeps_pending_birth_and_all_non_numeric_duties() {
        let mut types = LiveSourceTypes::default();
        let mut packet = pending_numeric_packet(&mut types);
        let original = packet.try_clone(&mut 4096).unwrap();
        let resolution = numeric_resolution();
        resolution.apply(&mut packet.value, &mut 4096).unwrap();
        packet
            .apply_numeric_resolution(NumericHoleId(3), resolution.clone(), &mut types, &mut 4096)
            .unwrap();
        let (schema, environment) = resolve_current(&packet, &types).unwrap().unwrap();
        assert_eq!(
            schema.key().unwrap(),
            crate::sema::effect_identity::ArgumentKey::Name {
                name: "f32".into(),
                arguments: vec![],
            }
        );
        let environment = environment.id();
        assert!(packet.shares_birth(&original));
        assert_eq!(
            resolve_birth(&packet, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );
        assert_eq!(packet.value.results, original.value.results);
        assert_eq!(packet.value.outer_results, original.value.outer_results);
        assert_eq!(packet.value.participants, original.value.participants);
        assert_eq!(packet.value.permission, original.value.permission);
        assert_eq!(packet.allocation_epoch, original.allocation_epoch);
        assert_eq!(packet.identity, original.identity);
        let (_, _, retained) = packet.numeric_source_derivation().unwrap();
        assert!(Arc::ptr_eq(retained, &resolution));
        packet
            .transport_checked(&[(NodeId(1), NodeId(6))], &mut 4096)
            .unwrap();
        assert_eq!(
            resolve_current(&packet, &types).unwrap().unwrap().1.id(),
            environment
        );
        let cloned = packet.try_clone(&mut 4096).unwrap();
        assert_eq!(
            resolve_current(&cloned, &types).unwrap().unwrap().1.id(),
            environment
        );
        packet.invalidate_current_source();
        assert_eq!(
            resolve_current(&packet, &types).unwrap_err(),
            SourceTypesError::SourceViewPending
        );
    }

    #[test]
    fn numeric_admission_cannot_hide_changes_to_held_permissions_or_duties() {
        let mut types = LiveSourceTypes::default();
        let birth = packet(&mut types);
        let moves = [(NodeId(1), NodeId(6))];
        let mut held = birth.try_clone(&mut 4096).unwrap();
        held.transport_checked(&moves, &mut 4096).unwrap();
        assert_eq!(
            same_transported_birth(&birth.value, 0, &held.value, 1, &moves, &mut 4096),
            Ok(true)
        );
        let changes: [fn(&mut Value); 8] = [
            |value| value.permission = Permission::Write,
            |value| value.publication = crate::sema::facts::Publication::Immutable,
            |value| value.participants.clear(),
            |value| value.results.clear(),
            |value| value.outer_results.clear(),
            |value| value.marker = !value.marker,
            |value| {
                value
                    .condition_inspections
                    .evaluations
                    .insert(crate::sema::result_conditions::ConditionEvaluationId(99));
            },
            |value| value.condition_inspections.channel_when_true.incomplete = true,
        ];
        for change in changes {
            let mut changed = held.try_clone(&mut 4096).unwrap();
            change(&mut changed.value);
            assert_eq!(
                same_transported_birth(&birth.value, 0, &changed.value, 1, &moves, &mut 4096),
                Ok(false)
            );
        }
        assert!(matches!(
            same_transported_birth(&birth.value, 0, &held.value, 1, &moves, &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            same_transported_birth(&birth.value, 1, &held.value, 0, &moves, &mut 4096),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn numeric_source_cannot_replace_unknown_error_or_an_unrelated_pending_birth() {
        let mut types = LiveSourceTypes::default();
        let resolution = numeric_resolution();
        for outcome in [
            Ok(unknown_source(&mut types)),
            Err(SourceTypesError::MissingNode),
            Err(SourceTypesError::BudgetExceeded),
        ] {
            let mut packet = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
            packet.capture_birth_source(outcome, None).unwrap();
            resolution.apply(&mut packet.value, &mut 4096).unwrap();
            assert!(
                packet
                    .apply_numeric_resolution(
                        NumericHoleId(3),
                        resolution.clone(),
                        &mut types,
                        &mut 4096
                    )
                    .is_err()
            );
            assert!(packet.numeric_source_derivation().is_none());
        }
        let mut pending = pending_numeric_packet(&mut types);
        resolution.apply(&mut pending.value, &mut 4096).unwrap();
        assert_eq!(
            pending.apply_numeric_resolution(
                NumericHoleId(4),
                resolution.clone(),
                &mut types,
                &mut 4096
            ),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(
            pending.apply_numeric_resolution(
                NumericHoleId(3),
                resolution.clone(),
                &mut types,
                &mut 0
            ),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(pending.numeric_source_derivation().is_none());
        pending.value.numeric.selections.clear();
        assert_eq!(
            pending.apply_numeric_resolution(NumericHoleId(3), resolution, &mut types, &mut 4096),
            Err(SourceTypesError::Unresolved)
        );
    }

    #[test]
    fn source_coordinates_retain_original_identity_and_environment_when_frozen() {
        let mut types = LiveSourceTypes::default();
        let environment = FrozenEnvironment::default();
        let environment_id = environment.id();
        let original = Some(TypeExprId(73));
        let schema =
            SourceSchema::scalar(SourceScalar::I32, original, &mut WorkLimit::new(4096)).unwrap();
        let source =
            SourceRef::intern(&schema, environment, &mut types, &mut WorkLimit::new(4096)).unwrap();
        let mut packet =
            EvaluatedValue::new(Value::scalar(Ty::Int("i32".into()), None, CauseId(0)), 0);
        packet
            .capture_birth_source(Ok(CapturedSource::Known(source)), None)
            .unwrap();
        let live = packet
            .birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(live.schema.as_ref().unwrap().root_id(), source.view.ty);
        assert_eq!(live.schema.as_ref().unwrap().original(), original);
        assert_eq!(live.environment.id(), environment_id);
        let frozen = types.freeze();
        let retained = packet
            .birth_source(SourceTypesRef::Frozen(&frozen), &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(retained.schema.as_ref().unwrap().root_id(), source.view.ty);
        assert_eq!(retained.schema.as_ref().unwrap().original(), original);
        assert_eq!(retained.environment.id(), environment_id);
        assert!(matches!(
            packet.birth_source(SourceTypesRef::Frozen(&frozen), &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let foreign = LiveSourceTypes::default();
        assert!(
            packet
                .birth_source(SourceTypesRef::Live(&foreign), &mut WorkLimit::new(4096))
                .is_err()
        );
    }

    #[test]
    fn unknown_source_keeps_its_actual_environment_and_rejects_missing_coordinates() {
        let mut types = LiveSourceTypes::default();
        let environment = FrozenEnvironment::default();
        let environment_id = types
            .intern_environment(environment, &mut WorkLimit::new(4096))
            .unwrap();
        let mut packet = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        packet
            .capture_birth_source(Ok(CapturedSource::Unknown(environment_id)), None)
            .unwrap();
        let known_environment = packet
            .input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
            .unwrap();
        assert!(known_environment.schema.is_none());
        assert_eq!(known_environment.environment.id(), environment_id);
        let mut foreign = LiveSourceTypes::default();
        foreign
            .intern_environment(FrozenEnvironment::default(), &mut WorkLimit::new(4096))
            .unwrap();
        assert!(matches!(
            packet.input_source(SourceTypesRef::Live(&foreign), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        let missing_id = FrozenEnvironment::default().id();
        let mut missing = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        missing
            .capture_birth_source(Ok(CapturedSource::Unknown(missing_id)), None)
            .unwrap();
        assert!(matches!(
            missing.input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        assert!(matches!(
            types.intern_environment(FrozenEnvironment::poisoned(), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        let frozen = types.freeze();
        let retained = packet
            .input_source(SourceTypesRef::Frozen(&frozen), &mut WorkLimit::new(4096))
            .unwrap();
        assert!(retained.schema.is_none());
        assert_eq!(retained.environment.id(), environment_id);
    }

    #[test]
    fn equal_source_views_do_not_identify_independent_birth_receipts() {
        let mut types = LiveSourceTypes::default();
        let first = packet(&mut types);
        let Some(SourceCapture::Captured(basis)) = first.birth.source.get() else {
            panic!("fixture must retain its real captured source");
        };
        let source = *basis.result.as_ref().unwrap();
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(first.observation.unwrap() as u32),
            identity: first.identity,
            scope: ScopeId(0),
            context: first.birth_context.unwrap(),
            allocation_epoch: first.allocation_epoch,
            environment: first.environment,
        };
        let mut independent =
            EvaluatedValue::observed(first.value.clone(), first.observation.unwrap(), &record);
        // Even forged equal coordinates cannot turn another capture into the
        // original immutable receipt merely because its view is shared.
        assert_eq!(independent.birth_coordinates(), first.birth_coordinates());
        assert!(!first.shares_birth(&independent));
        independent.capture_birth_source(Ok(source), None).unwrap();
        assert!(!first.shares_birth(&independent));
        assert!(first.shares_birth(&first.try_clone(&mut 4096).unwrap()));
        let left = resolve_birth(&first, &types).unwrap().unwrap();
        let right = resolve_birth(&independent, &types).unwrap().unwrap();
        assert_eq!(left.0.root_id(), right.0.root_id());
        assert_eq!(left.1.id(), right.1.id());
    }

    #[test]
    fn numeric_source_resolution_requires_its_original_environment_registry() {
        let mut types = LiveSourceTypes::default();
        let mut packet = pending_numeric_packet(&mut types);
        let Some(SourceCapture::NumericPending(basis)) = packet.birth.source.get() else {
            panic!("fixture must retain its pending numeric basis");
        };
        let environment_id = basis.environment;
        let original = packet.try_clone(&mut 4096).unwrap();
        let resolution = numeric_resolution();
        resolution.apply(&mut packet.value, &mut 4096).unwrap();
        let mut foreign = LiveSourceTypes::default();
        assert!(matches!(
            packet.apply_numeric_resolution(
                NumericHoleId(3),
                resolution.clone(),
                &mut foreign,
                &mut 4096
            ),
            Err(SourceTypesError::MissingNode)
        ));
        assert!(packet.numeric_source_derivation().is_none());
        assert!(packet.shares_birth(&original));
        packet
            .apply_numeric_resolution(NumericHoleId(3), resolution, &mut types, &mut 4096)
            .unwrap();
        let selected = packet
            .current_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(selected.environment.id(), environment_id);
        assert_eq!(
            selected.schema.unwrap().key().unwrap(),
            ArgumentKey::Name {
                name: "f32".into(),
                arguments: vec![]
            }
        );
        assert!(packet.shares_birth(&original));
        assert!(matches!(
            packet.birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::SourceViewPending)
        ));
    }

    #[test]
    fn birth_equality_keeps_physical_boolean_receipts_in_every_payload() {
        use crate::sema::{
            channel_messages::{ChannelGuard, GuardLiteral},
            result_conditions::{ConditionEvaluationId, ConditionInspections},
        };
        let mut leaf = Value::scalar(Ty::Bool, None, CauseId(0));
        leaf.condition_inspections
            .evaluations
            .insert(ConditionEvaluationId(17));
        leaf.condition_inspections.channel_when_true =
            ChannelGuard::literal(GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(17),
                truth: true,
            });
        leaf.condition_inspections.channel_when_false =
            ChannelGuard::literal(GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(17),
                truth: false,
            });
        let changes: [fn(&mut ConditionInspections); 5] = [
            |evidence| evidence.evaluations.clear(),
            |evidence| evidence.evaluations = BTreeSet::from([ConditionEvaluationId(18)]),
            |evidence| {
                evidence.channel_when_true = ChannelGuard::literal(GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(18),
                    truth: true,
                })
            },
            |evidence| {
                evidence.channel_when_false = ChannelGuard::literal(GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(18),
                    truth: false,
                })
            },
            |evidence| evidence.channel_when_true.incomplete = true,
        ];
        for (change_index, change) in changes.into_iter().enumerate() {
            let mut changed = leaf.clone();
            change(&mut changed.condition_inspections);
            for slot in 0..7 {
                let wrap = |value: Value| {
                    let mut shell = Value::scalar(Ty::Unknown, None, CauseId(0));
                    match slot {
                        0 => return value,
                        1 => shell.option_payload = Some(Box::new(value)),
                        2 => shell.result_payload = Some(Box::new(value)),
                        3 => shell.result_success = Some(Box::new(value)),
                        4 => shell.result_error = Some(Box::new(value)),
                        5 => shell.variant_payload = Some(Box::new(value)),
                        _ => {
                            shell
                                .variant_witnesses
                                .insert("item".into(), Box::new(value));
                        }
                    }
                    shell
                };
                let original = wrap(leaf.clone());
                let changed = wrap(changed.clone());
                if change_index < 4 {
                    // Deliberately coarser fixed-point equality remains valid
                    // for its old clients, but cannot authenticate an emission.
                    assert_eq!(original, changed);
                }
                assert_eq!(same_birth_value(&original, &original, &mut 4096), Ok(true));
                assert_eq!(same_birth_value(&original, &changed, &mut 4096), Ok(false));
                assert!(matches!(
                    same_birth_value(&original, &changed, &mut 0),
                    Err(SourceTypesError::BudgetExceeded)
                ));
            }
        }
    }

    #[test]
    fn epoch_transport_admits_each_alternative_frontier_before_scanning_it() {
        let mut value = Value::reference(Ty::Named("Item".into()), NodeId(1), CauseId(0));
        value.origins.choices = (0..512)
            .map(|choice| (choice, vec![BTreeSet::from([NodeId(1)])]))
            .collect();
        let mut packet = EvaluatedValue::new(value, 0);
        let mut work = 2;
        assert!(matches!(
            packet.transport_checked(&[(NodeId(1), NodeId(6))], &mut work),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert_eq!(
            work, 0,
            "the root is paid before the alternatives frontier is inspected"
        );
        assert_eq!(packet.recency, 0);
        assert!(
            packet
                .value
                .origins
                .choices
                .values()
                .all(|branches| branches == &[BTreeSet::from([NodeId(1)])])
        );
    }

    #[test]
    fn explicit_epoch_transport_preserves_birth_and_intermediate_snapshots() {
        let mut types = LiveSourceTypes::default();
        let original = packet(&mut types);
        let moves = [(NodeId(1), NodeId(6)), (NodeId(6), NodeId(8))];
        let completion = transport_value_at(&original.value, &moves, 0, 1, &mut 4096).unwrap();
        let current = transport_value_at(&completion, &moves, 1, 2, &mut 4096).unwrap();
        let direct = transport_value_at(&original.value, &moves, 0, 2, &mut 4096).unwrap();
        assert_eq!(same_birth_value(&current, &direct, &mut 4096), Ok(true));
        assert_eq!(original.value.origins.nodes, BTreeSet::from([NodeId(1)]));
        assert_eq!(completion.origins.nodes, BTreeSet::from([NodeId(6)]));
        assert_eq!(current.origins.nodes, BTreeSet::from([NodeId(8)]));
        assert_eq!(original.allocation_epoch, 0);
        for (from, to) in [(2, 1), (0, 3)] {
            assert!(matches!(
                transport_value_at(&original.value, &moves, from, to, &mut 4096),
                Err(SourceTypesError::Unresolved)
            ));
        }
        assert!(matches!(
            transport_value_at(&original.value, &moves, 0, 2, &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn birth_equality_admits_nonshared_witness_keys_and_return_contracts() {
        let mut types = LiveSourceTypes::default();
        let packet = packet(&mut types);
        let mut left = packet.value.clone();
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let syntax = ril_syntax::ast::TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: ril_syntax::ast::TypeKind::Name {
                path: vec!["int".into()],
                arguments: vec![],
            },
        };
        let witness = SourceTypeWitness {
            syntax,
            key: "coordinate".repeat(1024),
        };
        left.source_type_witness = Some(Arc::new(witness.clone()));
        let mut right = left.clone();
        right.source_type_witness = Some(Arc::new(witness));
        assert!(matches!(
            same_birth_value(&left, &right, &mut 100),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert_eq!(same_birth_value(&left, &right, &mut 65_536), Ok(true));

        let mut changed = (**right.source_type_witness.as_ref().unwrap()).clone();
        changed.syntax.hir_id = Some(ril_compiler_core::ids::TypeExprId(42));
        right.source_type_witness = Some(Arc::new(changed));
        assert_eq!(
            left, right,
            "legacy key equality cannot identify the original header"
        );
        assert_eq!(same_birth_value(&left, &right, &mut 65_536), Ok(false));

        left.source_type_witness = None;
        right.source_type_witness = None;
        let mut bound = CallableReturnBound::raw(Callable::Builtin("entry".into()), span);
        bound.syntax.text = "contract".repeat(1024);
        left.callable_returns.push(Arc::new(bound.clone()));
        right.callable_returns.push(Arc::new(bound));
        assert!(matches!(
            same_birth_value(&left, &right, &mut 100),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert_eq!(same_birth_value(&left, &right, &mut 65_536), Ok(true));

        let mut changed = (**right.callable_returns.first().unwrap()).clone();
        changed.syntax.hir_id = Some(ril_compiler_core::ids::TypeExprId(43));
        right.callable_returns[0] = Arc::new(changed);
        assert_eq!(
            left, right,
            "structural AST equality deliberately omits HIR identity"
        );
        assert_eq!(same_birth_value(&left, &right, &mut 65_536), Ok(false));
    }
}
