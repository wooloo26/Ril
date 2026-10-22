//! Values held across later evaluation must follow allocation-site recency.
//! Each wrapper belongs to one Checker's monotonically growing move history.
//! It must not be transferred between checkers or reused with a rolled-back log.
use crate::sema::{
    application_effect::OccurrenceIdentity,
    context::FrozenEnvironment,
    effect_identity::InvocationContext,
    facts::NodeId,
    model::{Callable, CallableReturnBound, Value},
    source_reception::Construction,
    source_types::{SourceSchema, SourceTypesError},
};
use std::sync::Arc;

pub(crate) type CheckedSource = Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError>;

fn opaque_construction() -> &'static Construction {
    static OPAQUE: std::sync::OnceLock<Construction> = std::sync::OnceLock::new();
    OPAQUE.get_or_init(|| Construction::Opaque)
}

/// Read-only birth coordinates stay coupled to the captured Source basis.
/// Deref exposes these coordinates without permitting callers to restamp them.
#[derive(Clone, Debug)]
pub(crate) struct EvaluationBirth {
    pub(crate) observation: Option<usize>,
    pub(crate) allocation_epoch: usize,
    pub(crate) identity: Option<OccurrenceIdentity>,
    pub(crate) birth_context: Option<InvocationContext>,
    source: SourceCapture,
}

#[derive(Clone, Debug)]
enum SourceCapture {
    Uncaptured,
    Captured(Arc<BirthSource>),
}

#[derive(Debug)]
struct BirthSource {
    result: CheckedSource,
    fresh: Option<Arc<Construction>>,
}

#[derive(Clone, Debug)]
enum CurrentSource {
    Birth,
    Pending,
    Failed(SourceTypesError),
}

#[derive(Clone, Debug)]
pub(crate) struct EvaluatedValue {
    pub(crate) value: Value,
    recency: usize,
    pub(crate) source_valid: bool,
    birth: EvaluationBirth,
    current_source: CurrentSource,
}

impl std::ops::Deref for EvaluatedValue {
    type Target = EvaluationBirth;

    fn deref(&self) -> &Self::Target {
        &self.birth
    }
}

impl EvaluatedValue {
    /// Capture is single-assignment. Neither mutation nor a failed capture can
    /// replace the original schema, environment, construction or birth identity.
    pub(crate) fn capture_birth_source(
        &mut self,
        result: CheckedSource,
        fresh: Option<Arc<Construction>>,
    ) -> Result<(), SourceTypesError> {
        if !matches!(self.birth.source, SourceCapture::Uncaptured) {
            return Err(SourceTypesError::AlreadyDefined);
        }
        if !matches!(self.current_source, CurrentSource::Birth) {
            return Err(SourceTypesError::SourceViewPending);
        }
        self.birth.source = SourceCapture::Captured(Arc::new(BirthSource { result, fresh }));
        Ok(())
    }

    pub(crate) fn has_captured_source(&self) -> bool {
        matches!(self.birth.source, SourceCapture::Captured(_))
    }

    /// Only an authenticated original-input role may consume this basis. The
    /// current Value may have undergone a separately pending receiving change.
    pub(crate) fn birth_source(
        &self,
    ) -> Result<&Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        match &self.birth.source {
            SourceCapture::Uncaptured => Err(SourceTypesError::SourceNotCaptured),
            SourceCapture::Captured(basis) => basis.result.as_ref().map_err(Clone::clone),
        }
    }

    pub(crate) fn current_source(
        &self,
    ) -> Result<&Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        match &self.current_source {
            CurrentSource::Birth => self.birth_source(),
            CurrentSource::Pending => Err(SourceTypesError::SourceViewPending),
            CurrentSource::Failed(error) => Err(error.clone()),
        }
    }

    pub(crate) fn fresh(&self) -> &Construction {
        match &self.birth.source {
            SourceCapture::Captured(basis) => match basis.fresh.as_deref() {
                Some(fresh) => fresh,
                None => opaque_construction(),
            },
            SourceCapture::Uncaptured => opaque_construction(),
        }
    }

    pub(crate) fn value(&self) -> &Value {
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
            birth: EvaluationBirth {
                observation: None,
                allocation_epoch: recency,
                identity: None,
                birth_context: None,
                source: SourceCapture::Uncaptured,
            },
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
        let mut packet = Self::new(value, record.allocation_epoch);
        packet.birth.observation = Some(observation);
        packet.birth.identity = record.identity;
        packet.birth.birth_context = Some(record.context);
        packet
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

#[cfg(test)]
mod packet_tests {
    use super::*;
    use crate::sema::{
        application_effect::EvaluationRecord,
        effect_identity::ArgumentKey,
        facts::{LoanId, Participant, Permission, ScopeId},
        model::{SourceTypeWitness, Ty},
        source_types::WorkLimit,
    };
    use ril_compiler_core::ids::{
        ActivationEpochId, EvaluationOccurrenceId, ExprId, OptionalTagId,
    };
    use ril_compiler_core::{
        diagnostic::CauseId,
        source::{FileId, Span},
    };
    use std::collections::BTreeSet;

    fn packet() -> EvaluatedValue {
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
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(2),
            identity: Some(OccurrenceIdentity {
                source: ExprId(4),
                activation: ActivationEpochId(5),
            }),
            scope: ScopeId(0),
            context,
            allocation_epoch: 0,
        };
        let mut packet = EvaluatedValue::observed(value, 2, &record);
        packet
            .capture_birth_source(
                Ok(Some((
                    SourceSchema::import(
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
                    FrozenEnvironment::default(),
                ))),
                None,
            )
            .unwrap();
        packet
    }

    #[test]
    fn pure_epoch_transport_preserves_birth_source_permissions_and_duties() {
        let mut packet = packet();
        let (schema, environment) = packet.birth_source().unwrap().as_ref().unwrap();
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
        let (schema, frozen) = packet.birth_source().unwrap().as_ref().unwrap();
        assert_eq!(schema.root_id(), root);
        assert_eq!(frozen.id(), environment);
    }

    #[test]
    fn mutable_current_view_cannot_reuse_the_immutable_input_schema() {
        let original = Arc::new(packet());
        let mut current = original.try_clone(&mut 4096).unwrap();
        current.current_mut(&[]).ty = Ty::Str;
        assert!(matches!(
            current.current_source(),
            Err(SourceTypesError::SourceViewPending)
        ));
        assert!(matches!(current.birth_source(), Ok(Some(_))));
        assert!(matches!(original.current_source(), Ok(Some(_))));
        let (birth, _) = current.birth_source().unwrap().as_ref().unwrap();
        let (original_birth, _) = original.birth_source().unwrap().as_ref().unwrap();
        assert_eq!(birth.root_id(), original_birth.root_id());
        assert_eq!(current.observation, original.observation);
        assert_eq!(current.allocation_epoch, original.allocation_epoch);
    }

    #[test]
    fn packet_clone_admits_owned_values_without_conflating_unknown_and_error() {
        let mut packet = packet();
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
        unknown.capture_birth_source(Ok(None), None).unwrap();
        assert!(matches!(
            unknown.try_clone(&mut 4096).unwrap().birth_source(),
            Ok(None)
        ));
        let mut failed = EvaluatedValue::new(packet.value.clone(), 0);
        failed
            .capture_birth_source(Err(SourceTypesError::MissingNode), None)
            .unwrap();
        assert!(matches!(
            failed.try_clone(&mut 4096).unwrap().birth_source(),
            Err(SourceTypesError::MissingNode)
        ));
    }

    #[test]
    fn uncaptured_source_is_distinct_from_unknown_and_attempted_failure() {
        let mut uncaptured = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        assert!(!uncaptured.has_captured_source());
        assert_eq!(
            uncaptured.current_source().unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        let cloned = uncaptured.try_clone(&mut 100).unwrap();
        assert!(!cloned.has_captured_source());
        assert_eq!(
            cloned.birth_source().unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        uncaptured.capture_birth_source(Ok(None), None).unwrap();
        assert!(uncaptured.has_captured_source());
        assert!(matches!(uncaptured.current_source(), Ok(None)));

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
            assert_eq!(attempted.birth_source().unwrap_err(), error);
        }
    }

    #[test]
    fn birth_source_cannot_be_replaced_or_installed_after_a_current_view_change() {
        let mut packet = packet();
        let root = packet.birth_source().unwrap().as_ref().unwrap().0.root_id();
        packet.invalidate_current_source();
        assert_eq!(
            packet.capture_birth_source(Ok(None), None),
            Err(SourceTypesError::AlreadyDefined)
        );
        assert_eq!(
            packet.birth_source().unwrap().as_ref().unwrap().0.root_id(),
            root
        );
        assert_eq!(
            packet.current_source().unwrap_err(),
            SourceTypesError::SourceViewPending
        );

        let mut pending = EvaluatedValue::new(Value::scalar(Ty::Unit, None, CauseId(0)), 0);
        pending.current_mut(&[]).ty = Ty::Str;
        assert_eq!(
            pending.capture_birth_source(Ok(None), None),
            Err(SourceTypesError::SourceViewPending)
        );
        assert!(!pending.has_captured_source());
        assert_eq!(
            pending.birth_source().unwrap_err(),
            SourceTypesError::SourceNotCaptured
        );
        assert_eq!(
            pending.current_source().unwrap_err(),
            SourceTypesError::SourceViewPending
        );
    }

    #[test]
    fn failed_current_view_keeps_the_original_source_and_duties() {
        let mut packet = packet();
        let environment = packet.birth_source().unwrap().as_ref().unwrap().1.id();
        packet.fail_current_source(SourceTypesError::BudgetExceeded);
        packet.value.ty = Ty::Unknown;
        assert_eq!(
            packet.current_source().unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(
            packet.birth_source().unwrap().as_ref().unwrap().1.id(),
            environment
        );
        assert_eq!(packet.value.results, BTreeSet::from([7]));
        packet.current_mut(&[]).ty = Ty::Str;
        packet.invalidate_current_source();
        packet.fail_current_source(SourceTypesError::Unresolved);
        assert_eq!(
            packet.current_source().unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(packet.value.results, BTreeSet::from([7]));
        assert_eq!(
            packet.birth_source().unwrap().as_ref().unwrap().1.id(),
            environment
        );
        packet
            .transport_checked(&[(NodeId(1), NodeId(6))], &mut 4096)
            .unwrap();
        assert_eq!(
            packet.current_source().unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
        assert_eq!(
            packet.birth_source().unwrap().as_ref().unwrap().1.id(),
            environment
        );
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
        let original = packet();
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
        let packet = packet();
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
