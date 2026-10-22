//! Values held across later evaluation must follow allocation-site recency.
//! Each wrapper belongs to one Checker's monotonically growing move history.
//! It must not be transferred between checkers or reused with a rolled-back log.
use super::*;
use crate::sema::{
    application_effect::OccurrenceIdentity,
    context::FrozenEnvironment,
    effect_identity::InvocationContext,
    source_reception::Construction,
    source_types::{SourceSchema, SourceTypesError},
};
use std::sync::Arc;

pub(super) type CheckedSource = Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError>;

fn opaque_construction() -> Arc<Construction> {
    static OPAQUE: std::sync::OnceLock<Arc<Construction>> = std::sync::OnceLock::new();
    OPAQUE
        .get_or_init(|| Arc::new(Construction::Opaque))
        .clone()
}

#[derive(Clone, Debug)]
pub(super) struct EvaluatedValue {
    pub(super) value: Value,
    recency: usize,
    pub(super) observation: Option<usize>,
    pub(super) source_valid: bool,
    pub(super) allocation_epoch: usize,
    pub(super) identity: Option<OccurrenceIdentity>,
    pub(super) birth_context: Option<InvocationContext>,
    pub(super) source: CheckedSource,
    pub(super) fresh: Arc<Construction>,
}
impl EvaluatedValue {
    pub(super) fn try_clone(&self, work: &mut usize) -> Result<Self, SourceTypesError> {
        charge_value_clone(&self.value, work, 0).ok_or(SourceTypesError::BudgetExceeded)?;
        *work = work
            .checked_sub(3)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        Ok(self.clone())
    }
    /// Call after evaluation: the new result already belongs to this epoch.
    pub fn new(value: Value, recency: usize) -> Self {
        Self {
            value,
            recency,
            observation: None,
            source_valid: true,
            allocation_epoch: recency,
            identity: None,
            birth_context: None,
            source: Err(SourceTypesError::MissingNode),
            fresh: opaque_construction(),
        }
    }

    pub(super) fn unobserved(value: Value, recency: usize, source_valid: bool) -> Self {
        let mut packet = Self::new(value, recency);
        packet.source_valid = source_valid;
        packet
    }

    pub(super) fn observed(
        value: Value,
        observation: usize,
        record: &crate::sema::application_effect::EvaluationRecord,
    ) -> Self {
        let mut packet = Self::new(value, record.allocation_epoch);
        packet.observation = Some(observation);
        packet.identity = record.identity;
        packet.birth_context = Some(record.context);
        packet
    }

    pub(super) fn transport(&mut self, moves: &[(NodeId, NodeId)]) {
        for &(recent, older) in &moves[self.recency..] {
            copy::remap_value_origins(&mut self.value, recent, older);
        }
        self.recency = moves.len();
    }

    pub fn current_mut(&mut self, moves: &[(NodeId, NodeId)]) -> &mut Value {
        // Only node references change. Permission, loan/root participants,
        // copy/Result/condition/numeric identities retain their existing duties.
        // remap_value_origins also transports every nested payload witness.
        self.transport(moves);
        // A mutable interface may install another type or callable view. Only
        // an independently checked selection/reception may give it a new Source.
        self.source = Err(SourceTypesError::Unresolved);
        &mut self.value
    }
    pub fn current(&mut self, moves: &[(NodeId, NodeId)]) -> Value {
        self.transport(moves);
        self.value.clone()
    }
    pub(super) fn current_read(
        &self,
        moves: &[(NodeId, NodeId)],
        work: &mut usize,
    ) -> Result<Value, SourceTypesError> {
        transport_value_at(&self.value, moves, self.recency, moves.len(), work)
    }
    pub(super) fn transport_checked(
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
    pub fn into_current(mut self, moves: &[(NodeId, NodeId)]) -> Value {
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
        super::type_source::clone_work::ty(work, &value.ty, depth)?;
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

pub(super) fn same_birth_value(
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
        super::type_source::clone_work::ty(work, &bound.target, depth)
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
pub(super) fn transport_value_at(
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
        copy::remap_value_origins(&mut value, recent, older);
    }
    Ok(value)
}

impl Checker {
    pub(super) fn read_evaluation_packet(
        &mut self,
        packet: &EvaluatedValue,
        work_span: Span,
    ) -> Result<Value, SourceTypesError> {
        let moves = &self.recency_moves;
        let result = self
            .application_effect
            .with_work(|work| packet.current_read(moves, work));
        if let Err(error) = &result {
            self.unsupported(
                work_span,
                format!("evaluation packet read admission: {error}"),
            );
        }
        result
    }
    pub(super) fn transport_evaluation_packet(&mut self, packet: &mut EvaluatedValue, span: Span) {
        let moves = &self.recency_moves;
        if let Err(error) = self
            .application_effect
            .with_work(|work| packet.transport_checked(moves, work))
        {
            self.unsupported(span, format!("evaluation packet epoch transport: {error}"));
            packet.source = Err(error);
            packet.source_valid = false;
            // Keep the original untransported graph and duties inspectable;
            // the failed Source/receiver state prevents their certification.
            packet.value.ty = Ty::Unknown;
        }
    }

    pub(super) fn clone_evaluation_packet(
        &mut self,
        packet: &EvaluatedValue,
        span: Span,
    ) -> Result<EvaluatedValue, SourceTypesError> {
        let result = self
            .application_effect
            .with_work(|work| packet.try_clone(work));
        if let Err(error) = &result {
            self.unsupported(span, format!("evaluation packet clone admission: {error}"));
        }
        result
    }
}

#[cfg(test)]
mod packet_tests {
    use super::*;
    use crate::sema::{
        application_effect::EvaluationRecord, effect_identity::ArgumentKey, source_types::WorkLimit,
    };
    use ril_compiler_core::ids::{
        ActivationEpochId, EvaluationOccurrenceId, ExprId, OptionalTagId,
    };

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
        packet.source = Ok(Some((
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
        )));
        packet
    }

    #[test]
    fn pure_epoch_transport_preserves_birth_source_permissions_and_duties() {
        let mut packet = packet();
        let (schema, environment) = packet.source.as_ref().unwrap().as_ref().unwrap();
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
        let (schema, frozen) = packet.source.as_ref().unwrap().as_ref().unwrap();
        assert_eq!(schema.root_id(), root);
        assert_eq!(frozen.id(), environment);
    }

    #[test]
    fn mutable_current_view_cannot_reuse_the_immutable_input_schema() {
        let original = Arc::new(packet());
        let mut current = original.try_clone(&mut 4096).unwrap();
        current.current_mut(&[]).ty = Ty::Str;
        assert!(matches!(current.source, Err(SourceTypesError::Unresolved)));
        assert!(matches!(original.source, Ok(Some(_))));
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
        packet.source = Ok(None);
        assert!(matches!(
            packet.try_clone(&mut 4096).unwrap().source,
            Ok(None)
        ));
        packet.source = Err(SourceTypesError::MissingNode);
        assert!(matches!(
            packet.try_clone(&mut 4096).unwrap().source,
            Err(SourceTypesError::MissingNode)
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
