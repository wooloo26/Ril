//! Explicit current views retain the packet they consume. A recipe is a claim
//! for independent replay; it never replaces the physical packet's birth.
use super::*;
use crate::sema::{
    copy_contract::CopyCallEventId,
    facts::{Permission, Publication, Slot},
    model::{CallableBound, Ty},
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use ril_syntax::ast::{Annotation, AnnotationKind};

#[derive(Debug, Clone)]
pub(crate) enum CurrentValueStep {
    ReadHandle,
    FieldProjection {
        receiver: Arc<EvaluatedValue>,
        slot: Slot,
        cause: CauseId,
    },
    CatalogCallableBound {
        event: CopyCallEventId,
        argument: u32,
        field: Slot,
        span: Span,
    },
}

impl EvaluatedValue {
    /// Called by a transfer, after its real input has been selected. Source is
    /// obtained from that input or receiver, never inferred from the output Ty.
    pub(crate) fn derive_current(
        input: Arc<Self>,
        step: CurrentValueStep,
        value: Value,
        types: &mut LiveSourceTypes,
        work: &mut usize,
    ) -> Result<Self, SourceTypesError> {
        *work = work
            .checked_sub(3)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        let mut graph_work = WorkLimit::new(*work);
        let source = (|| {
            let input_source =
                input.current_source(SourceTypesRef::Live(types), &mut graph_work)?;
            let schema = input_source.schema.ok_or(SourceTypesError::Unresolved)?;
            let (schema, environment) = match &step {
                CurrentValueStep::FieldProjection { receiver, slot, .. } => {
                    if receiver.current_epoch() != input.current_epoch() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    let receiver_source =
                        receiver.current_source(SourceTypesRef::Live(types), &mut graph_work)?;
                    let path = match slot {
                        Slot::Field(label) => {
                            graph_work.text(label)?;
                            crate::sema::source_types::SourcePath::Field(label.clone())
                        }
                        Slot::Tuple(index) => crate::sema::source_types::SourcePath::Tuple(*index),
                        _ => return Err(SourceTypesError::MissingProjection),
                    };
                    let projected = receiver_source
                        .schema
                        .ok_or(SourceTypesError::Unresolved)?
                        .project_steps(&[path], &mut graph_work)?;
                    if !projected.equivalent_in(
                        &schema,
                        &receiver_source.environment,
                        &input_source.environment,
                        &mut graph_work,
                    )? || (projected.requires_environment(&mut graph_work)?
                        && receiver_source.environment.id() != input_source.environment.id())
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    (projected, receiver_source.environment)
                }
                _ => (schema, input_source.environment),
            };
            SourceRef::intern(&schema, environment, types, &mut graph_work)
        })();
        *work = graph_work.remaining();
        let source = source?;
        let recency = input.current_epoch();
        let source_valid = input.source_valid;
        let birth = input.birth.clone();
        Ok(Self {
            value,
            recency,
            source_valid,
            birth,
            current_source: CurrentSource::Derived(Arc::new(CurrentValueDerivation {
                input,
                step,
                source,
            })),
        })
    }
}

pub(crate) fn catalog_callable_bound(span: Span) -> CallableBound {
    CallableBound {
        annotations: vec![Annotation {
            kind: AnnotationKind::Capability,
            text: "&mut".into(),
            span,
        }],
        source: None,
        typing_environment: crate::sema::builtin_sources::catalog_environment().clone(),
        span,
    }
}

/// Replay a single stored constituent through its access path. Selection of
/// the actual child and its original record edge is a separate obligation.
pub(crate) fn projected_value(
    child: &Value,
    receiver: &Value,
    slot: &Slot,
    cause: CauseId,
    work: &mut usize,
) -> Result<Value, SourceTypesError> {
    charge_value_export(receiver, work)?;
    let mut value = transport_value_at(child, &[], 0, 0, work)?;
    let receiver_ty = match &receiver.ty {
        Ty::Immutable(inner) => &**inner,
        ty => ty,
    };
    let selected = match (receiver_ty, slot) {
        (Ty::Record(fields) | Ty::OpenRecord { fields, .. }, Slot::Field(name)) => {
            fields.get(name).map(|(_, ty)| ty)
        }
        (Ty::Tuple(items), Slot::Tuple(index)) => items.get(*index as usize),
        _ => None,
    }
    .ok_or(SourceTypesError::MissingProjection)?;
    if !receiver.must_results.is_empty() || receiver.origins.nodes.len() != 1 {
        return Err(SourceTypesError::Unresolved);
    }
    crate::sema::clone_work::ty(work, selected, 0).ok_or(SourceTypesError::BudgetExceeded)?;
    value.ty = selected.clone();
    for (&choice, branches) in &receiver.origins.choices {
        *work = work
            .checked_sub(
                1 + branches.len() + value.origins.nodes.len().saturating_mul(branches.len()),
            )
            .ok_or(SourceTypesError::BudgetExceeded)?;
        value.origins.choices.insert(
            choice,
            branches
                .iter()
                .map(|parents| {
                    if receiver
                        .origins
                        .nodes
                        .iter()
                        .any(|parent| parents.contains(parent))
                    {
                        value.origins.nodes.clone()
                    } else {
                        Default::default()
                    }
                })
                .collect(),
        );
    }
    value.permission = value.permission.meet(receiver.permission);
    value.construction &= receiver.construction;
    value.publication = if value.publication == Publication::Immutable
        || receiver.publication == Publication::Immutable
    {
        Publication::Immutable
    } else if receiver.publication == Publication::Live {
        Publication::Live
    } else {
        value.publication
    };
    if !value.origins.nodes.is_empty() {
        value.temporary |= receiver.temporary;
    }
    value.stable &= receiver.stable;
    value.sources = receiver.sources.clone();
    value.static_coordinate = None;
    value
        .callback_parameters
        .extend(&receiver.callback_parameters);
    if !value.ty.scalar() {
        value.scoped.extend(&receiver.scoped);
    }
    value.participants = receiver.participants.clone();
    value.marker = receiver.marker || (receiver.construction && value.marker);
    value.retention_result =
        receiver.retention_result || (receiver.construction && value.retention_result);
    value.through_return |= receiver.through_return;
    if value.ty.scalar() {
        value.unsuffixed_numeric = false;
        value.participants.clear();
        value.temporary = false;
        value.scoped.clear();
    }
    value.must_outer_results = value
        .outer_results
        .intersection(&value.must_results)
        .copied()
        .collect();
    value.cause = cause;
    // The receiver was already walked and admitted above, before allocating
    // the recursive dependency union.
    value.inherit_copy_dependencies(&receiver.nested_copy_dependencies());
    Ok(value)
}

pub(crate) fn read_handle(value: &mut Value) {
    value.permission = Permission::Read;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::facts::{LoanId, Participant};
    use std::collections::{BTreeMap, BTreeSet};

    fn recipe(packet: &EvaluatedValue) -> CurrentValueDerivation {
        let CurrentSource::Derived(derived) = &packet.current_source else {
            panic!("a real generated callback must keep its current recipe")
        };
        CurrentValueDerivation {
            input: derived.input.clone(),
            step: derived.step.clone(),
            source: derived.source,
        }
    }

    #[test]
    fn applied_rows_keep_their_original_environment_through_read_and_field_recipes() {
        use crate::sema::{application_effect::EntryOrigin, validate::solved_facts};
        for layout in ["pointer32", "pointer64"] {
            let verified = crate::Session::with_options(
                ril_test::case_bytes(
                    "tests/regressions/closed-standard-data.ril::applied-effect-reader",
                )
                .to_vec(),
                crate::CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap();
            let facts = verified.facts();
            let calls: Vec<_> = facts
                .copy_invocations
                .iter()
                .enumerate()
                .filter_map(|(index, call)| {
                    let packet = call.entry.callee.as_ref()?;
                    (matches!(call.entry.origin, EntryOrigin::Generated { .. })
                        && matches!(
                            packet.evidence_view().current,
                            CurrentSourceView::Derived {
                                step: CurrentValueStep::CatalogCallableBound { .. },
                                ..
                            }
                        ))
                    .then_some(index)
                })
                .collect();
            assert!(calls.len() >= 2);
            let original = facts.copy_invocations[calls[0]]
                .entry
                .callee
                .as_ref()
                .unwrap();
            let sibling = facts.copy_invocations[calls[1]]
                .entry
                .callee
                .as_ref()
                .unwrap();
            assert!(!original.shares_birth(sibling));
            let projection = recipe(original).input;
            let field = recipe(&projection);
            let CurrentValueStep::FieldProjection { receiver, .. } = &field.step else {
                panic!("actual field recipe required")
            };
            assert!(matches!(
                receiver.evidence_view().current,
                CurrentSourceView::Derived {
                    step: CurrentValueStep::ReadHandle,
                    ..
                }
            ));
            let source = field
                .input
                .current_source(
                    SourceTypesRef::Frozen(&facts.source_types),
                    &mut WorkLimit::new(65536),
                )
                .unwrap();
            let schema = source.schema.unwrap();
            assert!(
                schema
                    .callable_annotations(&mut WorkLimit::new(4096))
                    .unwrap()
                    .unwrap()
                    .iter()
                    .any(|annotation| annotation.contains("Visit<int>"))
            );
            assert_eq!(
                schema.equivalent_in(
                    &schema,
                    &source.environment,
                    &source.environment,
                    &mut WorkLimit::new(65536)
                ),
                Ok(true)
            );
            assert!(
                schema
                    .equivalent(&schema, &mut WorkLimit::new(65536))
                    .is_err(),
                "the actual applied row must require its original interpretation"
            );
            let other_environment = facts
                .evaluations
                .iter()
                .filter_map(|record| record.environment)
                .find(|id| *id != recipe(original).source.view.environment)
                .expect("a separate real evaluation capture must be registered");
            for mutation in 0..3 {
                let mut changed = facts.clone();
                let mut packet = original.try_clone(&mut 1_000_000).unwrap();
                let mut derived = recipe(original);
                match mutation {
                    0 => derived.source.view.environment = other_environment,
                    1 => derived.input = recipe(sibling).input,
                    _ => {
                        derived.source.original = Some(ril_compiler_core::ids::TypeExprId(u32::MAX))
                    }
                }
                packet.current_source = CurrentSource::Derived(Arc::new(derived));
                changed.copy_invocations[calls[0]].entry.callee = Some(Arc::new(packet));
                assert!(
                    solved_facts(&changed).is_err(),
                    "{layout}: row current-view mutation {mutation}"
                );
            }
        }
    }

    #[test]
    fn generated_field_recipes_reject_foreign_operands_and_changed_contracts() {
        for layout in ["pointer32", "pointer64"] {
            generated_field_recipes_for_layout(layout);
        }
    }

    fn generated_field_recipes_for_layout(layout: &str) {
        use crate::sema::{application_effect::EntryOrigin, validate::solved_facts};
        let source =
            ril_test::case_source("tests/regressions/closed-standard-data.ril::repeated-reader");
        let verified = crate::Session::with_options(
            source.as_bytes().to_vec(),
            crate::CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = verified.facts();
        let invocations: Vec<_> = facts
            .copy_invocations
            .iter()
            .enumerate()
            .filter_map(|(index, call)| {
                let packet = call.entry.callee.as_ref()?;
                (matches!(call.entry.origin, EntryOrigin::Generated { .. })
                    && matches!(
                        packet.evidence_view().current,
                        CurrentSourceView::Derived {
                            step: CurrentValueStep::CatalogCallableBound { .. },
                            ..
                        }
                    ))
                .then_some(index)
            })
            .collect();
        assert!(invocations.len() >= 2);
        let (first, second) = (invocations[0], invocations[1]);
        let original = facts.copy_invocations[first].entry.callee.as_ref().unwrap();
        let foreign = facts.copy_invocations[second]
            .entry
            .callee
            .as_ref()
            .unwrap();
        let physical = facts.expressions[original.observation.unwrap()]
            .value
            .packet();
        assert!(original.shares_birth(physical));
        assert!(!original.shares_birth(foreign));
        for mutation in 0..9 {
            let mut changed = facts.clone();
            let mut packet = original.try_clone(&mut 1_000_000).unwrap();
            let mut derived = recipe(original);
            match mutation {
                0 => {
                    let CurrentValueStep::CatalogCallableBound { event, .. } = &mut derived.step
                    else {
                        unreachable!()
                    };
                    *event = CopyCallEventId(u32::MAX);
                }
                1 => {
                    let CurrentValueStep::CatalogCallableBound { argument, .. } = &mut derived.step
                    else {
                        unreachable!()
                    };
                    *argument = u32::MAX;
                }
                2 => {
                    let CurrentValueStep::CatalogCallableBound { field, .. } = &mut derived.step
                    else {
                        unreachable!()
                    };
                    *field = Slot::Field("write".into());
                }
                3 => derived.input = recipe(foreign).input,
                4 => {
                    let mut projected = derived.input.try_clone(&mut 1_000_000).unwrap();
                    let mut field_recipe = recipe(&projected);
                    let foreign_field = recipe(&recipe(foreign).input);
                    let CurrentValueStep::FieldProjection {
                        receiver: foreign_receiver,
                        ..
                    } = foreign_field.step
                    else {
                        unreachable!()
                    };
                    let CurrentValueStep::FieldProjection { receiver, .. } = &mut field_recipe.step
                    else {
                        unreachable!()
                    };
                    *receiver = foreign_receiver;
                    projected.current_source = CurrentSource::Derived(Arc::new(field_recipe));
                    derived.input = Arc::new(projected);
                }
                5 => {
                    let mut projected = derived.input.try_clone(&mut 1_000_000).unwrap();
                    let mut field_recipe = recipe(&projected);
                    let CurrentValueStep::FieldProjection { cause, .. } = &mut field_recipe.step
                    else {
                        unreachable!()
                    };
                    *cause = CauseId(u32::MAX);
                    projected.current_source = CurrentSource::Derived(Arc::new(field_recipe));
                    derived.input = Arc::new(projected);
                }
                6 => {
                    let field_recipe = recipe(&derived.input);
                    let CurrentValueStep::FieldProjection { receiver, .. } = field_recipe.step
                    else {
                        unreachable!()
                    };
                    derived.source = recipe(&receiver).source;
                }
                7 => packet.value.callable_bounds.pop().map(|_| ()).unwrap(),
                _ => {
                    let bound = packet.value.callable_bounds.last_mut().unwrap();
                    bound.typing_environment = crate::sema::context::FrozenEnvironment::default();
                }
            }
            packet.current_source = CurrentSource::Derived(Arc::new(derived));
            assert!(
                packet.shares_birth(original),
                "faults retain the real birth"
            );
            changed.copy_invocations[first].entry.callee = Some(Arc::new(packet));
            assert!(
                solved_facts(&changed).is_err(),
                "current recipe mutation {mutation}"
            );
        }
        let CurrentValueStep::CatalogCallableBound { event, .. } = recipe(original).step else {
            unreachable!()
        };
        let primitive = facts.copy_call_events[event.0 as usize]
            .callee_expression
            .unwrap();
        for mutation in 0..2 {
            let mut changed = facts.clone();
            let value = changed.expressions[primitive]
                .value
                .corrupt_value(&mut 1_000_000)
                .unwrap();
            if mutation == 0 {
                value.ty = Ty::Int("int".into());
            } else {
                value.mutable_environment = true;
            }
            let (_, message) = crate::sema::application_effect::validate(&changed).unwrap_err();
            assert!(
                message.contains(
                    "catalog callable contract changed the original universal primitive descriptor"
                ),
                "primitive mutation {mutation}: {message}"
            );
        }
    }

    #[test]
    fn field_views_replay_authority_and_keep_nested_obligations() {
        let mut child = Value::reference(
            Ty::Array(Box::new(Ty::Int("int".into()))),
            NodeId(2),
            CauseId(4),
        );
        child.permission = Permission::Write;
        child.participants.insert(Participant::Loan(LoanId(3)));
        child.results.insert(7);
        child.must_results.insert(7);
        child.outer_results.insert(7);
        child.option_payload = Some(Box::new(child.clone()));
        let mut receiver = Value::reference(
            Ty::Record(BTreeMap::from([(
                "items".into(),
                (false, child.ty.clone()),
            )])),
            NodeId(1),
            CauseId(5),
        );
        receiver.permission = Permission::Read;
        receiver.publication = Publication::Live;
        receiver.sources.insert(9);
        receiver.participants.insert(Participant::Loan(LoanId(6)));
        let projected = projected_value(
            &child,
            &receiver,
            &Slot::Field("items".into()),
            CauseId(8),
            &mut 4096,
        )
        .unwrap();
        assert_eq!(projected.permission, Permission::Read);
        assert_eq!(projected.sources, BTreeSet::from([9]));
        assert_eq!(
            projected.participants,
            BTreeSet::from([Participant::Loan(LoanId(6))])
        );
        assert_eq!(projected.results, child.results);
        assert_eq!(projected.must_outer_results, BTreeSet::from([7]));
        assert_eq!(projected.option_payload, child.option_payload);
        assert_eq!(child.permission, Permission::Write);
        for mutation in 0..5 {
            let mut forged = projected.clone();
            match mutation {
                0 => forged.permission = Permission::Write,
                1 => forged.participants = child.participants.clone(),
                2 => forged.sources.clear(),
                3 => forged.option_payload = None,
                _ => forged.must_results.clear(),
            }
            assert!(
                !same_birth_value(&projected, &forged, &mut 4096).unwrap(),
                "mutation {mutation}"
            );
        }
        assert_eq!(
            projected_value(
                &child,
                &receiver,
                &Slot::Field("items".into()),
                CauseId(8),
                &mut 0
            )
            .unwrap_err(),
            SourceTypesError::BudgetExceeded
        );
    }
}
