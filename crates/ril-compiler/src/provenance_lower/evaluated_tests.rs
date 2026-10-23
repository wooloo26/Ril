//! Pure packet models exercise export, not an invented runtime evaluation.
use super::*;
use crate::sema::{
    application_effect::{
        CallableEntry, EntryArgument, EntryOrigin, EvaluationRecord, OccurrenceIdentity,
    },
    context::FrozenEnvironment,
    effect_identity::InvocationContext,
    facts::{LoanId, Participant, ScopeId},
    numeric_selection::{NumericBirth, NumericDependencies, NumericResolution},
    source_types::{LiveSourceTypes, SourceScalar, SourceSchema},
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{
        ActivationEpochId, EvaluationOccurrenceId, ExprId, NumericHoleId, NumericSelectionId,
        NumericUseId, TypeExprId,
    },
    source::FileId,
};

fn span() -> Span {
    Span {
        file: FileId(0),
        start: 3,
        end: 7,
    }
}

fn context() -> InvocationContext {
    InvocationContext {
        invocation: None,
        owner: None,
        closure: None,
        closure_invocation: None,
        budget_validation: false,
        default_use: None,
    }
}

fn record() -> EvaluationRecord {
    EvaluationRecord {
        id: EvaluationOccurrenceId(0),
        identity: Some(OccurrenceIdentity {
            source: ExprId(4),
            activation: ActivationEpochId(6),
        }),
        scope: ScopeId(0),
        context: context(),
        allocation_epoch: 0,
        environment: None,
    }
}

fn root_value() -> m::Value {
    let mut value = m::Value::scalar(
        m::Ty::Int("int".into()),
        Some(m::Constant::Integer(7)),
        CauseId(0),
    );
    value.origins.nodes.insert(f::NodeId(4));
    value.results.insert(7);
    value.outer_results.insert(8);
    value.must_results.insert(7);
    value.must_outer_results.insert(8);
    value.participants.insert(Participant::Loan(LoanId(3)));
    value
}

fn exporter(facts: &SemanticFacts) -> ReturnContracts {
    ReturnContracts {
        packet_sources: Some(PacketSources::new(facts)),
        ..Default::default()
    }
}

fn known() -> (SemanticFacts, Arc<EvaluatedValue>) {
    let mut live = LiveSourceTypes::default();
    let schema = SourceSchema::scalar(
        SourceScalar::Int,
        Some(TypeExprId(9)),
        &mut WorkLimit::new(4096),
    )
    .unwrap();
    let source = SourceRef::intern(
        &schema,
        FrozenEnvironment::default(),
        &mut live,
        &mut WorkLimit::new(4096),
    )
    .unwrap();
    let mut birth_record = record();
    birth_record.environment = Some(
        live.intern_environment(
            crate::sema::context::TypingEnvironment {
                contract_bindings: [("caller".into(), 2)].into(),
                ..Default::default()
            }
            .freeze(),
            &mut WorkLimit::new(4096),
        )
        .unwrap(),
    );
    let mut packet = EvaluatedValue::observed(root_value(), 0, &birth_record);
    packet
        .capture_birth_source(
            Ok(CapturedSource::Known(source)),
            Some(Arc::new(Construction::Record(
                [(
                    "items".into(),
                    Construction::Tuple(vec![
                        Construction::Array(vec![]),
                        Construction::Map(vec![]),
                    ]),
                )]
                .into(),
            ))),
        )
        .unwrap();
    let packet = Arc::new(packet);
    (
        SemanticFacts {
            source_types: live.freeze(),
            expressions: vec![crate::sema::ExpressionFact {
                source_id: Some(ExprId(4)),
                allocation_epoch: 0,
                span: span(),
                value: crate::sema::PhysicalValue::from_packet(packet.clone()),
            }],
            evaluations: vec![birth_record],
            ..Default::default()
        },
        packet,
    )
}

#[test]
fn derived_packets_keep_the_child_birth_and_all_input_receiver_and_catalog_receipts() {
    let mut live = LiveSourceTypes::default();
    let mut work = WorkLimit::new(100_000);
    let environment = FrozenEnvironment::default();
    let gamma = live
        .intern_environment(environment.clone(), &mut work)
        .unwrap();
    let scalar = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
    let function = SourceSchema::callable(
        &[(ParameterMode::Read, scalar.clone())],
        &scalar,
        &[],
        Some(TypeExprId(9)),
        &mut work,
    )
    .unwrap();
    let receiver_schema = SourceSchema::record(
        &[("read".into(), false, function.clone())],
        None,
        Some(TypeExprId(10)),
        &mut work,
    )
    .unwrap();
    let child_source =
        SourceRef::intern(&function, environment.clone(), &mut live, &mut work).unwrap();
    let receiver_source =
        SourceRef::intern(&receiver_schema, environment, &mut live, &mut work).unwrap();
    let mut child_record = record();
    child_record.environment = Some(gamma);
    let mut child_value = root_value();
    child_value.ty = m::Ty::Callable(
        vec![m::Ty::Int("int".into())],
        Box::new(m::Ty::Int("int".into())),
    );
    child_value.constant = None;
    let mut child = EvaluatedValue::observed(child_value, 0, &child_record);
    child
        .capture_birth_source(Ok(CapturedSource::Known(child_source)), None)
        .unwrap();
    let child = Arc::new(child);
    let receiver_record = EvaluationRecord {
        id: EvaluationOccurrenceId(1),
        identity: Some(OccurrenceIdentity {
            source: ExprId(5),
            activation: ActivationEpochId(7),
        }),
        environment: Some(gamma),
        ..record()
    };
    let mut receiver_value = m::Value::scalar(
        m::Ty::Record([("read".into(), (false, child.value().ty.clone()))].into()),
        None,
        CauseId(0),
    );
    receiver_value.origins.nodes.insert(f::NodeId(10));
    receiver_value.permission = f::Permission::Write;
    let mut receiver = EvaluatedValue::observed(receiver_value, 1, &receiver_record);
    receiver
        .capture_birth_source(Ok(CapturedSource::Known(receiver_source)), None)
        .unwrap();
    let original_receiver = Arc::new(receiver);
    let mut read_value = original_receiver.value().clone();
    crate::sema::evaluated::read_handle(&mut read_value);
    let receiver = Arc::new(
        EvaluatedValue::derive_current(
            original_receiver.clone(),
            CurrentValueStep::ReadHandle,
            read_value,
            &mut live,
            &mut 100_000,
        )
        .unwrap(),
    );
    let slot = f::Slot::Field("read".into());
    let cause = CauseId(42);
    let projected_value = crate::sema::evaluated::projected_value(
        child.value(),
        receiver.value(),
        &slot,
        cause,
        &mut 100_000,
    )
    .unwrap();
    let projected = Arc::new(
        EvaluatedValue::derive_current(
            child.clone(),
            CurrentValueStep::FieldProjection {
                receiver: receiver.clone(),
                slot: slot.clone(),
                cause,
            },
            projected_value,
            &mut live,
            &mut 100_000,
        )
        .unwrap(),
    );
    assert!(projected.shares_birth(&child));
    assert!(receiver.shares_birth(&original_receiver));
    let catalog_span = Span {
        start: 11,
        end: 29,
        ..span()
    };
    let mut bounded_value = projected.value().clone();
    bounded_value
        .callable_bounds
        .push(crate::sema::evaluated::catalog_callable_bound(catalog_span));
    let bounded = Arc::new(
        EvaluatedValue::derive_current(
            projected.clone(),
            CurrentValueStep::CatalogCallableBound {
                event: crate::sema::copy_contract::CopyCallEventId(17),
                argument: 3,
                field: slot,
                span: catalog_span,
            },
            bounded_value,
            &mut live,
            &mut 100_000,
        )
        .unwrap(),
    );
    assert!(bounded.shares_birth(&child));
    let facts = SemanticFacts {
        source_types: live.freeze(),
        ..Default::default()
    };
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    let original_child = contracts.packet(&mut types, &child, span()).unwrap();
    let original_receiver_core = contracts
        .packet(&mut types, &original_receiver, span())
        .unwrap();
    let receiver_core = contracts.packet(&mut types, &receiver, span()).unwrap();
    let projected_core = contracts.packet(&mut types, &projected, span()).unwrap();
    let bounded_core = contracts.packet(&mut types, &bounded, span()).unwrap();
    assert_eq!(bounded_core.birth, original_child.birth);
    assert_eq!(projected_core.birth, original_child.birth);
    let p::CurrentSource::Derived {
        input,
        step,
        source,
    } = &receiver_core.current
    else {
        panic!("receiver ReadHandle receipt was lost")
    };
    assert!(Arc::ptr_eq(input, &original_receiver_core));
    assert!(matches!(step, p::CurrentValueStep::ReadHandle));
    let receiver_environment = source.view.environment;
    let p::CurrentSource::Derived {
        input,
        step:
            p::CurrentValueStep::FieldProjection {
                receiver,
                slot,
                cause: retained_cause,
            },
        source,
    } = &projected_core.current
    else {
        panic!("field projection receipt was lost")
    };
    assert!(Arc::ptr_eq(input, &original_child));
    assert!(Arc::ptr_eq(receiver, &receiver_core));
    assert!(matches!(slot, p::Projection::Field(label) if label=="read"));
    assert_eq!(*retained_cause, cause);
    assert_eq!(source.view.environment, receiver_environment);
    let projected_source = *source;
    let p::CurrentSource::Derived {
        input,
        step:
            p::CurrentValueStep::CatalogCallableBound {
                event,
                argument,
                field,
                span,
            },
        source,
    } = &bounded_core.current
    else {
        panic!("catalog callable-bound receipt was lost")
    };
    assert!(Arc::ptr_eq(input, &projected_core));
    assert_eq!(*event, p::CopyCallEventId(17));
    assert_eq!(*argument, 3);
    assert!(matches!(field, p::Projection::Field(label) if label=="read"));
    assert_eq!(*span, catalog_span);
    assert_eq!(*source, projected_source);
    assert_eq!(bounded_core.callable_bounds.len(), 1);
    let retained = facts
        .source_types
        .retained(&mut WorkLimit::new(100_000))
        .unwrap();
    assert!(
        matches!(retained.graph.get(source.view.ty), Some(p::SourceTypeNode::Callable { parameters, .. }) if parameters.len()==1)
    );
    assert_eq!(contracts.packet_sources.as_ref().unwrap().packets.len(), 5);
}

#[test]
fn physical_birth_and_source_declaration_environments_keep_separate_identities() {
    let (facts, packet) = known();
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    let physical = contracts
        .evaluation_record(&mut types, &facts.evaluations[0])
        .unwrap();
    let output = contracts.packet(&mut types, &packet, span()).unwrap();
    let physical_environment = physical.environment.unwrap();
    assert_eq!(output.birth.environment, Some(physical_environment));
    let p::SourceCapture::Captured {
        result: Ok(p::CapturedSource::Known(source)),
        ..
    } = &output.capture
    else {
        panic!("known declaration Source was lost");
    };
    assert_ne!(physical_environment, source.view.environment);
    assert_eq!(
        contracts.environments[physical_environment.0 as usize].lexical,
        [("caller".into(), 2)]
    );
    assert!(
        contracts.environments[source.view.environment.0 as usize]
            .lexical
            .is_empty()
    );
    let unported = contracts.evaluation_record(&mut types, &record()).unwrap();
    assert_eq!(unported.environment, None);

    let mut missing = record();
    missing.environment = Some(FrozenEnvironment::default().id());
    assert!(
        contracts.evaluation_record(&mut types, &missing).is_err(),
        "an absent physical environment cannot be replaced by a fresh default"
    );
}

#[test]
fn complete_packets_keep_birth_graph_duties_and_pending_current_distinct() {
    let (facts, mut packet) = known();
    Arc::make_mut(&mut packet).current_mut(&[]).ty = m::Ty::Bool;
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    let output = contracts.packet(&mut types, &packet, span()).unwrap();
    assert_eq!(output.birth.observation, Some(EvaluationOccurrenceId(0)));
    assert_eq!(
        output.birth.identity,
        Some(p::OccurrenceIdentity {
            source: ExprId(4),
            activation: ActivationEpochId(6)
        })
    );
    assert_eq!(output.birth.context, Some(resumption_context(context())));
    assert_eq!(output.birth.allocation_epoch, 0);
    assert_eq!(output.current_epoch, 0);
    assert!(matches!(types[output.value.ty.0 as usize], p::Type::Bool));
    assert!(matches!(output.current, p::CurrentSource::Pending));
    assert_eq!(output.value.results, vec![7]);
    assert_eq!(output.value.outer_results, vec![8]);
    assert_eq!(output.value.must_results, vec![7]);
    assert_eq!(output.value.must_outer_results, vec![8]);
    assert!(matches!(
        output.value.participants.as_slice(),
        [p::Participant::Loan(3)]
    ));
    let p::SourceCapture::Captured {
        result: Ok(p::CapturedSource::Known(source)),
        fresh,
    } = &output.capture
    else {
        panic!("birth Source was replaced by the pending current view")
    };
    assert_eq!(source.original, Some(TypeExprId(9)));
    let retained = facts
        .source_types
        .retained(&mut WorkLimit::new(4096))
        .unwrap();
    assert!(matches!(
        retained.graph.get(source.view.ty),
        Some(p::SourceTypeNode::Scalar(p::SourceScalar::Int))
    ));
    assert!(
        matches!(fresh, Some(p::Construction::Record(fields)) if matches!(fields.get("items"), Some(p::Construction::Tuple(items)) if matches!(items.as_slice(), [p::Construction::Array(a),p::Construction::Map(m)] if a.is_empty() && m.is_empty())))
    );
}

#[test]
fn unknown_uncaptured_and_failed_captures_never_collapse_into_each_other() {
    let mut live = LiveSourceTypes::default();
    let environment = live
        .intern_environment(FrozenEnvironment::default(), &mut WorkLimit::new(4096))
        .unwrap();
    let facts = SemanticFacts {
        source_types: live.freeze(),
        ..Default::default()
    };
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    let uncaptured = Arc::new(EvaluatedValue::new(root_value(), 0));
    assert!(matches!(
        contracts
            .packet(&mut types, &uncaptured, span())
            .unwrap()
            .capture,
        p::SourceCapture::Uncaptured
    ));
    let mut missing_context = EvaluatedValue::observed(root_value(), 0, &record());
    assert!(
        missing_context
            .capture_birth_source(Ok(CapturedSource::Unknown(environment)), None)
            .is_err()
    );
    let mut observed = record();
    observed.environment = Some(environment);
    let mut unknown = EvaluatedValue::observed(root_value(), 0, &observed);
    unknown
        .capture_birth_source(Ok(CapturedSource::Unknown(environment)), None)
        .unwrap();
    let unknown = contracts
        .packet(&mut types, &Arc::new(unknown), span())
        .unwrap();
    let p::SourceCapture::Captured {
        result: Ok(p::CapturedSource::Unknown(id)),
        fresh: None,
    } = &unknown.capture
    else {
        panic!("unknown lost its registered environment")
    };
    assert!((id.0 as usize) < contracts.environments.len());
    let mut failed = EvaluatedValue::new(root_value(), 0);
    failed
        .capture_birth_source(
            Err(SourceTypesError::InvalidEvidence(
                "wrong physical input".into(),
            )),
            None,
        )
        .unwrap();
    failed.fail_current_source(SourceTypesError::BudgetExceeded);
    failed.source_valid = false;
    let failed = contracts
        .packet(&mut types, &Arc::new(failed), span())
        .unwrap();
    assert!(
        matches!(&failed.capture, p::SourceCapture::Captured { result: Err(p::SourceTypesError::InvalidEvidence(reason)), fresh: None } if reason=="wrong physical input")
    );
    assert!(matches!(
        failed.current,
        p::CurrentSource::Failed(p::SourceTypesError::BudgetExceeded)
    ));
    assert!(!failed.source_valid);
    assert_eq!(failed.value.results, vec![7]);
}

#[test]
fn numeric_packets_retain_pending_birth_and_the_complete_resolution() {
    let mut live = LiveSourceTypes::default();
    let environment = live
        .intern_environment(FrozenEnvironment::default(), &mut WorkLimit::new(4096))
        .unwrap();
    let hole = NumericHoleId(3);
    let mut value = root_value();
    value.ty = m::Ty::NumericHole(hole);
    let mut missing_context = EvaluatedValue::observed(value.clone(), 0, &record());
    let birth = NumericBirth {
        occurrence: record().identity.unwrap(),
        scope: ScopeId(0),
        context: context(),
        allocation_epoch: 0,
    };
    assert!(
        missing_context
            .capture_numeric_birth_source(hole, birth, environment, None)
            .is_err()
    );
    let mut observed = record();
    observed.environment = Some(environment);
    let mut packet = EvaluatedValue::observed(value, 0, &observed);
    packet
        .capture_numeric_birth_source(
            hole,
            birth,
            environment,
            Some(Arc::new(Construction::Opaque)),
        )
        .unwrap();
    let resolution = Arc::new(NumericResolution {
        number_type: crate::numeric_literals::NumberType::Int,
        constant: Some(m::Constant::Integer(7)),
        encoded: None,
        dependencies: NumericDependencies {
            uses: [NumericUseId(1)].into(),
            selections: [NumericSelectionId(2)].into(),
        },
    });
    resolution.apply(&mut packet.value, &mut 4096).unwrap();
    packet
        .apply_numeric_resolution(hole, resolution, &mut live, &mut 4096)
        .unwrap();
    let facts = SemanticFacts {
        source_types: live.freeze(),
        ..Default::default()
    };
    let output = exporter(&facts)
        .packet(&mut vec![], &Arc::new(packet), span())
        .unwrap();
    let p::SourceCapture::NumericPending {
        hole: original_hole,
        birth,
        environment,
        fresh,
    } = &output.capture
    else {
        panic!("numeric selection rewrote birth Source")
    };
    assert_eq!(*original_hole, hole);
    assert_eq!(birth.source, ExprId(4));
    assert!(matches!(fresh, Some(p::Construction::Opaque)));
    let p::CurrentSource::Numeric {
        hole: current_hole,
        birth: current_birth,
        environment: current_environment,
        resolution,
        source,
    } = &output.current
    else {
        panic!("numeric resolution receipt was erased")
    };
    assert_eq!(*current_hole, hole);
    assert_eq!(current_birth, birth);
    assert_eq!(current_environment, environment);
    assert_eq!(source.view.environment, *environment);
    assert_eq!(output.birth.environment, Some(*environment));
    assert_eq!(resolution.number_type, p::NumericType::Int);
    assert!(matches!(resolution.constant, Some(p::Constant::Integer(7))));
    assert_eq!(resolution.dependencies.uses, [NumericUseId(1)]);
    assert_eq!(resolution.dependencies.selections, [NumericSelectionId(2)]);
    assert_eq!(output.value.results, vec![7]);
}

#[test]
fn common_entries_share_one_packet_and_heap_without_another_root_value() {
    let (facts, packet) = known();
    let heap = Arc::new(CopyHeapSnapshot {
        allocation_epoch: 0,
        nodes: vec![crate::sema::copy_contract::CopyNode {
            origin: f::NodeId(4),
            fact: f::HeapNode {
                kind: f::OriginKind::Opaque,
                multiplicity: f::Multiplicity::One,
                owner: ScopeId(0),
                fields: [(f::Slot::Field("item".into()), [f::NodeId(5)].into())].into(),
                writable_roots: [f::RootId(2)].into(),
                escaping: false,
                cause: CauseId(0),
            },
            fields: vec![(f::Slot::Field("item".into()), root_value())],
            length: Some(Some(1)),
            fixed: true,
        }],
        relations: vec![(
            f::NodeId(4),
            f::NodeId(5),
            r::Relation {
                equal: r::Condition::FALSE,
                disjoint: r::Condition::TRUE,
            },
        )],
    });
    let entry = CallableEntry {
        parent: Some(ActivationEpochId(6)),
        caller_context: context(),
        origin: EntryOrigin::DeclarationProbe,
        allocation_epoch: 0,
        callee: Some(packet.clone()),
        arguments: Arc::new(vec![EntryArgument {
            mode: ParameterMode::Read,
            packet: packet.clone(),
            span: span(),
            heap: Some(heap.clone()),
        }]),
    };
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    assert!(Arc::ptr_eq(facts.expressions[0].value.packet(), &packet));
    let physical = contracts
        .packet(&mut types, facts.expressions[0].value.packet(), span())
        .unwrap();
    let first = callable_entry(&entry, span(), &mut types, &mut contracts).unwrap();
    let second = callable_entry(&entry, span(), &mut types, &mut contracts).unwrap();
    assert!(Arc::ptr_eq(
        &first.arguments[0].packet,
        &second.arguments[0].packet
    ));
    assert!(Arc::ptr_eq(
        first.callee.as_ref().unwrap(),
        &first.arguments[0].packet
    ));
    assert!(Arc::ptr_eq(&physical, &first.arguments[0].packet));
    let core = lower(&facts).unwrap();
    assert_eq!(core.values.len(), 1);
    // Each exporter assigns local environment ordinals. Compare coordinates
    // directly, and authenticate Gamma against its record in each registry.
    let core_birth = core.values[0].birth;
    assert_eq!(core_birth.observation, physical.birth.observation);
    assert_eq!(core_birth.identity, physical.birth.identity);
    assert_eq!(core_birth.context, physical.birth.context);
    assert_eq!(core_birth.allocation_epoch, physical.birth.allocation_epoch);
    let local_record = contracts
        .evaluation_record(&mut types, &facts.evaluations[0])
        .unwrap();
    assert_eq!(physical.birth.environment, local_record.environment);
    assert_eq!(core_birth.environment, core.evaluations[0].environment);
    let local_gamma = &contracts.environments[physical.birth.environment.unwrap().0 as usize];
    let core_gamma = &core.frozen_environments[core_birth.environment.unwrap().0 as usize];
    assert_eq!(local_gamma.lexical, [("caller".into(), 2)]);
    assert_eq!(core_gamma.lexical, local_gamma.lexical);
    let p::SourceCapture::Captured {
        result: Ok(p::CapturedSource::Known(source)),
        ..
    } = &core.values[0].capture
    else {
        panic!("physical Source declaration Gamma was lost");
    };
    assert_ne!(Some(source.view.environment), core_birth.environment);
    assert!(
        core.frozen_environments[source.view.environment.0 as usize]
            .lexical
            .is_empty()
    );
    assert_eq!(core.values[0].results, [7]);
    assert!(Arc::ptr_eq(
        first.arguments[0].heap.as_ref().unwrap(),
        second.arguments[0].heap.as_ref().unwrap()
    ));
    assert_eq!(first.arguments[0].packet.value.results, [7]);
    assert_eq!(
        first.arguments[0].heap.as_ref().unwrap().allocation_epoch,
        0
    );
    let retained_heap = first.arguments[0].heap.as_ref().unwrap();
    assert_eq!(retained_heap.nodes[0].origin.id, OriginId(4));
    assert!(retained_heap.nodes[0].fixed);
    assert_eq!(retained_heap.nodes[0].length, Some(Some(1)));
    assert!(
        matches!(&retained_heap.nodes[0].fields[0], (p::Projection::Field(name), value) if name=="item" && value.results==[7])
    );
    assert_eq!(retained_heap.relations[0].left, OriginId(4));
    assert_eq!(retained_heap.relations[0].right, OriginId(5));
    assert_eq!(retained_heap.relations[0].disjoint, r::Condition::TRUE.0);
    let mut changed = entry;
    Arc::make_mut(&mut changed.arguments)[0].heap = Some(Arc::new(CopyHeapSnapshot {
        allocation_epoch: 1,
        ..(*heap).clone()
    }));
    assert!(
        callable_entry(&changed, span(), &mut types, &mut contracts).is_err(),
        "a heap proof from another epoch must not be paired with the packet"
    );
    changed.callee = None;
    Arc::make_mut(&mut changed.arguments)[0].heap = None;
    assert!(
        callable_entry(&changed, span(), &mut types, &mut contracts)
            .unwrap()
            .callee
            .is_none()
    );
    changed.allocation_epoch = 1;
    assert!(
        callable_entry(&changed, span(), &mut types, &mut contracts).is_err(),
        "a cached argument packet still has to match the new entry epoch"
    );
    changed.arguments = Arc::new(vec![]);
    changed.callee = Some(packet);
    assert!(
        callable_entry(&changed, span(), &mut types, &mut contracts).is_err(),
        "a zero-argument entry cannot borrow a callee from another epoch"
    );
    changed.callee = None;
    assert!(callable_entry(&changed, span(), &mut types, &mut contracts).is_ok());
}

#[test]
fn core_copy_memos_reject_a_capture_completed_after_export() {
    let facts = SemanticFacts::default();
    let mut writer = EvaluatedValue::new(root_value(), 0);
    let physical = Arc::new(writer.try_clone(&mut 4096).unwrap());
    let mut contracts = exporter(&facts);
    let mut types = vec![];
    let initial = contracts.packet(&mut types, &physical, span()).unwrap();
    assert!(matches!(initial.capture, p::SourceCapture::Uncaptured));
    writer
        .capture_birth_source(Err(SourceTypesError::MissingNode), None)
        .unwrap();
    assert!(
        contracts.packet(&mut types, &physical, span()).is_err(),
        "a same-pointer memo cannot conceal Source capture completed after the snapshot"
    );
    let terminal = exporter(&facts)
        .packet(&mut vec![], &physical, span())
        .unwrap();
    assert!(matches!(
        terminal.capture,
        p::SourceCapture::Captured {
            result: Err(p::SourceTypesError::MissingNode),
            ..
        }
    ));
    assert_eq!(
        writer.capture_birth_source(
            Ok(CapturedSource::Unknown(FrozenEnvironment::default().id())),
            None
        ),
        Err(SourceTypesError::AlreadyDefined)
    );
}

#[test]
fn entry_origin_copies_share_the_budget_before_vectors_text_and_environments() {
    use crate::sema::application_effect::{InputOrigin, SignatureFormal, SignatureProbeSource};
    use ril_compiler_core::projection::TypeProjection;
    let label = "field".repeat(1024);
    let origins = [
        EntryOrigin::Generated {
            anchor: ActivationEpochId(6),
            callee: EvaluationOccurrenceId(2),
            inputs: vec![InputOrigin::Observed(EvaluationOccurrenceId(2)); 128],
        },
        EntryOrigin::SignatureProbe(Arc::new(SignatureProbeSource {
            source: TypeExprId(9),
            header: Arc::new(ril_syntax::ast::TypeExpr {
                hir_id: Some(TypeExprId(9)),
                text: String::new(),
                span: span(),
                kind: ril_syntax::ast::TypeKind::Name {
                    path: vec!["int".into()],
                    arguments: vec![],
                },
            }),
            path: Arc::new(vec![
                TypeProjection::RecordRemainder([label.clone()].into()),
                TypeProjection::Field(label.clone()),
            ]),
            environment: crate::sema::context::TypingEnvironment {
                contract_bindings: [(label, 3)].into(),
                ..Default::default()
            }
            .freeze(),
            formals: Arc::new(vec![SignatureFormal {
                slot: 0,
                binding: 3,
            }]),
        })),
    ];
    for origin in origins {
        let facts = SemanticFacts::default();
        let entry = CallableEntry {
            parent: None,
            caller_context: context(),
            origin,
            allocation_epoch: 0,
            callee: None,
            arguments: Arc::new(vec![]),
        };
        let mut context = exporter(&facts);
        let before = context.packet_sources.as_ref().unwrap().work.remaining();
        let mut types = vec![];
        let output = callable_entry(&entry, span(), &mut types, &mut context).unwrap();
        let exact = before - context.packet_sources.as_ref().unwrap().work.remaining();
        for units in [1, exact - 1, exact] {
            let mut context = exporter(&facts);
            context.packet_sources.as_mut().unwrap().work = WorkLimit::new(units);
            assert_eq!(
                callable_entry(&entry, span(), &mut vec![], &mut context).is_ok(),
                units == exact
            );
        }
        match (&entry.origin, &output.origin) {
            (
                EntryOrigin::Generated { inputs, .. },
                p::EntryOrigin::Generated {
                    inputs: retained, ..
                },
            ) => assert_eq!(inputs.len(), retained.len()),
            (EntryOrigin::SignatureProbe(source), p::EntryOrigin::SignatureProbe(retained)) => {
                assert_eq!(source.path.as_ref(), &retained.path);
                assert_eq!(source.formals.len(), retained.formals.len());
                assert_eq!(
                    context.environments[retained.environment.0 as usize]
                        .lexical
                        .len(),
                    1
                );
            }
            _ => panic!("entry origin shape changed during export"),
        }
    }
}

#[test]
fn oversized_observation_indices_cannot_alias_a_core_occurrence() {
    if usize::BITS <= u32::BITS {
        return;
    }
    let packet = Arc::new(EvaluatedValue::observed(
        root_value(),
        usize::MAX,
        &record(),
    ));
    let facts = SemanticFacts::default();
    let mut contracts = exporter(&facts);
    assert!(contracts.packet(&mut vec![], &packet, span()).is_err());
    assert!(
        contracts
            .packet_sources
            .as_ref()
            .unwrap()
            .packets
            .is_empty()
    );
}

#[test]
fn source_coordinates_and_shared_work_cannot_be_forged_by_export() {
    let (facts, packet) = known();
    let mut context = exporter(&facts);
    let before = context.packet_sources.as_ref().unwrap().work.remaining();
    context.packet(&mut vec![], &packet, span()).unwrap();
    let exact = before - context.packet_sources.as_ref().unwrap().work.remaining();
    for units in [0, exact - 1, exact] {
        let mut context = exporter(&facts);
        context.packet_sources.as_mut().unwrap().work = WorkLimit::new(units);
        assert_eq!(
            context.packet(&mut vec![], &packet, span()).is_ok(),
            units == exact
        );
        assert_eq!(
            context.packet_sources.as_ref().unwrap().packets.len(),
            usize::from(units == exact)
        );
    }
    let foreign = SemanticFacts::default();
    assert!(
        exporter(&foreign)
            .packet(&mut vec![], &packet, span())
            .is_err(),
        "a foreign Source arena cannot become a Core root ordinal"
    );
    let missing_environment = FrozenEnvironment::default().id();
    let mut observed = record();
    observed.environment = Some(missing_environment);
    let mut missing = EvaluatedValue::observed(root_value(), 0, &observed);
    missing
        .capture_birth_source(Ok(CapturedSource::Unknown(missing_environment)), None)
        .unwrap();
    assert!(
        exporter(&facts)
            .packet(&mut vec![], &Arc::new(missing), span())
            .is_err(),
        "unknown still requires its actual registered environment"
    );
}
