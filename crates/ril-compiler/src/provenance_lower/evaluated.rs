//! Export shared entry packets without rebuilding their Source from values.
use super::*;
use crate::sema::{
    context::FrozenEnvId,
    copy_contract::CopyHeapSnapshot,
    evaluated::{
        CapturedSource, CurrentSourceView, CurrentValueStep, EvaluatedValue, SourceCaptureView,
        SourceRef,
    },
    source_reception::Construction,
    source_types::{SourceTypeIndex, SourceTypesError, WorkLimit},
};
use std::{collections::BTreeMap, sync::Arc};

pub(super) struct PacketSources {
    index: SourceTypeIndex,
    work: WorkLimit,
    hir: Option<Arc<crate::hir::HirProgram>>,
    // Copy memos retain their inputs so allocator reuse cannot alias receipts.
    packets: BTreeMap<*const EvaluatedValue, (Arc<EvaluatedValue>, Arc<p::EvaluatedValue>)>,
    heaps: BTreeMap<*const CopyHeapSnapshot, (Arc<CopyHeapSnapshot>, Arc<p::CopyHeapSnapshot>)>,
}

#[cfg(test)]
#[path = "evaluated_tests.rs"]
mod tests;

impl PacketSources {
    pub(super) fn new(facts: &SemanticFacts) -> Self {
        Self {
            index: facts.source_types.clone(),
            // This is the existing storage Source export allowance, shared by
            // packet and storage exports rather than renewed for each packet.
            work: WorkLimit::new(4_000_000),
            hir: facts.semantic_hir.clone(),
            packets: BTreeMap::new(),
            heaps: BTreeMap::new(),
        }
    }
}

fn failure(error: SourceTypesError) -> NotImplemented {
    NotImplemented::new(
        ril_compiler_core::phase::Stage::Lowering,
        format!("entry packet evidence could not be retained: {error}"),
    )
}

fn capture_unchanged(packet: &EvaluatedValue, capture: &p::SourceCapture) -> bool {
    // Capture is single-assignment. A filled cell cannot replace its result;
    // an unfilled cell becoming filled must not reuse an earlier Core copy.
    matches!(
        (packet.evidence_view().capture, capture),
        (SourceCaptureView::Uncaptured, p::SourceCapture::Uncaptured)
            | (
                SourceCaptureView::Captured { .. },
                p::SourceCapture::Captured { .. }
            )
            | (
                SourceCaptureView::NumericPending { .. },
                p::SourceCapture::NumericPending { .. }
            )
    )
}

impl ReturnContracts {
    pub(super) fn evaluation_record(
        &mut self,
        types: &mut Vec<p::Type>,
        record: &crate::sema::application_effect::EvaluationRecord,
    ) -> Result<p::EvaluationRecord, NotImplemented> {
        self.packet_charge(1)?;
        Ok(p::EvaluationRecord {
            id: record.id,
            source: record.identity.map(|identity| identity.source),
            activation: record.identity.map(|identity| identity.activation),
            scope: record.scope.0,
            context: resumption_context(record.context),
            allocation_epoch: record.allocation_epoch as u64,
            environment: record
                .environment
                .map(|id| self.packet_environment(types, id))
                .transpose()?,
        })
    }

    pub(super) fn source_query<T>(
        &mut self,
        query: impl FnOnce(&SourceTypeIndex, &mut WorkLimit) -> Result<T, SourceTypesError>,
    ) -> Result<T, NotImplemented> {
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        query(&sources.index, &mut sources.work).map_err(failure)
    }

    fn packet_charge(&mut self, units: usize) -> Result<(), NotImplemented> {
        self.source_query(|_, work| work.charge(units))
    }

    fn packet_value_charge(&mut self, value: &m::Value) -> Result<(), NotImplemented> {
        self.source_query(|_, work| {
            let mut remaining = work.remaining();
            let result = crate::sema::evaluated::charge_value_export(value, &mut remaining);
            work.charge(work.remaining() - remaining)?;
            result
        })
    }

    fn packet_environment(
        &mut self,
        types: &mut Vec<p::Type>,
        id: FrozenEnvId,
    ) -> Result<p::FrozenEnvironmentId, NotImplemented> {
        let environment = self.source_query(|index, work| index.environment(id, work))?;
        self.retained_packet_environment(types, &environment)
    }

    pub(super) fn retained_packet_environment(
        &mut self,
        types: &mut Vec<p::Type>,
        environment: &crate::sema::context::FrozenEnvironment,
    ) -> Result<p::FrozenEnvironmentId, NotImplemented> {
        self.packet_charge(1 + self.environment_ids.len().checked_ilog2().unwrap_or(0) as usize)?;
        if let Some(id) = self.environment_ids.get(&environment.id()) {
            return Ok(*id);
        }
        self.source_query(|_, work| {
            let mut remaining = work.remaining();
            let admitted = crate::sema::clone_work::environment(environment, &mut remaining);
            work.charge(work.remaining() - remaining)?;
            admitted.ok_or(SourceTypesError::BudgetExceeded)
        })?;
        Ok(self.environment(types, environment))
    }

    fn packet_source(
        &mut self,
        types: &mut Vec<p::Type>,
        source: SourceRef,
    ) -> Result<p::SourceRef, NotImplemented> {
        let (root, environment) = self.source_query(|index, work| {
            let (_, environment) = index.view_schema(source.view, source.original, work)?;
            Ok((index.retained_root(source.view, work)?, environment))
        })?;
        Ok(p::SourceRef {
            view: p::SourceView {
                ty: root,
                environment: self.retained_packet_environment(types, &environment)?,
            },
            original: source.original,
        })
    }

    fn captured_source(
        &mut self,
        types: &mut Vec<p::Type>,
        source: CapturedSource,
    ) -> Result<p::CapturedSource, NotImplemented> {
        Ok(match source {
            CapturedSource::Known(source) => {
                p::CapturedSource::Known(self.packet_source(types, source)?)
            }
            CapturedSource::Unknown(id) => {
                p::CapturedSource::Unknown(self.packet_environment(types, id)?)
            }
        })
    }

    fn packet_error(
        &mut self,
        error: &SourceTypesError,
    ) -> Result<p::SourceTypesError, NotImplemented> {
        self.packet_charge(1)?;
        Ok(match error {
            SourceTypesError::InvalidEvidence(reason) => {
                self.source_query(|_, work| work.text(reason))?;
                p::SourceTypesError::InvalidEvidence(reason.clone())
            }
            SourceTypesError::BudgetExceeded => p::SourceTypesError::BudgetExceeded,
            SourceTypesError::ForeignIdentity => p::SourceTypesError::ForeignIdentity,
            SourceTypesError::MissingNode => p::SourceTypesError::MissingNode,
            SourceTypesError::SourceNotCaptured => p::SourceTypesError::SourceNotCaptured,
            SourceTypesError::SourceViewPending => p::SourceTypesError::SourceViewPending,
            SourceTypesError::AlreadyDefined => p::SourceTypesError::AlreadyDefined,
            SourceTypesError::DuplicateField => p::SourceTypesError::DuplicateField,
            SourceTypesError::InvalidContainer => p::SourceTypesError::InvalidContainer,
            SourceTypesError::AliasCycle => p::SourceTypesError::AliasCycle,
            SourceTypesError::RowCycle => p::SourceTypesError::RowCycle,
            SourceTypesError::NeedsStaticElaboration => p::SourceTypesError::NeedsStaticElaboration,
            SourceTypesError::Unresolved => p::SourceTypesError::Unresolved,
            SourceTypesError::MissingProjection => p::SourceTypesError::MissingProjection,
            SourceTypesError::CyclicSubstitution => p::SourceTypesError::CyclicSubstitution,
            SourceTypesError::RecursiveLegacyKey => p::SourceTypesError::RecursiveLegacyKey,
            SourceTypesError::IdentityExhausted => p::SourceTypesError::IdentityExhausted,
            SourceTypesError::TransactionOpen => p::SourceTypesError::TransactionOpen,
            SourceTypesError::InvalidTransaction => p::SourceTypesError::InvalidTransaction,
        })
    }

    fn construction(
        &mut self,
        source: &Construction,
        depth: usize,
    ) -> Result<p::Construction, NotImplemented> {
        self.packet_charge(1)?;
        if depth > 64 {
            return Err(failure(SourceTypesError::BudgetExceeded));
        }
        Ok(match source {
            Construction::Opaque => p::Construction::Opaque,
            Construction::Nullary {
                declaration,
                source,
            } => p::Construction::Nullary {
                declaration: *declaration,
                source: *source,
            },
            Construction::Array(items) | Construction::Tuple(items) => {
                self.packet_charge(items.len())?;
                let output = items
                    .iter()
                    .map(|item| self.construction(item, depth + 1))
                    .collect::<Result<_, _>>()?;
                if matches!(source, Construction::Array(_)) {
                    p::Construction::Array(output)
                } else {
                    p::Construction::Tuple(output)
                }
            }
            Construction::Map(items) => {
                self.packet_charge(items.len())?;
                p::Construction::Map(
                    items
                        .iter()
                        .map(|(key, value)| {
                            Ok((
                                self.construction(key, depth + 1)?,
                                self.construction(value, depth + 1)?,
                            ))
                        })
                        .collect::<Result<_, NotImplemented>>()?,
                )
            }
            Construction::Record(fields) => {
                let search = fields.len().checked_ilog2().unwrap_or(0) as usize + 1;
                self.packet_charge(
                    fields
                        .len()
                        .checked_mul(search)
                        .ok_or_else(|| failure(SourceTypesError::BudgetExceeded))?,
                )?;
                for name in fields.keys() {
                    self.source_query(|_, work| {
                        work.charge(name.len().div_ceil(32).saturating_mul(search))
                    })?;
                }
                p::Construction::Record(
                    fields
                        .iter()
                        .map(|(name, value)| {
                            Ok((name.clone(), self.construction(value, depth + 1)?))
                        })
                        .collect::<Result<_, NotImplemented>>()?,
                )
            }
        })
    }

    pub(super) fn packet(
        &mut self,
        types: &mut Vec<p::Type>,
        packet: &Arc<EvaluatedValue>,
        span: Span,
    ) -> Result<Arc<p::EvaluatedValue>, NotImplemented> {
        self.packet_at_depth(types, packet, span, 0)
    }

    fn packet_at_depth(
        &mut self,
        types: &mut Vec<p::Type>,
        packet: &Arc<EvaluatedValue>,
        span: Span,
        depth: usize,
    ) -> Result<Arc<p::EvaluatedValue>, NotImplemented> {
        if depth > 128 {
            return Err(failure(SourceTypesError::BudgetExceeded));
        }
        let pointer = Arc::as_ptr(packet);
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        sources
            .work
            .charge(1 + sources.packets.len().checked_ilog2().unwrap_or(0) as usize)
            .map_err(failure)?;
        if let Some((_, output)) = sources.packets.get(&pointer) {
            if !capture_unchanged(packet, &output.capture) {
                return Err(failure(SourceTypesError::InvalidEvidence(
                    "Source capture changed after Core packet export".into(),
                )));
            }
            return Ok(output.clone());
        }
        let evidence = packet.evidence_view();
        // The Value's span remains diagnostic. EntryArgument separately retains
        // each use span; a shared observed packet uses its canonical HIR span.
        let value_span = evidence
            .birth
            .identity
            .and_then(|identity| {
                sources
                    .hir
                    .as_ref()?
                    .expression(identity.source)
                    .map(|node| node.info.span)
            })
            .unwrap_or(span);
        self.packet_value_charge(packet.value())?;
        let lowered_value = value(types, self, packet.value(), value_span);
        let capture = match evidence.capture {
            SourceCaptureView::Uncaptured => p::SourceCapture::Uncaptured,
            SourceCaptureView::Captured { result, fresh } => p::SourceCapture::Captured {
                result: match result {
                    Ok(source) => Ok(self.captured_source(types, source)?),
                    Err(error) => Err(self.packet_error(error)?),
                },
                fresh: fresh.map(|fresh| self.construction(fresh, 0)).transpose()?,
            },
            SourceCaptureView::NumericPending {
                hole,
                birth,
                environment,
                fresh,
            } => p::SourceCapture::NumericPending {
                hole,
                birth: numeric::birth(*birth),
                environment: self.packet_environment(types, environment)?,
                fresh: fresh.map(|fresh| self.construction(fresh, 0)).transpose()?,
            },
        };
        let current = match evidence.current {
            CurrentSourceView::Birth => p::CurrentSource::Birth,
            CurrentSourceView::Derived {
                input,
                step,
                source,
            } => {
                self.packet_charge(1)?;
                p::CurrentSource::Derived {
                    input: self.packet_at_depth(types, input, span, depth + 1)?,
                    step: self.current_value_step(types, step, span, depth + 1)?,
                    source: self.packet_source(types, source)?,
                }
            }
            CurrentSourceView::Pending => p::CurrentSource::Pending,
            CurrentSourceView::Failed(error) => p::CurrentSource::Failed(self.packet_error(error)?),
            CurrentSourceView::Numeric {
                hole,
                birth,
                environment,
                resolution,
                source,
            } => {
                self.packet_charge(
                    1 + resolution.dependencies.uses.len()
                        + resolution.dependencies.selections.len(),
                )?;
                if let Some(crate::numeric_literals::EncodedNumber::BigInteger(value)) =
                    &resolution.encoded
                {
                    self.packet_charge(value.bits().div_ceil(32) as usize + 1)?;
                }
                p::CurrentSource::Numeric {
                    hole,
                    birth: numeric::birth(*birth),
                    environment: self.packet_environment(types, environment)?,
                    resolution: Arc::new(numeric::resolution(resolution)),
                    source: self.packet_source(types, source)?,
                }
            }
        };
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        if !capture_unchanged(packet, &capture) {
            return Err(failure(SourceTypesError::InvalidEvidence(
                "Source capture changed during Core packet export".into(),
            )));
        }
        sources
            .work
            .charge(2 + sources.packets.len().checked_ilog2().unwrap_or(0) as usize)
            .map_err(failure)?;
        let output = Arc::new(p::EvaluatedValue {
            value: lowered_value,
            birth: p::EvaluationBirthCoordinates {
                observation: evidence
                    .birth
                    .observation
                    .map(|id| {
                        u32::try_from(id)
                            .map(ril_compiler_core::ids::EvaluationOccurrenceId)
                            .map_err(|_| failure(SourceTypesError::IdentityExhausted))
                    })
                    .transpose()?,
                allocation_epoch: evidence.birth.allocation_epoch as u64,
                identity: evidence
                    .birth
                    .identity
                    .map(|identity| p::OccurrenceIdentity {
                        source: identity.source,
                        activation: identity.activation,
                    }),
                context: evidence.birth.context.map(resumption_context),
                environment: evidence
                    .birth
                    .environment
                    .map(|id| self.packet_environment(types, id))
                    .transpose()?,
            },
            current_epoch: evidence.current_epoch as u64,
            capture,
            current,
            source_valid: evidence.source_valid,
        });
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        sources
            .packets
            .insert(pointer, (packet.clone(), output.clone()));
        Ok(output)
    }

    fn current_value_step(
        &mut self,
        types: &mut Vec<p::Type>,
        step: &CurrentValueStep,
        span: Span,
        depth: usize,
    ) -> Result<p::CurrentValueStep, NotImplemented> {
        self.packet_charge(1)?;
        Ok(match step {
            CurrentValueStep::ReadHandle => p::CurrentValueStep::ReadHandle,
            CurrentValueStep::FieldProjection {
                receiver,
                slot,
                cause,
            } => {
                self.packet_slot(slot)?;
                p::CurrentValueStep::FieldProjection {
                    receiver: self.packet_at_depth(types, receiver, span, depth)?,
                    slot: projection(slot),
                    cause: *cause,
                }
            }
            CurrentValueStep::CatalogCallableBound {
                event,
                argument,
                field,
                span,
            } => {
                self.packet_slot(field)?;
                p::CurrentValueStep::CatalogCallableBound {
                    event: p::CopyCallEventId(event.0),
                    argument: *argument,
                    field: projection(field),
                    span: *span,
                }
            }
        })
    }

    pub(super) fn packet_heap(
        &mut self,
        types: &mut Vec<p::Type>,
        heap: &Arc<CopyHeapSnapshot>,
        span: Span,
    ) -> Result<Arc<p::CopyHeapSnapshot>, NotImplemented> {
        let pointer = Arc::as_ptr(heap);
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        sources
            .work
            .charge(1 + sources.heaps.len().checked_ilog2().unwrap_or(0) as usize)
            .map_err(failure)?;
        if let Some((_, output)) = sources.heaps.get(&pointer) {
            return Ok(output.clone());
        }
        self.packet_charge(1 + heap.nodes.len() + heap.relations.len())?;
        for node in &heap.nodes {
            self.packet_charge(
                1 + node.fact.fields.len() + node.fact.writable_roots.len() + node.fields.len(),
            )?;
            for (slot, origins) in &node.fact.fields {
                self.packet_slot(slot)?;
                self.packet_charge(origins.len())?;
            }
            for (slot, value) in &node.fields {
                self.packet_slot(slot)?;
                self.packet_value_charge(value)?;
            }
        }
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        sources
            .work
            .charge(2 + sources.heaps.len().checked_ilog2().unwrap_or(0) as usize)
            .map_err(failure)?;
        let output = Arc::new(p::CopyHeapSnapshot {
            allocation_epoch: heap.allocation_epoch as u64,
            nodes: heap
                .nodes
                .iter()
                .map(|node| copy_node(node, span, types, self))
                .collect(),
            relations: heap
                .relations
                .iter()
                .map(|(a, b, relation)| p::Relation {
                    left: origin(*a),
                    right: origin(*b),
                    equal: relation.equal.0,
                    disjoint: relation.disjoint.0,
                })
                .collect(),
        });
        let sources = self
            .packet_sources
            .as_mut()
            .ok_or_else(|| failure(SourceTypesError::MissingNode))?;
        sources
            .heaps
            .insert(pointer, (heap.clone(), output.clone()));
        Ok(output)
    }

    fn packet_slot(&mut self, slot: &f::Slot) -> Result<(), NotImplemented> {
        use crate::sema::model::rows::RowIdentity;
        self.packet_charge(1)?;
        let text = match slot {
            f::Slot::Field(name) | f::Slot::RowTail(RowIdentity::Binder(name)) => Some(name),
            f::Slot::RowTail(RowIdentity::Fresh { owner, .. }) => Some(owner),
            _ => None,
        };
        if let Some(text) = text {
            self.source_query(|_, work| work.text(text))?;
        }
        Ok(())
    }
}
