//! Context selects constructor type variables only after the actual payload's
//! known Source or fresh literal tree has passed the shared receiving relation.
use super::*;
use crate::sema::source_types::{SourceContainer, SourcePath};
use crate::sema::{
    source_construction::{self, Input, Literal},
    source_types::projection_receipts::ProjectionOccurrence,
};
use ril_compiler_core::builtin_calls::PayloadConstructor;

impl Checker {
    pub(super) fn contextual_construction_input(
        &self,
        source_id: ril_compiler_core::ids::ExprId,
        packet: &EvaluatedValue,
        frame: &Frame,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<Input, SourceTypesError> {
        work.charge(3)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let observation = packet.observation.ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .application_effect
            .expressions
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let record = self
            .application_effect
            .evaluations
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
        let context = self.invocation_context(frame.callable_owner);
        let birth = packet.birth_coordinates();
        if source_id != identity.source
            || fact.source_id != Some(source_id)
            || record.context != context
            || birth.context != Some(context)
            || birth.observation != Some(observation)
            || birth.identity != Some(identity)
            || birth.environment != record.environment
            || birth.allocation_epoch != record.allocation_epoch
            || record.id.0 as usize != observation
        {
            return Err(SourceTypesError::Unresolved);
        }
        let source = packet
            .input_source(
                SourceTypesRef::Live(self.type_source.storage.live_types()),
                work,
            )?
            .into_known();
        let fresh = source_construction::hir_construction(source_id, &self.semantic_hir, work, 0)?;
        let parent = ProjectionOccurrence {
            identity,
            context,
            cause: fact.value.cause,
        };
        let literal = if source.is_some() {
            Literal::Opaque
        } else {
            source_construction::hir_literal_plan(source_id, &self.semantic_hir, work)?.try_map(
                |child| {
                    let index = self
                        .source_projection_receipts()
                        .child_observation(parent, child, work)?
                        .0 as usize;
                    let child_packet = self
                        .application_effect
                        .expressions
                        .get(index)
                        .ok_or(SourceTypesError::MissingNode)?
                        .value
                        .packet();
                    self.contextual_construction_input(child, child_packet, frame, work, depth + 1)
                },
            )?
        };
        Ok(Input {
            source,
            fresh,
            literal,
        })
    }

    pub(super) fn prepare_contextual_constructor(
        &mut self,
        syntax: &Expr,
        value: &mut Value,
        expected: Option<&Ty>,
        target: &source_reception::Target,
        frame: &Frame,
    ) {
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            return;
        };
        if application.operands.len() != 1 {
            return;
        }
        let Some(&(event, context)) = self.call_input_source.carriers.get(&value.cause.0) else {
            return;
        };
        if context != self.invocation_context(frame.callable_owner) {
            return;
        }
        let result = (|| {
            let mut work = WorkLimit::new(16384);
            let call = self
                .copy_call_events
                .get(event.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let callee = self
                .application_effect
                .expressions
                .get(
                    call.callee_expression
                        .ok_or(SourceTypesError::MissingNode)?,
                )
                .ok_or(SourceTypesError::MissingNode)?;
            if !call.matches_source(syntax)
                || callee.source_id != application.callee.hir_id
                || !callee.value.sources.is_empty()
            {
                return Err(SourceTypesError::Unresolved);
            }
            let [Callable::Builtin(name)] = callee.value.callables.as_slice() else {
                return Ok(None);
            };
            let Some(constructor) = PayloadConstructor::lookup(name) else {
                return Ok(None);
            };
            let Some(owner) = &target.schema else {
                return Err(SourceTypesError::Unresolved);
            };
            let active = match owner.project_steps(&[constructor.projection()], &mut work) {
                Ok(active) => active,
                Err(SourceTypesError::MissingProjection) => return Ok(None),
                Err(error) => return Err(error),
            };
            let input = self
                .call_input_source
                .supplied
                .get(&event)
                .and_then(|inputs| inputs.get(&0))
                .ok_or(SourceTypesError::MissingNode)?
                .packet
                .clone();
            let input = self.contextual_construction_input(
                application.operands[0]
                    .expression
                    .hir_id
                    .ok_or(SourceTypesError::MissingNode)?,
                &input,
                frame,
                &mut work,
                0,
            )?;
            if !source_construction::receives(&active, &target.environment, &input, &mut work)? {
                return Ok(Some(false));
            }
            let schema = match constructor {
                PayloadConstructor::Some => {
                    SourceSchema::container(SourceContainer::Option, &[active], None, &mut work)?
                }
                PayloadConstructor::Ok | PayloadConstructor::Err => {
                    let other = if constructor == PayloadConstructor::Ok {
                        SourcePath::ResultError
                    } else {
                        SourcePath::ResultSuccess
                    };
                    let inactive = owner.project_steps(&[other], &mut work)?;
                    let arguments = if constructor == PayloadConstructor::Ok {
                        [active, inactive]
                    } else {
                        [inactive, active]
                    };
                    SourceSchema::container(SourceContainer::Result, &arguments, None, &mut work)?
                }
            };
            let source = SourceRef::intern(
                &schema,
                target.environment.clone(),
                self.type_source.storage.live_types_mut(),
                &mut work,
            )?;
            self.call_input_source
                .carrier_sources
                .insert(value.cause.0, source);
            self.attach_result_graph_witness(&schema, value, syntax.span);
            if let Some(expected) = expected {
                value.ty = join_type_holes(&value.ty, expected);
            }
            Ok::<_, SourceTypesError>(Some(true))
        })();
        match result {
            Ok(Some(false)) => self.error(
                "E0301",
                syntax.span,
                "constructor payload does not fit its original receiving Source",
                [value.cause],
            ),
            Ok(_) => {}
            Err(error) => self.unsupported(
                syntax.span,
                format!(
                    "constructor receiving lacks its actual operand and declaration Source: {error}"
                ),
            ),
        }
    }
}
