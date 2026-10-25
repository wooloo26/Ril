use super::super::recursive::{self, Port, ReturnValue, ScalarKind};
use super::*;
impl Checker {
    pub(super) fn instantiate_recursive(
        &mut self,
        id: usize,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        caller: &mut Frame,
        verifying: bool,
        callback_epoch: usize,
    ) -> Option<Value> {
        let info = self.functions[id].clone();
        let summary = self
            .recursive_analysis
            .summaries
            .get(&info.definition)?
            .clone();
        if !summary.complete || !summary.productive {
            self.unsupported(
                span,
                summary.reason.unwrap_or_else(|| {
                    "recursive dependency has no established normal-return relation".into()
                }),
            );
            return None;
        }
        let mut frame = self.frame(info.lexical.clone(), false);
        frame.definition = Some(info.definition);
        frame.callable_owner = Some(CallableOwner::Function(info.definition));
        if let Some(&invocation) = self.copy_invocation_stack.last() {
            self.scopes.set_origin(
                frame.owner,
                crate::sema::scopes::ScopeOrigin::Named(invocation),
            );
        }
        self.scopes.set_parent(frame.owner, caller.owner);
        let mut inputs = Vec::new();
        let mut loans = BTreeMap::new();
        for (index, parameter) in info.syntax.parameters.iter().enumerate() {
            let (_, mut value, arg_span) = args.get(index)?.clone();
            if let Some(ty) = &parameter.ty {
                let ty = self.ty(ty);
                self.require_type(&value, &ty, arg_span);
            }
            let sources = value.sources.clone();
            if parameter.mode == ParameterMode::Read {
                value.permission = Permission::Read;
                value.construction = false;
            } else {
                if value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        arg_span,
                        "recursive mutable argument lacks write authority",
                        [value.cause],
                    );
                }
                if parameter.mode == ParameterMode::SharedMut && value.temporary {
                    self.unsupported(
                        arg_span,
                        "recursive retained argument cannot extend a temporary loan",
                    );
                }
                let loan = LoanId(self.next_loan);
                self.next_loan += 1;
                self.loan_parents.insert(loan, value.participants.clone());
                loans.insert(loan, value.participants.clone());
                self.start_invocation_loan(
                    loan,
                    &value,
                    &frame,
                    index,
                    parameter.mode == ParameterMode::SharedMut,
                    arg_span,
                );
                value.participants = [Participant::Loan(loan)].into();
                value.temporary |= parameter.mode == ParameterMode::Mut;
            }
            let start = frame.locals.len();
            self.bind_pattern(
                &parameter.pattern,
                if parameter.mode == ParameterMode::Read {
                    BindingMode::Let
                } else {
                    BindingMode::LetMut
                },
                value.clone(),
                &mut frame,
                true,
            );
            for &binding in &frame.locals[start..] {
                self.bindings[binding].forwarded = sources.clone();
                if let PatternKind::Name(_) = parameter.pattern.kind {
                    value = self.bindings[binding].value.clone();
                }
            }
            inputs.push((parameter.mode, value, arg_span));
        }
        for access in &summary.accesses {
            let value = self.recursive_port(&access.port, &inputs, span, &mut frame)?;
            self.access(
                &value,
                access.slot.clone(),
                recursive_mode(access.access),
                span,
                &mut frame,
            );
            if access.access == super::super::summary::Access::Retain {
                frame.obligations.retention = true;
            }
        }
        for input in &summary.equality_inputs {
            let value = self.recursive_return(input, &inputs, span, &mut frame)?;
            self.deep_read(&value, span, &mut frame);
            self.check_structural_equality(&[&value], span);
        }
        for (name, access) in &summary.named {
            let binding = if info.owner.is_some() {
                caller.env.get(name)
            } else {
                info.lexical.get(name)
            }
            .copied();
            let Some(binding) = binding else {
                self.unsupported(
                    span,
                    "recursive named source could not be anchored to its lexical binding",
                );
                return None;
            };
            let mode = recursive_mode(*access);
            frame.obligations.named.insert(binding, mode);
            frame.obligations.concrete.insert(binding, mode);
            let binding_info = &self.bindings[binding];
            let mut value = binding_info.value.clone();
            if let Some(cell) = binding_info.cell {
                value.origins = Origins::one(cell);
            }
            frame.obligations.accesses.push(AccessFact {
                observed_recency: self.recency_moves.len(),
                recency: self.recency_moves.len(),
                origin_owners: self.access_owners(&value.origins),
                origins: value.origins,
                slot: None,
                mode,
                participants: value.participants,
                cause: value.cause,
                span,
            });
            if mode != Mode::Read {
                self.mark_write(binding);
            }
        }
        frame
            .obligations
            .effects
            .extend(summary.effects.iter().cloned());
        frame
            .obligations
            .concrete_effects
            .extend(summary.effects.iter().cloned());
        for callback in &summary.callbacks {
            let callback_value = self.recursive_port(
                &Port {
                    parameter: callback.parameter,
                    path: callback.path.clone(),
                },
                &inputs,
                span,
                &mut frame,
            )?;
            if !callback.arguments.is_empty() {
                self.unsupported(span, "recursive callback argument-port instantiation");
                return None;
            }
            let _ = self.invoke_generated_values(&callback_value, vec![], span, &mut frame);
        }
        let mut result = self.recursive_return(&summary.return_value, &inputs, span, &mut frame)?;
        let returned = self.heap.reachable(result.origins.nodes.iter().copied());
        for (index, parameter) in info.syntax.parameters.iter().enumerate() {
            if parameter.mode == ParameterMode::SharedMut
                && !returned.is_disjoint(&inputs[index].1.origins.nodes)
            {
                frame.obligations.retention = true;
                result.retention_result = true;
                for source in &inputs[index].1.sources {
                    self.mark_write(*source);
                }
            }
        }
        for access in &mut frame.obligations.accesses {
            access.transport(&self.recency_moves);
        }
        self.check_exclusivity(&frame.obligations.accesses, span);
        self.check_annotations(
            &info.syntax,
            &frame,
            info.owner,
            if verifying {
                super::calls::AnnotationCheck::Declaration
            } else {
                super::calls::AnnotationCheck::Invocation
            },
        );
        let invocation = self.invocation_summary(id, &frame, &returned);
        self.record_effect_invocation(&info, span, &invocation, verifying, callback_epoch);
        let summary = self.retain_invocation_summary(invocation);
        self.end_invocation_loans(&mut result, &frame, &loans, span);
        self.completed_invocation = Some(super::contracts::CompletedInvocation::Recorded(summary));
        for &binding in &frame.locals {
            self.check_authority_use(binding);
            self.bindings[binding].alive = false;
        }
        let forwarded_callback = args.iter().any(|(_, value, _)| {
            value
                .callback_parameters
                .iter()
                .any(|binding| self.bindings[*binding].owner == caller.owner)
        });
        for (&binding, &mode) in &frame.obligations.named {
            if self.bindings[binding].owner != caller.owner {
                caller
                    .obligations
                    .named
                    .entry(binding)
                    .and_modify(|old| *old = (*old).max(mode))
                    .or_insert(mode);
                if !caller.callback_call
                    && (!forwarded_callback || frame.obligations.concrete.contains_key(&binding))
                {
                    caller
                        .obligations
                        .concrete
                        .entry(binding)
                        .and_modify(|old| *old = (*old).max(mode))
                        .or_insert(mode);
                }
            }
        }
        if !caller.callback_call {
            caller.obligations.concrete_effects.extend(
                if forwarded_callback {
                    frame.obligations.concrete_effects.iter()
                } else {
                    frame.obligations.effects.iter()
                }
                .cloned(),
            );
        }
        caller.obligations.handler_environment |= frame.obligations.handler_environment;
        caller
            .obligations
            .copy_boundaries
            .extend(&frame.obligations.copy_boundaries);
        caller
            .obligations
            .selected_handlers
            .extend(frame.obligations.selected_handlers);
        caller
            .obligations
            .performed_operations
            .extend(frame.obligations.performed_operations);
        caller.obligations.effects.extend(frame.obligations.effects);
        caller.obligations.symbolic |= frame.obligations.symbolic;
        for mut access in frame.obligations.accesses {
            access.participants = normalize_participants(&access.participants, &loans);
            caller.obligations.accesses.push(access);
        }
        for (_, value, _) in args {
            for source in &value.sources {
                if self.bindings[*source].parameter && self.bindings[*source].write_used {
                    caller.obligations.parameter_write = true;
                }
            }
        }
        result.participants = normalize_participants(&result.participants, &loans);
        result.sources.clear();
        result.through_return = true;
        result.cause = self.cause(
            CauseKind::Call,
            span,
            "instantiate a productive recursive fixed-point summary",
            [result.cause],
        );
        Some(result)
    }
    fn recursive_port(
        &mut self,
        port: &Port,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let mut value = args.get(port.parameter as usize)?.1.clone();
        for slot in &port.path {
            value = self.project(&value, slot.clone(), span, frame, false);
        }
        Some(value)
    }
    fn recursive_return(
        &mut self,
        term: &ReturnValue,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        match term {
            ReturnValue::Bottom | ReturnValue::Unknown => None,
            ReturnValue::Unit => Some(self.unit(span)),
            ReturnValue::Scalar(kind) => {
                let ty = match kind {
                    ScalarKind::Bool => Ty::Bool,
                    ScalarKind::Integer => Ty::Int("int".into()),
                    ScalarKind::Float => Ty::Float("f64".into()),
                    ScalarKind::String => Ty::Str,
                    ScalarKind::Bytes => Ty::Bytes,
                };
                let cause = self.cause(
                    CauseKind::Call,
                    span,
                    "recursive scalar result has no reference authority",
                    [],
                );
                Some(Value::scalar(ty, None, cause))
            }
            ReturnValue::Parameter { port, permission } => {
                let mut value = self.recursive_port(port, args, span, frame)?;
                value.permission = value.permission.meet(*permission);
                value.construction = false;
                if value.permission == Permission::Write {
                    value.marker = true;
                }
                Some(value)
            }
            ReturnValue::Global {
                name,
                path,
                permission,
            } => {
                let binding = *frame.env.get(name)?;
                let mut value = self.bindings[binding].value.clone();
                for slot in path {
                    value = self.project(&value, slot.clone(), span, frame, false);
                }
                value.permission = value.permission.meet(*permission);
                value.construction = false;
                Some(value)
            }
            ReturnValue::Clone {
                source,
                site,
                immutable,
                reception,
            } => {
                let source = self.recursive_port(source, args, span, frame)?;
                if matches!(self.expanded(&source.ty,&mut BTreeSet::new()),Ty::Applied{ref constructor,..} if constructor=="Channel::Sender")
                {
                    self.unsupported(recursive::site_span(*site),"recursive Sender cloning requires a resource-specific invocation and lifetime fixed point");
                    return None;
                }
                let mut value =
                    self.clone_value(&source, recursive::site_span(*site), frame, *immutable);
                apply_reception(&mut value, *reception);
                Some(value)
            }
            ReturnValue::Tuple {
                site,
                items,
                reception,
            } => {
                let values = items
                    .iter()
                    .map(|item| self.recursive_return(item, args, span, frame))
                    .collect::<Option<Vec<_>>>()?;
                let node = self.allocate_owned(recursive::site_span(*site), 0, frame.owner);
                let mut value = Value::reference(
                    Ty::Tuple(values.iter().map(|v| v.ty.clone()).collect()),
                    node,
                    self.heap.nodes[node.0 as usize].cause,
                );
                for (index, child) in values.into_iter().enumerate() {
                    value.scoped.extend(&child.scoped);
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    value.mutable_environment |= child.mutable_environment;
                    value.observer_environment |= child.observer_environment;
                    self.store_field(node, Slot::Tuple(index as u32), child);
                }
                apply_reception(&mut value, *reception);
                Some(value)
            }
            ReturnValue::Record {
                site,
                type_name,
                fields,
                field_modes,
                reception,
            } => {
                let mut values = BTreeMap::new();
                for (name, item) in fields {
                    values.insert(
                        name.clone(),
                        self.recursive_return(item, args, span, frame)?,
                    );
                }
                let ty = type_name
                    .as_ref()
                    .map(|name| Ty::Named(name.clone()))
                    .unwrap_or_else(|| {
                        Ty::Record(
                            values
                                .iter()
                                .map(|(name, value)| {
                                    (
                                        name.clone(),
                                        (
                                            field_modes.get(name).copied().unwrap_or(false),
                                            value.ty.clone(),
                                        ),
                                    )
                                })
                                .collect(),
                        )
                    });
                let node = self.allocate_owned(recursive::site_span(*site), 0, frame.owner);
                let mut value = Value::reference(ty, node, self.heap.nodes[node.0 as usize].cause);
                for (name, child) in values {
                    value.scoped.extend(&child.scoped);
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    self.store_field(node, Slot::Field(name), child);
                }
                apply_reception(&mut value, *reception);
                Some(value)
            }
            ReturnValue::Alternatives(alternatives) => {
                let mut values = alternatives
                    .iter()
                    .map(|alternative| self.recursive_return(alternative, args, span, frame))
                    .collect::<Option<Vec<_>>>()?
                    .into_iter();
                let mut value = values.next()?;
                for other in values {
                    let cause = self.cause(
                        CauseKind::BranchJoin,
                        span,
                        "whole recursive return alternatives preserve output correlations",
                        [value.cause, other.cause],
                    );
                    value = value.join(&other, self.choice(), cause);
                }
                Some(value)
            }
        }
    }
}
fn recursive_mode(mode: super::super::summary::Access) -> Mode {
    match mode {
        super::super::summary::Access::Read => Mode::Read,
        super::super::summary::Access::Write => Mode::Write,
        super::super::summary::Access::Retain => Mode::Retain,
    }
}
pub(super) fn normalize_participants(
    participants: &BTreeSet<Participant>,
    loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
) -> BTreeSet<Participant> {
    let mut result = BTreeSet::new();
    for participant in participants {
        if let Participant::Loan(loan) = participant
            && let Some(parents) = loans.get(loan)
        {
            result.extend(parents);
        } else {
            result.insert(*participant);
        }
    }
    result
}

fn apply_reception(value: &mut Value, reception: recursive::Reception) {
    match reception {
        recursive::Reception::Construction => {}
        recursive::Reception::Immutable => {
            value.permission = Permission::Read;
            value.publication = Publication::Immutable;
            value.construction = false;
        }
        recursive::Reception::Readonly => {
            value.permission = Permission::Read;
            value.publication = Publication::Live;
            value.construction = false;
        }
    }
}
