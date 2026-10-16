use super::*;
#[derive(Clone)]
pub(super) struct WriteEvent {
    origins: Origins,
    slot: Option<Slot>,
    unknown: bool,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Place {
    pub root: BindingId,
    pub path: Vec<Slot>,
}
#[derive(Clone, PartialEq, Eq)]
pub(super) struct Refinement {
    some: bool,
    variant: Option<String>,
    excluded: BTreeSet<String>,
    cause: CauseId,
    storage: Origins,
    slot: Option<Slot>,
    live: bool,
    invalid: Option<&'static str>,
}
impl Refinement {
    pub(super) fn remap_origins(&mut self, moves: &[(NodeId, NodeId)]) {
        for &(recent, older) in moves {
            self.storage.remap(recent, older);
        }
    }
}
impl WriteEvent {
    pub(super) fn remap_origins(&mut self, moves: &[(NodeId, NodeId)]) {
        for &(recent, older) in moves {
            self.origins.remap(recent, older);
        }
    }
}
impl Checker {
    pub(super) fn refine_condition(
        &mut self,
        condition: &Expr,
        truth: bool,
        cause: CauseId,
        frame: &mut Frame,
    ) {
        match &condition.kind {
            ExprKind::Unary { operator, operand } if operator == "!" => {
                self.refine_condition(operand, !truth, cause, frame);
                return;
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if (operator == "&&" && truth) || (operator == "||" && !truth) => {
                self.refine_condition(left, truth, cause, frame);
                self.refine_condition(right, truth, cause, frame);
                return;
            }
            _ => {}
        }
        let mut variant = None;
        let candidate = match &condition.kind {
            ExprKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "==" | "!=") => {
                if is_none(right, frame) {
                    Some((&**left, if operator == "!=" { truth } else { !truth }))
                } else if is_none(left, frame) {
                    Some((&**right, if operator == "!=" { truth } else { !truth }))
                } else {
                    None
                }
            }
            ExprKind::Is { value, pattern } => match &pattern.kind {
                PatternKind::Constructor {
                    path, arguments, ..
                } if standard_tag(path, "Some", frame) => {
                    (truth || arguments.iter().all(payload_covers_all)).then_some((&**value, truth))
                }
                PatternKind::Constructor { path, .. } if standard_tag(path, "None", frame) => {
                    Some((&**value, !truth))
                }
                PatternKind::Constructor {
                    path, arguments, ..
                } if standard_tag(path, "Ok", frame) || standard_tag(path, "Err", frame) => {
                    let tag = if standard_tag(path, "Ok", frame) {
                        "Ok"
                    } else {
                        "Err"
                    };
                    variant = Some((tag.to_owned(), truth));
                    (truth || arguments.iter().all(payload_covers_all)).then_some((&**value, false))
                }
                PatternKind::Constructor {
                    path, arguments, ..
                } if self.constructors.contains_key(&path.join("::")) => {
                    variant = Some((path.join("::"), truth));
                    (truth || arguments.iter().all(payload_covers_all)).then_some((&**value, false))
                }
                _ => None,
            },
            _ => None,
        };
        let Some((expression, some)) = candidate else {
            return;
        };
        let Some(place) = place(expression, frame) else {
            return;
        };
        let mut value = self.bindings[place.root].value.clone();
        let mut storage = Origins::default();
        let mut slot = None;
        let mut live = false;
        if place.path.is_empty() {
            let binding = &self.bindings[place.root];
            live = binding.mode.is_reassignable();
            if let Some(cell) = binding.cell {
                storage = Origins::one(cell);
                slot = Some(Slot::Field("value".into()));
            }
        } else {
            for (index, part) in place.path.iter().enumerate() {
                if index + 1 == place.path.len() {
                    storage = value.origins.clone();
                    slot = Some(part.clone());
                    live = value.publication != Publication::Immutable;
                }
                value = self.project(&value, part.clone(), expression.span, frame, false);
            }
        }
        if variant.is_none()
            && !matches!(
                self.expanded(&value.ty, &mut BTreeSet::new()),
                Ty::Optional(_)
            )
        {
            return;
        }
        let epoch = self
            .read_epochs
            .get(&(
                expression.span.file.0,
                expression.span.start,
                expression.span.end,
                frame.owner.0,
            ))
            .copied()
            .unwrap_or(self.write_events.len())
            .min(self.write_events.len());
        let invalid = if live {
            self.write_events[epoch..].iter().find_map(|event| {
                if event.unknown {
                    Some("E0533")
                } else if !(slot.is_some() && event.slot.is_some() && slot != event.slot)
                    && !self.origins_disjoint(&storage, &event.origins)
                {
                    Some("E0310")
                } else {
                    None
                }
            })
        } else {
            None
        };
        if self
            .refinements
            .get(&place)
            .is_some_and(|old| old.invalid == Some("E0533"))
            && let Ty::Optional(inner) = self.expanded(&value.ty, &mut BTreeSet::new())
            && !inner.scalar()
        {
            self.unsupported(expression.span,"renarrowing a reference payload after an unknown callback requires a heap transfer summary");
        }
        let old = self
            .refinements
            .get(&place)
            .filter(|old| old.invalid.is_none());
        let mut selected = old.and_then(|old| old.variant.clone());
        let mut excluded = old.map(|old| old.excluded.clone()).unwrap_or_default();
        if let Some((tag, truth)) = variant {
            if truth {
                selected = Some(tag);
            } else if matches!(tag.as_str(), "Ok" | "Err")
                && matches!(
                    self.expanded(&value.ty, &mut BTreeSet::new()),
                    Ty::Result(..)
                )
            {
                selected = Some(if tag == "Ok" {
                    "Err".into()
                } else {
                    "Ok".into()
                });
                excluded.insert(tag);
            } else {
                excluded.insert(tag);
                let remaining: Vec<_> = self
                    .constructors
                    .iter()
                    .filter(|(identity, constructor)| {
                        constructor.owner == value.ty && !excluded.contains(*identity)
                    })
                    .map(|(identity, _)| identity.clone())
                    .collect();
                if remaining.len() == 1 {
                    selected = remaining.into_iter().next();
                }
            }
        }
        self.refinements.insert(
            place,
            Refinement {
                some,
                variant: selected,
                excluded,
                cause,
                storage,
                slot,
                live,
                invalid,
            },
        );
    }
    pub(super) fn validate_variant_predicate(
        &mut self,
        expression: &Expr,
        pattern: &Pattern,
        frame: &Frame,
    ) {
        let PatternKind::Constructor { path, .. } = &pattern.kind else {
            return;
        };
        let Some(place) = place(expression, frame) else {
            return;
        };
        let Some(old) = self
            .refinements
            .get(&place)
            .filter(|old| old.invalid.is_none())
            .cloned()
        else {
            return;
        };
        let tag = path.join("::");
        let contradiction = if self.constructors.contains_key(&tag) {
            old.variant.as_ref().is_some_and(|active| active != &tag) || old.excluded.contains(&tag)
        } else if standard_tag(path, "Ok", frame) || standard_tag(path, "Err", frame) {
            let requested = if standard_tag(path, "Ok", frame) {
                "Ok"
            } else {
                "Err"
            };
            old.variant.as_deref().is_some_and(|tag| tag != requested)
                || old.excluded.contains(requested)
        } else if standard_tag(path, "Some", frame) {
            old.variant.is_none() && !old.some
        } else if standard_tag(path, "None", frame) {
            old.variant.is_none() && old.some
        } else {
            false
        };
        if contradiction {
            self.error(
                "E0311",
                pattern.span,
                "constructor predicate contradicts the active refinement",
                [old.cause],
            );
        }
    }
    pub(super) fn narrow_expression(
        &mut self,
        expression: &Expr,
        mut value: Value,
        frame: &mut Frame,
    ) -> Value {
        if self.suppress_refinement > 0 {
            return value;
        }
        let Some(place) = place(expression, frame) else {
            return value;
        };
        let Some(refinement) = self.refinements.get(&place).cloned() else {
            return value;
        };
        if let Some(code) = refinement.invalid {
            self.invalid_refinement_values.insert(value.cause.0, code);
            return value;
        }
        if let Some(tag) = &refinement.variant {
            if matches!(
                self.expanded(&value.ty, &mut BTreeSet::new()),
                Ty::Result(..)
            ) && matches!(tag.as_str(), "Ok" | "Err")
            {
                if value.result_tag.is_some_and(|known| known != (tag == "Ok")) {
                    value.result_payload = None;
                }
                value.result_tag = Some(tag == "Ok");
                value.cause = self.cause(
                    CauseKind::Restriction,
                    expression.span,
                    "dominating Result constructor predicate proves this tag",
                    [value.cause, refinement.cause],
                );
                return value;
            }
            if let Some(constructor) = self.constructors.get(tag).cloned() {
                let payload = if value.variant_tag.as_ref().is_some_and(|known| known != tag) {
                    let mut payload = self.formal_value(
                        constructor.payload,
                        expression.span.start,
                        expression.span,
                        &mut BTreeSet::new(),
                    );
                    payload.permission = payload.permission.meet(value.permission);
                    payload.construction = false;
                    payload
                } else {
                    self.constructor_pattern_payload(&value, tag, expression.span, frame)
                        .unwrap_or_else(|| self.unit(expression.span))
                };
                value.variant_tag = Some(tag.clone());
                value.variant_witnesses.retain(|known, _| known == tag);
                value
                    .variant_witnesses
                    .insert(tag.clone(), Box::new(payload.clone()));
                value.variant_payload = None;
                value.cause = self.cause(
                    CauseKind::Restriction,
                    expression.span,
                    "dominating sum constructor predicate proves the selected payload shape",
                    [value.cause, refinement.cause],
                );
                return value;
            }
        }
        if !refinement.some {
            return value;
        }
        let Ty::Optional(inner) = self.expanded(&value.ty, &mut BTreeSet::new()) else {
            return value;
        };
        let source = value.clone();
        value = source
            .option_payload
            .as_ref()
            .map(|payload| *payload.clone())
            .unwrap_or(source.clone());
        value.ty = *inner;
        value.permission = value.permission.meet(source.permission);
        value.construction &= source.construction;
        value.publication = if value.publication == Publication::Immutable
            || source.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if source.publication == Publication::Live {
            Publication::Live
        } else {
            value.publication
        };
        value.participants = source.participants;
        value.sources = source.sources;
        value.scoped.extend(source.scoped);
        value.temporary |= source.temporary;
        value.marker = source.marker || (source.construction && value.marker);
        value.retention_result =
            source.retention_result || (source.construction && value.retention_result);
        value.through_return |= source.through_return;
        value.cause = self.cause(
            CauseKind::Restriction,
            expression.span,
            "dominating Some branch proves exactly one implicit optional unwrap",
            [source.cause, refinement.cause],
        );
        let unwrap = super::super::ImplicitUnwrap {
            cause: value.cause,
            depth: 1,
            tags: vec!["Some".into()],
        };
        self.invocation_witness(
            frame.callable_owner,
            expression.span,
            super::super::effect_identity::InvocationWitnessKind::ImplicitUnwrap(unwrap.clone()),
        );
        self.implicit_unwraps.insert(
            (
                expression.span.file.0,
                expression.span.start,
                expression.span.end,
            ),
            unwrap,
        );
        value.unsuffixed_numeric = false;
        value
    }
    pub(super) fn merge_refinements(
        &mut self,
        left: &BTreeMap<Place, Refinement>,
        right: &BTreeMap<Place, Refinement>,
        left_never: bool,
        right_never: bool,
    ) {
        self.refinements = if left_never {
            right.clone()
        } else if right_never {
            left.clone()
        } else {
            left.iter()
                .filter_map(|(place, a)| {
                    right
                        .get(place)
                        .filter(|b| a == *b)
                        .map(|_| (place.clone(), a.clone()))
                })
                .collect()
        };
    }
    pub(super) fn invalidate_refinement_access(
        &mut self,
        value: &Value,
        slot: &Option<Slot>,
        unknown: bool,
    ) {
        let affected: Vec<_> = self
            .refinements
            .iter()
            .filter(|(_, refinement)| {
                refinement.live
                    && (unknown
                        || (!(refinement.slot.is_some()
                            && slot.is_some()
                            && refinement.slot != *slot)
                            && !self.origins_disjoint(&refinement.storage, &value.origins)))
            })
            .map(|(place, _)| place.clone())
            .collect();
        for place in affected {
            self.refinements.get_mut(&place).unwrap().invalid =
                Some(if unknown { "E0533" } else { "E0310" });
        }
    }
    pub(super) fn invalidate_unknown_callback_refinements(&mut self) {
        let live: Vec<_> = self
            .bindings
            .iter()
            .filter(|binding| binding.alive && binding.value.publication == Publication::Live)
            .map(|binding| binding.value.clone())
            .collect();
        self.mark_heap_uncertain(&live);
        let live_nodes = self.heap.reachable(
            live.iter()
                .flat_map(|value| value.origins.nodes.iter().copied()),
        );
        let cells: Vec<_> = self
            .bindings
            .iter()
            .filter(|binding| {
                binding.alive
                    && binding.mode.is_reassignable()
                    && self.reference_bearing(&binding.value.ty)
            })
            .filter_map(|binding| binding.cell)
            .collect();
        for cell in cells {
            self.uncertain_slots
                .insert((cell, Slot::Field("value".into())));
        }
        let dummy = Value::scalar(Ty::Unit, None, CauseId(0));
        self.note_refinement_write(&dummy, &None, true);
        self.invalidate_refinement_access(&dummy, &None, true);
        // A callback can change scalar data behind live slots. Never retain a
        // stale scalar constant or constructor tag after that invocation.
        fn forget(value: &mut Value) {
            value.constant = None;
            value.option_identity = None;
            value.condition_inspections = Default::default();
            value.option_tag = None;
            value.result_tag = None;
            value.variant_tag = None;
            if let Some(payload) = &mut value.option_payload {
                forget(payload);
            }
            for payload in [
                &mut value.result_payload,
                &mut value.result_success,
                &mut value.result_error,
                &mut value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values_mut())
            {
                forget(payload);
            }
        }
        for binding in &mut self.bindings {
            if binding.mode.is_reassignable() {
                forget(&mut binding.value);
            }
        }
        for ((node, _), value) in &mut self.fields {
            if live_nodes.contains(node) || value.publication != Publication::Immutable {
                forget(value);
            }
        }
    }
    pub(super) fn widen_repeated_refinements(&mut self) {
        for proof in self.refinements.values_mut() {
            if proof.live {
                proof.invalid = Some("E0533");
            }
        }
    }
    pub(super) fn optional_error_code(&self, value: &Value) -> &'static str {
        self.invalid_refinement_values
            .get(&value.cause.0)
            .copied()
            .unwrap_or("E0310")
    }
    pub(super) fn note_refinement_write(
        &mut self,
        value: &Value,
        slot: &Option<Slot>,
        unknown: bool,
    ) {
        self.write_events.push(WriteEvent {
            origins: value.origins.clone(),
            slot: slot.clone(),
            unknown,
        });
    }
}
fn standard_tag(path: &[String], tag: &str, frame: &Frame) -> bool {
    path == ["Prelude".to_owned(), tag.to_owned()]
        || (path == [tag.to_owned()] && !frame.env.contains_key(tag))
}
fn place(expression: &Expr, frame: &Frame) -> Option<Place> {
    match &expression.kind {
        ExprKind::Name(name) => Some(Place {
            root: *frame.env.get(name)?,
            path: Vec::new(),
        }),
        ExprKind::Field {
            base,
            field,
            safe: false,
        } => {
            let mut value = place(base, frame)?;
            if value.path.len() >= 3 {
                return None;
            }
            value.path.push(
                field
                    .parse()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone())),
            );
            Some(value)
        }
        _ => None,
    }
}
pub(super) fn is_none(expression: &Expr, frame: &Frame) -> bool {
    match &expression.kind {
        ExprKind::Name(name) => {
            name == "Prelude::None" || (name == "None" && !frame.env.contains_key(name))
        }
        ExprKind::Path(path) => standard_tag(path, "None", frame),
        _ => false,
    }
}

fn payload_covers_all(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Name(_) => true,
        PatternKind::Tuple(items) => items.iter().all(payload_covers_all),
        PatternKind::Record { fields, .. } => fields
            .iter()
            .all(|field| payload_covers_all(&field.pattern)),
        PatternKind::Alternative(items) => items.iter().any(payload_covers_all),
        _ => false,
    }
}
