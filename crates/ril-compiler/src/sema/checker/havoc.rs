use super::*;
impl Checker {
    pub(super) fn widen_callable_environment(&mut self, callable: &Callable) {
        let environment = match callable {
            Callable::Named(id) => self.functions[*id].lexical.clone(),
            Callable::Closure(id) => self.closures[*id].lexical.clone(),
            _ => return,
        };
        self.widen_definition_environment(&environment);
    }
    /// A declaration contract holds after any lawful use of its mutable
    /// environment, rather than only in the module's initialization state.
    pub(super) fn widen_definition_environment(&mut self, environment: &Env) {
        let selected: BTreeSet<_> = environment
            .values()
            .copied()
            .filter(|id| {
                let binding = &self.bindings[*id];
                binding.alive
                    && (binding.mode.is_reassignable()
                        || binding.value.publication == Publication::Live)
            })
            .collect();
        let values: Vec<_> = selected
            .iter()
            .map(|id| self.bindings[*id].value.clone())
            .collect();
        let reachable = self.heap.reachable(
            values
                .iter()
                .flat_map(|value| value.origins.nodes.iter().copied()),
        );
        self.mark_heap_uncertain(&values);
        for id in selected {
            if self.bindings[id].mode.is_reassignable() {
                if self.reference_bearing(&self.bindings[id].value.ty)
                    && let Some(cell) = self.bindings[id].cell
                {
                    self.uncertain_slots
                        .insert((cell, Slot::Field("value".into())));
                }
                forget_runtime_state(&mut self.bindings[id].value);
            }
        }
        for ((node, _), value) in &mut self.fields {
            if reachable.contains(node) {
                forget_runtime_state(value);
            }
        }
        self.refinements
            .retain(|place, _| !environment.values().any(|id| *id == place.root));
    }
    pub(super) fn mark_heap_uncertain(&mut self, values: &[Value]) {
        let live: BTreeSet<_> = values
            .iter()
            .flat_map(|value| self.heap.reachable(value.origins.nodes.iter().copied()))
            .collect();
        let mut typed: Vec<_> = values
            .iter()
            .flat_map(|value| {
                value
                    .origins
                    .nodes
                    .iter()
                    .map(move |node| (*node, value.ty.clone()))
            })
            .collect();
        typed.extend(
            self.fields
                .iter()
                .filter(|((parent, _), _)| live.contains(parent))
                .flat_map(|(_, value)| {
                    value
                        .origins
                        .nodes
                        .iter()
                        .map(move |node| (*node, value.ty.clone()))
                }),
        );
        for (node, ty) in typed {
            self.invalidate_opaque_collection_members(node);
            if matches!(self.expanded(&ty, &mut BTreeSet::new()), Ty::Array(_)) {
                // Fixed cardinality is a storage-type invariant, not an
                // observed element value. A lawful alias cannot resize that
                // storage; concrete length-changing calls remain rejected by
                // invalidate_array_length even through a dynamic view.
                // Contents and reachable aliases still become uncertain.
                if !self.fixed_arrays.contains(&node) {
                    self.array_lengths.insert(node, None);
                }
            }
            match self.expanded(&ty, &mut BTreeSet::new()) {
                Ty::Array(element) | Ty::Set(element) if self.reference_bearing(&element) => {
                    self.uncertain_slots.insert((node, Slot::AnyIndex));
                }
                Ty::Map(_, element) if self.reference_bearing(&element) => {
                    self.uncertain_slots.insert((node, Slot::AnyIndex));
                }
                Ty::Record(fields) => {
                    for (name, (mutable, ty)) in fields {
                        if mutable && self.reference_bearing(&ty) {
                            self.uncertain_slots.insert((node, Slot::Field(name)));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    pub(super) fn reference_bearing(&self, ty: &Ty) -> bool {
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Optional(inner) | Ty::Immutable(inner) => self.reference_bearing(&inner),
            Ty::Result(..) => true,
            ty if ty.scalar() => false,
            ty => self.constructor_scalar_type(&ty) != Some(true),
        }
    }
    pub(super) fn check_deep_uncertainty(&mut self, value: &Value, span: Span) {
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        if self
            .uncertain_slots
            .iter()
            .any(|(node, _)| reachable.contains(node))
        {
            self.unsupported(
                span,
                "deep traversal after an unknown heap write requires a heap transfer summary",
            );
        }
    }
}

fn forget_runtime_state(value: &mut Value) {
    value.constant = None;
    value.option_identity = None;
    value.condition_inspections = Default::default();
    value.option_tag = None;
    value.result_tag = None;
    value.variant_tag = None;
    value.origins.choices.clear();
    for payload in [
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        forget_runtime_state(payload);
    }
}

#[cfg(test)]
mod optional_tests {
    use super::*;
    #[test]
    fn unknown_writes_forget_tag_and_boolean_evidence_but_keep_detached_copies() {
        for callback in [false, true] {
            let mut checker = Checker::new(FileId(0));
            let span = Span {
                file: FileId(0),
                start: 0,
                end: 1,
            };
            let mut frame = checker.frame(BTreeMap::new(), false);
            let optional = checker.formal_value(
                Ty::Optional(Box::new(Ty::Int("int".into()))),
                0,
                span,
                &mut BTreeSet::new(),
            );
            let original = optional.option_identity.unwrap();
            let changing = checker.bind_name(
                "changing",
                BindingMode::Var,
                optional.clone(),
                span,
                &mut frame,
                false,
            );
            let detached = checker.bind_name(
                "detached",
                BindingMode::Let,
                optional,
                span,
                &mut frame,
                false,
            );
            let cause = checker.cause(CauseKind::Source, span, "stored boolean observation", []);
            let mut boolean = Value::scalar(Ty::Bool, None, cause);
            boolean.condition_inspections.when_true.insert(17);
            boolean.condition_inspections.versions.insert(17, 3);
            let changed_boolean = checker.bind_name(
                "changed_boolean",
                BindingMode::Var,
                boolean.clone(),
                span,
                &mut frame,
                false,
            );
            let detached_boolean = checker.bind_name(
                "detached_boolean",
                BindingMode::Let,
                boolean,
                span,
                &mut frame,
                false,
            );
            if callback {
                checker.invalidate_unknown_callback_refinements();
            } else {
                checker.widen_definition_environment(&frame.env);
            }
            assert_eq!(checker.bindings[changing].value.option_identity, None);
            assert_eq!(
                checker.bindings[detached].value.option_identity,
                Some(original)
            );
            assert!(
                checker.bindings[changed_boolean]
                    .value
                    .condition_inspections
                    .when_true
                    .is_empty()
            );
            assert_eq!(
                checker.bindings[detached_boolean]
                    .value
                    .condition_inspections
                    .when_true,
                [17].into()
            );
        }
    }
}
