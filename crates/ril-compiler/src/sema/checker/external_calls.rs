//! The trusted foreign contract supplies immutable inputs and temporary callback
//! invocation, never an actual callback's effects, authority or Result inspection.
use super::*;

impl Checker {
    pub(super) fn invoke_foreign_targets(
        &mut self,
        callee: &Value,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let before = self.snapshot_flow();
        let mut alternative: Option<(Value, flow::FlowSnapshot)> = None;
        for callable in &callee.callables {
            self.restore_definition_state(&before);
            let mut target = callee.clone();
            target.callables = vec![callable.clone()];
            let value = self.invoke(&target, args.clone(), span, frame);
            let value = if let Some((previous, state)) = alternative {
                self.branch_flow(&before, &state, &previous, &value, span)
            } else {
                value
            };
            alternative = Some((value, self.snapshot_flow()));
        }
        alternative
            .expect("multi-target invocation contains a target")
            .0
    }
    pub(super) fn external_formal_value(
        &mut self,
        ty: Ty,
        index: u32,
        syntax: Option<&TypeExpr>,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        self.check_external_result_shape(&ty, false, span, &mut BTreeSet::new());
        let mut value = self.formal_value(ty, index, span, &mut BTreeSet::new());
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        for ((node, _), field) in &self.fields {
            if reachable.contains(node) {
                value.results.extend(&field.results);
                value.must_results.extend(&field.must_results);
            }
        }
        // Reception is an actual transition from the outside producer. Keep
        // its immutable creation owner and record the received carrier.
        self.transfer_results(&value, ScopeId(u32::MAX), frame.owner);
        for ((node, _), field) in &mut self.fields {
            if reachable.contains(node) {
                freeze_formal_value(field);
            }
        }
        freeze_formal_value(&mut value);
        if let Some(syntax) = syntax {
            self.promise_array_shape(&value, syntax, frame);
        }
        value.cause = self.cause(
            CauseKind::Source,
            span,
            "foreign ordinary exchange contract supplies immutable data without freshness",
            [value.cause],
        );
        value
    }

    pub(super) fn check_external_result_shape(
        &mut self,
        ty: &Ty,
        conditional: bool,
        span: Span,
        seen: &mut BTreeSet<(String, bool)>,
    ) {
        if !seen.insert((format!("{ty:?}"), conditional)) {
            return;
        }
        match self.representation_graph_type(ty) {
            Ty::Result(ok, error) => {
                if conditional {
                    self.unsupported(span, "foreign nested Result production requires a conditional or multiplicity-aware inspection contract");
                }
                self.check_external_result_shape(&ok, true, span, seen);
                self.check_external_result_shape(&error, true, span, seen);
            }
            Ty::Immutable(inner) => {
                self.check_external_result_shape(&inner, conditional, span, seen)
            }
            Ty::Optional(inner) | Ty::Array(inner) | Ty::Set(inner) => {
                self.check_external_result_shape(&inner, true, span, seen)
            }
            Ty::Map(key, value) => {
                self.check_external_result_shape(&key, true, span, seen);
                self.check_external_result_shape(&value, true, span, seen);
            }
            Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                for (_, field) in fields.values() {
                    self.check_external_result_shape(field, conditional, span, seen);
                }
            }
            Ty::Tuple(items) => {
                for item in items {
                    self.check_external_result_shape(&item, conditional, span, seen);
                }
            }
            shape @ (Ty::Named(_) | Ty::Applied { .. }) => {
                let (name, arguments) = match &shape {
                    Ty::Named(name) => (name, vec![]),
                    Ty::Applied {
                        constructor,
                        arguments,
                    } => (constructor, arguments.clone()),
                    _ => unreachable!(),
                };
                if let Some(declaration) = self.types.get(name)
                    && declaration.opaque
                    && !declaration.nominal
                    && let Some(syntax) = &declaration.value
                {
                    let substitutions = declaration
                        .generics
                        .iter()
                        .zip(arguments)
                        .map(|(parameter, argument)| (parameter.name.clone(), argument))
                        .collect();
                    let representation =
                        self.ty_substituted(syntax, &mut BTreeSet::new(), &substitutions);
                    // An opaque external value cannot expose an inner duty to
                    // ordinary pattern inspection through its public type.
                    self.check_external_result_shape(&representation, true, span, seen);
                }
                let expanded = self.expanded(&shape, &mut BTreeSet::new());
                if expanded != shape {
                    self.check_external_result_shape(&expanded, conditional, span, seen);
                }
                let constructors: Vec<_> = self
                    .constructors
                    .values()
                    .filter(|constructor| constructor.owner == shape && constructor.has_payload)
                    .cloned()
                    .collect();
                for constructor in constructors {
                    self.check_external_result_shape(
                        &constructor.payload,
                        conditional || !constructor.nominal,
                        span,
                        seen,
                    );
                }
            }
            _ => {}
        }
    }

    fn check_external_exchange(&mut self, value: &Value, span: Span) {
        self.check_deep_uncertainty(value, span);
        if self.contains_callable(value) || !self.resource_free(value) || !value.scoped.is_empty() {
            self.unsupported(span, "external ordinary exchange cannot carry callable or scoped resource authority without a listed contract");
        } else if !self.construction_can_publish(value) {
            self.error("E0908", span, "external ordinary exchange requires deeply immutable data; a live view or surviving writer cannot cross this boundary", [value.cause]);
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        let duties = value.results.iter().copied().chain(
            self.fields
                .iter()
                .filter(|((node, _), _)| reachable.contains(node))
                .flat_map(|(_, field)| field.results.iter().copied()),
        );
        if self
            .result_family_closure(duties)
            .iter()
            .any(|id| !self.result_duties[*id as usize].inspected)
        {
            self.unsupported(span, "external exchange of an uninspected Result requires an explicit receiving inspection contract");
        }
    }

    fn external_callable_syntax(&self, syntax: &TypeExpr) -> Option<TypeExpr> {
        let mut syntax = syntax.clone();
        let mut seen = BTreeSet::new();
        loop {
            match &syntax.kind {
                TypeKind::Callable { .. } => return Some(syntax),
                TypeKind::Name { path, arguments } => {
                    let name = path.join("::");
                    if !seen.insert(name.clone()) {
                        return None;
                    }
                    let declaration = self.types.get(&name)?;
                    if declaration.nominal || declaration.opaque || !declaration.variants.is_empty()
                    {
                        return None;
                    }
                    syntax = if declaration.generics.is_empty() {
                        declaration.value.clone()?
                    } else {
                        let mut template = declaration.clone();
                        template.nominal = true;
                        crate::static_eval::normalize_constructor_arguments(
                            &template,
                            arguments,
                            &self.types,
                            self.layout,
                        )
                        .ok()?
                        .payloads
                        .remove(&name)??
                    };
                }
                _ => return None,
            }
        }
    }

    pub(super) fn check_external_invocation(
        &mut self,
        function: &Function,
        arguments: &[Value],
        received: &[Value],
        span: Span,
        frame: &mut Frame,
    ) {
        for (index, parameter) in function.parameters.iter().enumerate() {
            let Some(actual) = received.get(index) else {
                continue;
            };
            let callback = parameter
                .ty
                .as_ref()
                .and_then(|syntax| self.external_callable_syntax(syntax));
            let Some(callback) = callback else {
                let original = arguments.get(index).unwrap_or(actual);
                self.check_external_exchange(original, span);
                continue;
            };
            let TypeKind::Callable {
                parameters, result, ..
            } = &callback.kind
            else {
                unreachable!()
            };
            if parameters
                .iter()
                .any(|parameter| parameter.mode != ParameterMode::Read)
            {
                self.error("E0908", parameter.span, "a foreign callback cannot receive mutable ordinary data without a listed resource contract", [actual.cause]);
                continue;
            }
            // The implementation may call each supplied callback zero or many
            // times, in any order. Widen changing scalars before the arbitrary
            // invocation; retained graph/authority changes still need a proof.
            if actual.callables.is_empty() {
                self.error(
                    "E0338",
                    span,
                    "foreign callback value has no callable target",
                    [actual.cause],
                );
                continue;
            }
            // A joined callback value denotes alternatives, not a guaranteed
            // sequence of all targets. Give every target its own zero-or-more
            // transition and retain the union after each proved transition.
            for callable in &actual.callables {
                let mut target = actual.clone();
                target.callables = vec![callable.clone()];
                let before = self.snapshot_flow();
                let family = self.begin_loop_results(frame.owner);
                let mut invocation = Vec::new();
                for (position, parameter) in parameters.iter().enumerate() {
                    let ty = parameter
                        .ty
                        .as_ref()
                        .map(|syntax| self.ty(syntax))
                        .unwrap_or(Ty::Unknown);
                    let input = self.external_formal_value(
                        ty,
                        position as u32,
                        parameter.ty.as_ref(),
                        parameter.span,
                        frame,
                    );
                    invocation.push((ParameterMode::Read, input, parameter.span));
                }
                let repeated = self.begin_repeated_callback(&mut invocation, frame);
                let exit_epoch = self.explanations.causes.len() as u32;
                self.foreign_callback_depth += 1;
                let output = self.invoke(&target, invocation, span, frame);
                self.foreign_callback_depth -= 1;
                let exits = self.finish_foreign_callback_exits(exit_epoch, &before);
                if output.ty == Ty::Never
                    && self.pending_abort.is_some()
                    && self.can_record_foreign_abort(span)
                {
                    self.finish_single_callback_results(family, span);
                    self.record_foreign_abort(&before, frame, span);
                    self.finish_aborted_repeated_callback(repeated, span);
                    continue;
                }
                if output.ty == Ty::Never && !exits.is_empty() {
                    self.finish_single_callback_results(family, span);
                    let retained = self.foreign_abort_exits.clone();
                    self.restore_definition_state(&before);
                    self.include_foreign_exit_states(&retained);
                    self.finish_aborted_repeated_callback(repeated, span);
                    continue;
                }
                if output.ty != Ty::Never {
                    let expected = result
                        .as_ref()
                        .map(|syntax| self.ty(syntax))
                        .unwrap_or(Ty::Unit);
                    self.require_type(&output, &expected, span);
                    if let Some(syntax) = result {
                        self.check_storage_shape(&output, syntax, frame);
                    }
                    self.check_external_exchange(&output, span);
                }
                let mut iteration = self.unit(span);
                // Closing inspected Result families removes bookkeeping IDs
                // from carriers; compare the actual heap before that cleanup.
                self.finish_repeated_callback_with_exits(repeated, span, &exits);
                self.finish_loop_results(
                    family,
                    &mut iteration,
                    frame,
                    span,
                    &Block {
                        statements: vec![],
                        where_items: vec![],
                        span,
                    },
                );
                let executed = if output.ty == Ty::Never {
                    output
                } else {
                    iteration.clone()
                };
                self.conditional_flow(&before, &iteration, &executed, None, span);
            }
        }
    }
}
