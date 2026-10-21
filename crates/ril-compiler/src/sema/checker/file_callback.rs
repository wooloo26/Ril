use super::*;
#[derive(Clone, Copy)]
enum ResourceBoundary {
    File,
    Child,
}
impl Checker {
    pub(super) fn file_with_callback(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        self.with_resource_callback(args, span, frame, ResourceBoundary::File)
    }
    pub(super) fn process_with_callback(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        self.with_resource_callback(args, span, frame, ResourceBoundary::Child)
    }
    fn with_resource_callback(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
        boundary: ResourceBoundary,
    ) -> Value {
        let child = matches!(boundary, ResourceBoundary::Child);
        let action_index = if child { 1 } else { 2 };
        if args.len() != action_index + 1 {
            self.error(
                "E0314",
                span,
                "resource boundary argument count mismatch",
                [],
            );
            return self.unit(span);
        }
        let error_path = if child {
            vec!["Process".into(), "ProcessError".into()]
        } else {
            vec!["Io".into(), "IoError".into()]
        };
        let error = self.ty(&TypeExpr {
            hir_id: None,
            text: if child {
                "Process::ProcessError".into()
            } else {
                "Io::IoError".into()
            },
            kind: TypeKind::Name {
                path: error_path,
                arguments: vec![],
            },
            span,
        });
        let inputs = if child {
            vec![
                self.ty(&TypeExpr {
                    hir_id: None,
                    text: "Process::Command".into(),
                    kind: TypeKind::Name {
                        path: vec!["Process".into(), "Command".into()],
                        arguments: vec![],
                    },
                    span,
                }),
                args[action_index].1.ty.clone(),
            ]
        } else {
            vec![
                Ty::Named("Path::Path".into()),
                Ty::Named("File::OpenMode".into()),
                args[action_index].1.ty.clone(),
            ]
        };
        for ((mode, value, argument_span), expected) in args.iter().zip(inputs) {
            if *mode != ParameterMode::Read {
                self.error(
                    "E0405",
                    *argument_span,
                    "with_file arguments use read reception",
                    [value.cause],
                );
            }
            self.require_type(value, &expected, *argument_span);
        }
        let mut action = args[action_index].1.clone();
        action.permission = Permission::Read;
        if action.ty == Ty::Unknown
            && action
                .callables
                .iter()
                .any(|callable| matches!(callable, Callable::Builtin(_)))
        {
            self.unsupported(
                args[action_index].2,
                "with_file builtin action requires a complete checked callable signature",
            );
        }
        if let Some(parameters) = &action.signature
            && (parameters.len() != 1 || parameters[0].mode != ParameterMode::Mut)
        {
            self.error(
                "E0407",
                args[action_index].2,
                "with_file action must receive exactly one temporary mutable Handle",
                [action.cause],
            );
        }
        frame.obligations.effects.insert("Fiber".into());
        frame.obligations.concrete_effects.insert("Fiber".into());
        let mut helper = self.frame(frame.env.clone(), true);
        self.scopes.set_parent(helper.owner, frame.owner);
        let node = self.allocate(span, if child { 0xC11D } else { 0xF11E }, helper.owner);
        let handle = Value::reference(
            Ty::Named(if child {
                "Process::Child".into()
            } else {
                "File::Handle".into()
            }),
            node,
            self.heap.nodes[node.0 as usize].cause,
        );
        let lease = self.bind_name(
            if child {
                "ril__with_child_lease"
            } else {
                "ril__with_file_lease"
            },
            if child {
                BindingMode::LetMut
            } else {
                BindingMode::ScopedMut
            },
            handle,
            span,
            &mut helper,
            false,
        );
        if child {
            self.bindings[lease].value.scoped.insert(lease);
        }
        let mut borrowed = self.bindings[lease].value.clone();
        borrowed.temporary = true;
        let cause = self.cause(
            CauseKind::Source,
            span,
            "with_file returns one Result after opening, one callback and closing",
            [action.cause],
        );
        // The public result exists on the open-failure path too, before any
        // callback producer. It is distinct from each nested callback Result.
        let prototype = self.make_result(
            true,
            Value::scalar(Ty::Unknown, None, cause),
            span,
            frame.owner,
        );
        let open_error = self.standard_value(error.clone(), span, helper.owner, 0xF11F);
        let skipped = self.file_result_branch(false, open_error, &prototype, span);
        let before = self.snapshot_flow();
        let mut response = self.invoke(
            &action,
            vec![(ParameterMode::Mut, borrowed, span)],
            span,
            &mut helper,
        );
        let executed = if response.ty == Ty::Never {
            response.clone()
        } else if let Ty::Result(ok, actual_error) =
            self.expanded(&response.ty, &mut BTreeSet::new())
        {
            self.require_type(
                &Value::scalar(*actual_error, None, response.cause),
                &error,
                span,
            );
            response.ty = Ty::Result(ok.clone(), Box::new(error.clone()));
            self.inspect_result(&response);
            let success = self.result_payload(&response, true, span, &mut helper);
            let callback_error = self.result_payload(&response, false, span, &mut helper);
            let close_error = self.standard_value(error.clone(), span, helper.owner, 0xF120);
            let error_cause = self.cause(
                CauseKind::BranchJoin,
                span,
                "callback Err takes precedence; close may fail after callback Ok",
                [callback_error.cause, close_error.cause],
            );
            let error_payload = match response.result_tag {
                Some(true) => close_error,
                Some(false) => callback_error,
                None => callback_error.join(&close_error, self.choice(), error_cause),
            };
            let success_branch = self.file_result_branch(true, success, &prototype, span);
            let error_branch = self.file_result_branch(false, error_payload, &prototype, span);
            let mut result = if response.result_tag == Some(false) {
                error_branch
            } else {
                success_branch.join(&error_branch, self.choice(), cause)
            };
            result.ty = Ty::Result(ok, Box::new(error.clone()));
            result
        } else {
            self.error(
                "E0301",
                span,
                "with_file action must return Result<T, Io::IoError>",
                [response.cause],
            );
            self.unit(span)
        };
        if child {
            let scopes = BTreeSet::from([lease]);
            if self.carries_scoped(&executed, &scopes) {
                self.error(
                    "E0604",
                    span,
                    "borrowed Child authority escapes its owning with_child call",
                    [executed.cause],
                );
            }
            let ending: BTreeSet<_> = helper.locals.iter().copied().collect();
            let escaped: Vec<_> = self
                .bindings
                .iter()
                .enumerate()
                .filter(|(id, binding)| {
                    binding.alive
                        && !ending.contains(id)
                        && self.carries_scoped(&binding.value, &scopes)
                })
                .map(|(_, binding)| (binding.span, binding.value.cause))
                .collect();
            for (source, cause) in escaped {
                self.error(
                    "E0604",
                    source,
                    "outside storage retains a temporary Child authority",
                    [cause],
                );
            }
            self.use_binding(lease, Mode::Write, &mut helper);
            let cause = self.cause(
                CauseKind::Cleanup,
                span,
                "compiler-owned Child boundary terminates or reaps before exporting its result",
                [executed.cause],
            );
            self.cleanup_events.push(super::super::CleanupEvent {
                binding: lease,
                owner: helper.owner,
                span,
                resumed_boundary: None,
                cause,
            });
        } else {
            self.exit_cleanups(0, &executed, span, &mut helper);
        }
        if helper.obligations.capture || helper.obligations.retention {
            self.unsupported(span,"with_file callback publication requires a confined environment and writer-family summary");
        }
        let mut exported = self.conditional_flow(&before, &skipped, &executed, None, span);
        if exported.ty != Ty::Never {
            // The skipped error has no success evidence; retain the ordinary
            // type checked on the callback path without inventing a graph.
            exported.ty = join_type_holes(&skipped.ty, &executed.ty);
        }
        self.finish_results(helper.owner, &exported);
        self.transfer_results(&exported, helper.owner, frame.owner);
        let mut obligations = helper.obligations;
        obligations.named.retain(|binding, mode| {
            if self.bindings[*binding].owner == frame.owner {
                if self.bindings[*binding].parameter && *mode != Mode::Read {
                    frame.obligations.parameter_write = true;
                }
                false
            } else {
                self.bindings[*binding].owner != helper.owner
            }
        });
        obligations.concrete.retain(|binding, _| {
            self.bindings[*binding].owner != frame.owner
                && self.bindings[*binding].owner != helper.owner
        });
        obligations.direct.retain(|binding, _| {
            self.bindings[*binding].owner != frame.owner
                && self.bindings[*binding].owner != helper.owner
        });
        obligations.capture = false;
        obligations.retention = false;
        frame.obligations.include(&obligations, true);
        for binding in helper.locals {
            self.check_authority_use(binding);
            self.bindings[binding].alive = false;
        }
        exported
    }
    fn file_result_branch(
        &mut self,
        success: bool,
        payload: Value,
        prototype: &Value,
        span: Span,
    ) -> Value {
        let mut value = payload.clone();
        value.source_type_witness = None;
        value.ty = if success {
            Ty::Result(Box::new(payload.ty.clone()), Box::new(Ty::Unknown))
        } else {
            Ty::Result(Box::new(Ty::Unknown), Box::new(payload.ty.clone()))
        };
        value.result_success = success.then(|| Box::new(payload.clone()));
        value.result_error = (!success).then(|| Box::new(payload.clone()));
        value.result_payload = Some(Box::new(payload));
        value.result_tag = Some(success);
        value.option_payload = None;
        value.option_tag = None;
        value.option_identity = None;
        value.variant_payload = None;
        value.variant_witnesses.clear();
        value.variant_tag = None;
        value.callables.clear();
        value.signature = None;
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.constant = None;
        value.static_coordinate = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.outer_results = prototype.outer_results.clone();
        value.must_outer_results = prototype.must_outer_results.clone();
        value.results.extend(&prototype.outer_results);
        value.must_results.extend(&prototype.outer_results);
        value.cause = self.cause(
            CauseKind::BranchJoin,
            span,
            "with_file preserves selected payload provenance",
            [value.cause, prototype.cause],
        );
        value
    }
}
