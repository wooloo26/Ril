//! Publication into storage can cross a callable boundary independently of its
//! return value. Retaining a writer there has the same permission restrictions.
use super::*;
impl Checker {
    /// Instantiate the original universal declaration using full Source
    /// coordinates. Erased runtime shapes never establish its correlations.
    pub(super) fn instantiate_builtin_signature(&mut self, value: &mut Value, syntax: &TypeExpr) {
        if value.ty != Ty::Unknown || value.callables.len() != 1 {
            return;
        }
        let Callable::Builtin(name) = &value.callables[0] else {
            return;
        };
        let Some(id) = ril_compiler_core::builtin_calls::GenericBuiltin::lookup(name) else {
            return;
        };
        let target = self.freeze_source_receiving_target(syntax);
        let instance = target
            .schema
            .as_ref()
            .ok_or(crate::sema::source_types::SourceTypesError::Unresolved)
            .and_then(|source| {
                source
                    .instantiate_builtin(id, &mut crate::sema::source_types::WorkLimit::new(16384))
            });
        match instance {
            Ok(Some(_)) => value.ty = self.ty(syntax),
            Ok(None) => self.error("E0301", syntax.span, "primitive Source instance must preserve its receiver, full element/key types, result and parameter modes", [value.cause]),
            Err(_) => self.unsupported(syntax.span, "primitive signature selection requires its complete frozen receiving Source"),
        }
    }
    pub(super) fn check_stored_authority(
        &mut self,
        target: &Value,
        value: &Value,
        old: Option<&Value>,
        span: Span,
        frame: &mut Frame,
    ) {
        if self
            .heap
            .reachable(value.origins.nodes.iter().copied())
            .iter()
            .filter_map(|node| self.windows.get(node))
            .any(|window| !self.origins_disjoint(&window.backing, &target.origins))
        {
            self.unsupported(span,"publishing a window into possibly overlapping storage requires a post-write alias-liveness proof");
        }
        let replaced_same = old
            .is_some_and(|old| old.origins == value.origins && old.permission == value.permission);
        if !replaced_same
            && value.permission == Permission::Write
            && !value.construction
            && self.has_writer(value)
            && !value.marker
            && !value.retention_result
        {
            self.error("E0510",span,"publishing another writable stored alias requires a current sharing acknowledgement",[value.cause]);
        }
        let outside = target.sources.iter().any(|source| {
            self.bindings[*source].parameter || self.bindings[*source].owner != frame.owner
        }) || self
            .heap
            .reachable(target.origins.nodes.iter().copied())
            .iter()
            .any(|node| {
                self.heap.nodes[node.0 as usize]
                    .writable_roots
                    .iter()
                    .any(|root| {
                        self.bindings.get(root.0 as usize).is_some_and(|binding| {
                            binding.alive && (binding.parameter || binding.owner != frame.owner)
                        })
                    })
            });
        if !outside {
            return;
        }
        self.check_deep_uncertainty(value, span);
        if value.temporary
            && value.permission == Permission::Write
            && !value.origins.nodes.is_empty()
        {
            self.unsupported(
                span,
                "stored writer cannot extend an ordinary mutable parameter loan",
            );
        }
        let retained = self.writable_nodes(value).iter().any(|node| {
            self.heap.nodes[node.0 as usize]
                .writable_roots
                .iter()
                .any(|root| {
                    self.bindings.get(root.0 as usize).is_some_and(|binding| {
                        binding.alive && (binding.parameter || binding.owner != frame.owner)
                    })
                })
        });
        if retained && !replaced_same {
            frame.obligations.retention = true;
            self.access(value, None, Mode::Retain, span, frame);
        }
        for callable in self.graph_callables(value) {
            let temporary = match callable {
                Callable::Closure(id) => self.closures[id]
                    .captures
                    .iter()
                    .any(|binding| self.bindings[*binding].value.temporary),
                Callable::Named(id) => self.functions[id]
                    .captures
                    .iter()
                    .any(|binding| self.bindings[*binding].value.temporary),
                _ => false,
            };
            if temporary {
                self.unsupported(
                    span,
                    "stored callable cannot extend a captured temporary loan",
                );
            }
        }
        self.record_closure_exposure(
            value,
            frame,
            super::super::closure_exclusivity::ExposureKind::Stored,
            span,
        );
        self.escape_obligations(value, frame);
    }
}
