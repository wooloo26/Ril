//! Publication into storage can cross a callable boundary independently of its
//! return value. Retaining a writer there has the same permission restrictions.
use super::*;
impl Checker {
    /// Select the storage primitive's type variables from a written callable
    /// context. The descriptor keeps its intrinsic reception contract; the
    /// context must preserve the receiver/element relationship and modes.
    pub(super) fn contextual_storage_callable(&mut self, value: &mut Value, syntax: &TypeExpr) {
        fn parameters(
            checker: &Checker,
            syntax: &TypeExpr,
            seen: &mut BTreeSet<String>,
        ) -> Option<Vec<Parameter>> {
            match &syntax.kind {
                TypeKind::Callable { parameters, .. } => Some(parameters.clone()),
                TypeKind::Name { path, arguments } if arguments.is_empty() => {
                    let name = path.join("::");
                    if !seen.insert(name.clone()) {
                        return None;
                    }
                    let declaration = checker.types.get(&name)?;
                    if declaration.nominal || declaration.opaque {
                        return None;
                    }
                    parameters(checker, declaration.value.as_ref()?, seen)
                }
                _ => None,
            }
        }
        if value.ty != Ty::Unknown || value.callables.len() != 1 {
            return;
        }
        let Callable::Builtin(name) = &value.callables[0] else {
            return;
        };
        if !standard::storage_callable(name) {
            return;
        }
        let Some(parameters) = parameters(self, syntax, &mut BTreeSet::new()) else {
            return;
        };
        let target = self.ty(syntax);
        let Ty::Callable(inputs, result) = self.call_inference_type(&target) else {
            return;
        };
        let modes: Vec<_> = parameters.iter().map(|parameter| parameter.mode).collect();
        let ordinary = |mode| matches!(mode, ParameterMode::Read | ParameterMode::SharedMut);
        let valid = *result == Ty::Unit
            && match (name.as_str(), inputs.as_slice(), modes.as_slice()) {
                ("Array::push", [Ty::Array(element), supplied], [ParameterMode::Mut, mode]) => {
                    ordinary(*mode) && **element == *supplied
                }
                (
                    "Array::insert",
                    [Ty::Array(element), Ty::Int(index), supplied],
                    [ParameterMode::Mut, ParameterMode::Read, mode],
                ) => index == "int" && ordinary(*mode) && **element == *supplied,
                (
                    "Array::truncate",
                    [Ty::Array(_), Ty::Int(length)],
                    [ParameterMode::Mut, ParameterMode::Read],
                ) => length == "int",
                (
                    "Map::set",
                    [Ty::Map(key, element), supplied_key, supplied],
                    [ParameterMode::Mut, ParameterMode::Read, mode],
                ) => ordinary(*mode) && **key == *supplied_key && **element == *supplied,
                _ => false,
            };
        if !valid {
            self.error("E0301", syntax.span, "storage callable context must preserve its receiver, element types, result and parameter modes", [value.cause]);
            return;
        }
        value.ty = target;
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
