//! Finite resource allocation contexts and conservative descriptor families.
use super::*;

pub(super) fn merge_value(left: &mut Value, right: &Value) {
    // Both values may coexist in a descriptor family. Preserve every origin,
    // producer and permission restriction without a branch-correlation claim.
    *left = left.join(right, u32::MAX, left.cause);
    super::super::loop_graph::forget_choices(left);
}

pub(super) fn merge_task(left: &mut Task, right: &Task) {
    merge_value(&mut left.output, &right.output);
    left.borrows.extend(&right.borrows);
    left.joined |= right.joined;
    left.observed &= right.observed;
    left.may_fail |= right.may_fail;
}

impl State {
    pub(super) fn resource_variants(&self, node: NodeId) -> impl Iterator<Item = &Resource> {
        self.resources
            .get(&node)
            .into_iter()
            .chain(self.resource_alternatives.get(&node).into_iter().flatten())
    }
    pub(super) fn merge_resource(&mut self, node: NodeId, value: Resource) {
        if let Some(current) = self.resources.get(&node) {
            if current != &value
                && !self
                    .resource_alternatives
                    .get(&node)
                    .is_some_and(|values| values.contains(&value))
            {
                self.resource_alternatives
                    .entry(node)
                    .or_default()
                    .push(value);
            }
        } else {
            self.resources.insert(node, value);
        }
    }
}

impl Checker {
    pub(super) fn descriptor_node(
        &mut self,
        span: Span,
        discriminator: u32,
        owner: ScopeId,
    ) -> NodeId {
        let mut calls = Vec::new();
        let mut seen = BTreeSet::new();
        let mut recursive = false;
        for id in self.copy_invocation_stack.iter().rev() {
            let call = &self.copy_invocations[id.0 as usize];
            if !seen.insert(call.target) {
                recursive = true;
                break;
            }
            calls.push(DescriptorCall {
                target: call.target,
                caller: call.caller_owner,
                site: (call.span.file.0, call.span.start, call.span.end),
            });
        }
        let mut closures = Vec::new();
        let mut seen_closures = BTreeSet::new();
        for id in self.closure_invocation_stack.iter().rev() {
            let call = &self.closure_invocations[id.0 as usize];
            let Some(target) = self.closures[call.closure].site else {
                // Missing lexical identity merges conservatively and prevents
                // the resulting family from becoming a singleton proof.
                recursive = true;
                break;
            };
            if !seen_closures.insert(target) {
                recursive = true;
                break;
            }
            closures.push(DescriptorClosure {
                target,
                caller: call.caller_owner,
                site: (call.site.file.0, call.site.start, call.site.end),
            });
        }
        let key = DescriptorContext {
            site: (span.file.0, span.start, span.end),
            discriminator,
            calls,
            closures,
            recursive,
        };
        let site = if let Some(site) = self.descriptor_sites.get(&key) {
            *site
        } else {
            // The call alphabet is finite and no target occurs twice. The
            // explicit limit also bounds its potentially exponential paths.
            if self.descriptor_sites.len() >= 4096 {
                self.unsupported(span,"resource allocation context budget exhausted; no descriptor independence proof was issued");
                return self.allocate(span, discriminator, owner);
            }
            let site = SiteId(self.next_site);
            self.next_site = self
                .next_site
                .checked_add(1)
                .expect("semantic allocation site identity exhausted");
            self.descriptor_sites.insert(key, site);
            site
        };
        let node = self.allocate_site(span, site, owner);
        if recursive {
            self.heap.set_relation(node, node, Relation::UNKNOWN);
        }
        node
    }

    pub(super) fn exact_resource_node(&self, node: NodeId) -> bool {
        self.heap.nodes[node.0 as usize].multiplicity == Multiplicity::One
            && self
                .concurrency
                .resource_alternatives
                .get(&node)
                .is_none_or(Vec::is_empty)
            && self
                .concurrency
                .resources
                .get(&node)
                .is_none_or(|resource| {
                    std::iter::once(resource.scope)
                        .chain(resource.task)
                        .chain(resource.channel)
                        .all(|reference| {
                            self.heap.nodes[reference.0 as usize].multiplicity == Multiplicity::One
                        })
                })
    }
    pub(super) fn require_exact_resource_nodes(&mut self, value: &Value, span: Span) -> bool {
        if self
            .concurrent_nodes(value)
            .iter()
            .all(|node| self.exact_resource_node(*node))
        {
            return true;
        }
        self.unsupported(
            span,
            "resource descriptor family requires a per-instance authority and channel proof",
        );
        false
    }
    pub(super) fn resource_unproved(&mut self, span: Span) -> Value {
        let mut value = self.unit(span);
        value.ty = Ty::Never;
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn span(start: u32) -> Span {
        Span {
            file: FileId(0),
            start,
            end: start + 1,
        }
    }
    fn state(scope: NodeId, channel: NodeId, cause: CauseId) -> Resource {
        Resource {
            cause,
            scope,
            task: None,
            kind: Kind::Sender,
            channel: Some(channel),
            formal: false,
        }
    }
    #[test]
    fn recency_preserves_every_channel_scope_and_cause_alternative() {
        let mut checker = Checker::new(FileId(0));
        let scope = checker.allocate(span(1), 1, ScopeId(0));
        let channel_a = checker.allocate(span(2), 1, ScopeId(0));
        let channel_b = checker.allocate(span(3), 1, ScopeId(0));
        let first = checker.allocate(span(10), 1, ScopeId(0));
        checker.concurrency.resources.insert(
            first,
            state(scope, channel_a, checker.heap.nodes[first.0 as usize].cause),
        );
        let second = checker.allocate(span(10), 1, ScopeId(0));
        checker.concurrency.resources.insert(
            second,
            state(
                scope,
                channel_b,
                checker.heap.nodes[second.0 as usize].cause,
            ),
        );
        checker.allocate(span(10), 1, ScopeId(0));
        let older = checker.recency_moves.last().unwrap().1;
        let variants: Vec<_> = checker.concurrency.resource_variants(older).collect();
        assert_eq!(variants.len(), 2);
        assert_ne!(variants[0].cause, variants[1].cause);
        assert_eq!(
            variants
                .iter()
                .filter_map(|value| value.channel)
                .collect::<BTreeSet<_>>(),
            [channel_a, channel_b].into()
        );
        assert!(!checker.exact_resource_node(older));
        checker.concurrency.invalid.insert(older);
        let value = Value::reference(
            Ty::Unknown,
            older,
            checker.heap.nodes[older.0 as usize].cause,
        );
        assert!(
            checker
                .concurrent_identity(&value, Kind::Sender, span(20))
                .is_none()
        );
        assert!(
            checker.diagnostics.is_empty(),
            "a family does not prove which descriptor was consumed"
        );
        assert!(!checker.unsupported.is_empty());
    }

    #[test]
    fn equal_static_call_strings_share_a_site_and_recursion_never_claims_singleton() {
        let parsed = ril_syntax::parse("fn helper(value:int)->int{value}");
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        let call = checker.copy_invocations[0].clone();
        checker.copy_invocation_stack = vec![call.id];
        let frame = checker.frame(Env::new(), false);
        let first = checker.descriptor_node(span(50), 0x6700, frame.owner);
        let mut later = call.clone();
        later.id = super::super::super::super::copy_templates::InstanceId(
            checker.copy_invocations.len() as u32,
        );
        checker.copy_invocations.push(later.clone());
        checker.copy_invocation_stack = vec![later.id];
        let second = checker.descriptor_node(span(50), 0x6700, frame.owner);
        assert_eq!(first, second);
        assert_eq!(checker.descriptor_sites.len(), 1);
        assert!(!checker.recency_moves.is_empty());
        checker.copy_invocation_stack = vec![call.id, later.id];
        let node = checker.descriptor_node(span(50), 0x6700, frame.owner);
        assert_eq!(
            checker.heap.nodes[node.0 as usize].multiplicity,
            Multiplicity::MayMany
        );
        assert_eq!(checker.heap.relation(node, node), Relation::UNKNOWN);
        assert_eq!(checker.descriptor_sites.len(), 2);
        let before = checker.concurrency.scopes.clone();
        let body = checker.unit(span(70));
        let mut frame = frame;
        let result = checker.concurrent_scope(&body, span(71), &mut frame);
        assert_eq!(result.ty, Ty::Never);
        assert_eq!(checker.concurrency.scopes, before);
        assert!(checker.cancellation_contexts.is_empty());
        assert!(
            checker
                .unsupported
                .iter()
                .any(|item| item.description.contains("scope entry"))
        );
    }

    #[test]
    fn merging_task_and_receiver_metadata_retains_all_results_and_borrows() {
        let mut left = Value::scalar(Ty::Unit, None, CauseId(1));
        left.results.insert(7);
        let mut right = left.clone();
        right.results = [9].into();
        let mut task = Task {
            output: left,
            may_fail: false,
            joined: false,
            observed: true,
            borrows: [NodeId(1)].into(),
        };
        let other = Task {
            output: right,
            may_fail: true,
            joined: true,
            observed: false,
            borrows: [NodeId(2)].into(),
        };
        merge_task(&mut task, &other);
        assert_eq!(task.output.results, [7, 9].into());
        assert_eq!(task.borrows, [NodeId(1), NodeId(2)].into());
        assert!(task.may_fail && task.joined && !task.observed);
        assert!(task.output.origins.choices.is_empty());
    }
}
