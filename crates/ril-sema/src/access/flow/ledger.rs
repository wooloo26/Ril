use super::*;

impl Ledger {
    pub(in crate::access) fn loop_backedge(
        &mut self,
        owner: Span,
        repeated: Span,
        entry: &Self,
        local_data: impl Fn(Span) -> bool + Copy,
        repeated_storage: bool,
    ) {
        let local = |span: Span| {
            span.file == repeated.file && span.start >= repeated.start && span.end <= repeated.end
        };
        let age = |mut occurrence: Occurrence| {
            occurrence.prior_iteration |= local(occurrence.span);
            occurrence
        };
        // Correlations within the last iteration survive the backedge. Older
        // decisions can vary independently of the branch that is about to run.
        let age_choices = |choices: &mut Choices| {
            *choices = std::mem::take(choices)
                .into_iter()
                .filter(|(key, _)| key.span != owner && (!key.prior_iteration || !local(key.span)))
                .map(|(key, arm)| (age(key), arm))
                .collect();
        };
        self.iteration.truncate(entry.iteration.len());
        self.holds.truncate(entry.holds.len());
        self.slots.retain(|id, _| entry.slots.contains_key(id));
        self.array_extents.retain(|region, _| !local(region.source));
        let carried = self.rebase_results(local, age_choices);
        self.choices
            .retain(|key, _| key.span != owner && !local(key.span));
        for value in self
            .iteration
            .iter_mut()
            .chain(self.holds.iter_mut().map(|(_, value)| value))
        {
            value.remap_results(&carried, age_choices);
        }
        let age_value = |value: &mut Datum| {
            value.compact_snapshot(local_data);
            value.remap_results(&carried, age_choices);
            value.transform(&mut |origin| {
                origin.region.age_allocation(local(origin.region.source));
                origin.dependencies = std::mem::take(&mut origin.dependencies)
                    .into_iter()
                    .map(age)
                    .collect();
                age_choices(&mut origin.branches);
            });
        };

        for slot in self.slots.values_mut() {
            age_value(&mut slot.value);
            slot.value.fold_old_allocations(&mut self.loop_members);
        }
        for (mut slot, mut member) in std::mem::take(&mut self.loop_members) {
            slot.age_allocation(local(slot.source));
            age_value(&mut member);
            member.fold_old_allocations(&mut self.loop_members);
            merge_member(&mut self.loop_members, slot, member);
        }
        for (mut region, mut update) in std::mem::take(&mut self.replacements) {
            region.age_allocation(local(region.source));
            update.definite &= !region.summarized();
            age_value(&mut update.value);
            update.value.fold_old_allocations(&mut self.loop_members);
            self.replacements
                .entry(region)
                .and_modify(|prior| {
                    prior.value = std::mem::take(&mut prior.value).joined(update.value.clone());
                    prior.definite &= update.definite;
                })
                .or_insert(update);
        }
        for update in self.capture_updates.values_mut() {
            age_value(&mut update.value);
            update.value.fold_old_allocations(&mut self.loop_members);
        }
        for sample in self.storage_samples.values_mut() {
            age_value(sample);
            sample.fold_old_allocations(&mut self.loop_members);
        }
        if self.storage_flow != entry.storage_flow
            && let Some(flow) = &mut self.storage_flow
        {
            for value in flow.values_mut() {
                age_value(value);
                value.fold_old_allocations(&mut self.loop_members);
            }
            if repeated_storage {
                flow.widen();
            }
        }
        for (token, triggers) in std::mem::take(&mut self.revoked) {
            let archived = self.revoked.entry(age(token)).or_default();
            for (trigger, choices) in triggers {
                let combined = archived.entry(trigger).or_default();
                combined.extend(choices.into_iter().map(|mut branch| {
                    age_choices(&mut branch);
                    branch
                }));
                Self::widen_choices(combined);
            }
        }
    }

    pub(in crate::access) fn size(&self) -> usize {
        self.slots
            .values()
            .map(|slot| slot.value.size())
            .chain(self.replacements.values().map(|update| update.value.size()))
            .chain(
                self.capture_updates
                    .values()
                    .map(|update| update.value.size()),
            )
            .chain(self.loop_members.values().map(Datum::size))
            .sum()
    }

    pub(in crate::access) fn merge_bindings(&mut self, alternatives: &[Self]) {
        let mut prior = self.clone();
        if let Some(first) = alternatives.first() {
            for (&decl, slot) in &first.slots {
                if alternatives
                    .iter()
                    .all(|branch| branch.slots.contains_key(&decl))
                {
                    prior.slots.entry(decl).or_insert_with(|| slot.clone());
                }
            }
        }
        self.merge(&prior, alternatives);
    }

    pub(in crate::access) fn continue_at_pattern(&mut self, mut paths: Vec<Self>) -> bool {
        if let Some(last) = paths.pop() {
            if paths.is_empty() {
                *self = last;
            } else {
                paths.push(last);
                self.merge_bindings(&paths);
            }
            true
        } else {
            false
        }
    }

    pub(in crate::access) fn merge(&mut self, prior: &Self, alternatives: &[Self]) {
        let alternatives: Vec<_> = alternatives
            .iter()
            .filter(|ledger| !ledger.no_continuation)
            .collect();
        self.no_continuation = prior.no_continuation || alternatives.is_empty();
        self.slots = prior.slots.clone();
        self.result_samples.clone_from(&prior.result_samples);
        self.revoked = prior.revoked.clone();
        self.obligations.clear();
        if alternatives.is_empty() {
            self.obligations.clone_from(&prior.obligations);
        }
        self.lost_results = prior.lost_results.clone();
        self.linear_obligations.clear();
        if alternatives.is_empty() {
            self.linear_obligations
                .clone_from(&prior.linear_obligations);
        }
        for branch in &alternatives {
            for (&token, revoked) in &branch.revoked {
                let merged = self.revoked.entry(token).or_default();
                for (&trigger, alternatives) in revoked {
                    let cases = merged.entry(trigger).or_default();
                    cases.extend(alternatives.iter().cloned());
                    Self::widen_choices(cases);
                }
            }
            self.obligations.extend(branch.obligations.iter().cloned());
            self.lost_results.extend(&branch.lost_results);
            self.linear_obligations
                .extend(branch.linear_obligations.iter().cloned());
        }
        self.linear_consumed = if alternatives.is_empty() {
            prior.linear_consumed.clone()
        } else {
            alternatives
                .iter()
                .flat_map(|branch| &branch.linear_consumed)
                .filter(|item| {
                    alternatives.iter().all(|branch| {
                        branch.linear_consumed.contains(item)
                            || !branch.linear_obligations.contains(item)
                    })
                })
                .cloned()
                .collect()
        };
        self.linear_armed = if alternatives.is_empty() {
            prior.linear_armed.clone()
        } else {
            alternatives
                .first()
                .map(|first| {
                    first
                        .linear_armed
                        .iter()
                        .filter(|(item, _)| {
                            alternatives
                                .iter()
                                .all(|branch| branch.linear_armed.contains_key(*item))
                        })
                        .map(|(item, &scope)| (item.clone(), scope))
                        .collect()
                })
                .unwrap_or_default()
        };
        self.inspected = if alternatives.is_empty() {
            prior.inspected.clone()
        } else {
            alternatives
                .iter()
                .flat_map(|branch| &branch.inspected)
                .filter(|item| {
                    alternatives.iter().all(|branch| {
                        branch.inspected.contains(item) || !branch.obligations.contains(item)
                    })
                })
                .cloned()
                .collect()
        };
        self.merge_pending_paths(prior, &alternatives);
        for (id, slot) in &mut self.slots {
            if let Some(value) = alternatives
                .iter()
                .filter_map(|branch| branch.slots.get(id).map(|slot| slot.value.clone()))
                .reduce(Datum::joined)
            {
                slot.value = value;
            }
        }
        self.choices = prior.choices.clone();
        self.merge_replacements(prior, &alternatives);
        self.storage_samples = prior.storage_samples.clone();
        for (key, value) in alternatives
            .iter()
            .flat_map(|branch| &branch.storage_samples)
        {
            self.sample_storage(key.clone(), value.clone());
        }
        self.storage_flow = if alternatives.is_empty() {
            prior.storage_flow.clone()
        } else if alternatives
            .iter()
            .any(|branch| branch.storage_flow.is_some())
        {
            Some(StorageFlow::join(alternatives.iter().map(|branch| {
                branch
                    .storage_flow
                    .clone()
                    .unwrap_or_else(|| branch.storage_prefix())
            })))
        } else {
            None
        };
        self.capture_updates = if alternatives.is_empty() {
            prior.capture_updates.clone()
        } else {
            Self::join_updates(
                alternatives
                    .iter()
                    .map(|branch| &branch.capture_updates)
                    .collect(),
            )
        };
        self.drafts = prior
            .drafts
            .iter()
            .map(|(region, initial)| {
                let working = alternatives
                    .iter()
                    .filter_map(|branch| branch.drafts.get(region).cloned())
                    .reduce(Datum::join_draft_results)
                    .unwrap_or_else(|| initial.clone());
                (region.clone(), working)
            })
            .collect();
        self.array_extents = alternatives
            .first()
            .map_or(&prior.array_extents, |branch| &branch.array_extents)
            .iter()
            .filter_map(|(region, &extent)| {
                let merged = alternatives.iter().try_fold(extent, |merged, branch| {
                    let branch = branch.array_extents.get(region)?;
                    Some(merged.meet(*branch))
                })?;
                Some((region.clone(), merged))
            })
            .collect();
        self.loop_members = if alternatives.is_empty() {
            prior.loop_members.clone()
        } else {
            let mut members = BTreeMap::new();
            for (slot, member) in alternatives.iter().flat_map(|branch| &branch.loop_members) {
                merge_member(&mut members, slot.clone(), member.clone());
            }
            members
        };
    }

    pub(super) fn merge_pending_paths(&mut self, prior: &Self, alternatives: &[&Self]) {
        let Some(first) = alternatives.first() else {
            self.pending_result_paths
                .clone_from(&prior.pending_result_paths);
            return;
        };
        self.pending_result_paths.clear();
        for item in &self.obligations {
            if self.inspected.contains(item) {
                continue;
            }
            let prior_paths = first.pending_result_paths.get(item);
            if alternatives.iter().all(|branch| {
                branch.result_pending(item) && branch.pending_result_paths.get(item) == prior_paths
            }) {
                // Nothing narrows the pending paths when every branch keeps
                // the same obligation. This also avoids adding loop axes to it.
                if let Some(paths) = prior_paths {
                    self.pending_result_paths
                        .insert(item.clone(), paths.clone());
                }
                continue;
            }
            let mut paths = BTreeSet::new();
            for branch in alternatives
                .iter()
                .filter(|branch| branch.result_pending(item))
            {
                paths.extend(branch.pending_paths(item, &branch.choices).map(|mut path| {
                    path.extend(branch.choices.iter().map(|(&key, &arm)| (key, arm)));
                    path.retain(|key, arm| prior.choices.get(key) != Some(arm));
                    path
                }));
                Self::widen_choices(&mut paths);
                if paths.contains(&Choices::new()) {
                    break;
                }
            }
            if paths.is_empty() {
                self.inspected.insert(item.clone());
            } else if !paths.contains(&Choices::new()) {
                self.pending_result_paths.insert(item.clone(), paths);
            }
        }
    }

    pub(super) fn merge_replacements(&mut self, prior: &Self, alternatives: &[&Self]) {
        if alternatives.is_empty() {
            self.replacements.clone_from(&prior.replacements);
            return;
        }
        self.replacements = Self::join_updates(
            alternatives
                .iter()
                .map(|branch| &branch.replacements)
                .collect(),
        );
    }

    pub(in crate::access) fn join_updates(
        paths: Vec<&BTreeMap<Region, Replacement>>,
    ) -> BTreeMap<Region, Replacement> {
        let regions: BTreeSet<_> = paths.iter().flat_map(|path| path.keys()).collect();
        regions
            .into_iter()
            .filter_map(|region| {
                let entries: Vec<_> = paths.iter().filter_map(|path| path.get(region)).collect();
                let definite =
                    entries.len() == paths.len() && entries.iter().all(|entry| entry.definite);
                let value = entries
                    .into_iter()
                    .map(|entry| entry.value.clone())
                    .reduce(Datum::joined)?;
                Some((region.clone(), Replacement { value, definite }))
            })
            .collect()
    }

    pub(in crate::access) fn call_updates(
        &self,
        owner: Span,
        formals: &[Option<Span>],
        captures: &BTreeSet<Span>,
    ) -> BTreeMap<Region, Replacement> {
        self.replacements
            .iter()
            .filter(|(region, update)| {
                (formals.contains(&Some(region.source))
                    || region.selection.is_empty() && captures.contains(&region.source))
                    && update.value.publications.contains_key(&owner)
            })
            .chain(
                self.capture_updates
                    .iter()
                    .filter(|_| self.capture_owner == Some(owner)),
            )
            .map(|(region, update)| {
                (
                    region.clone(),
                    Replacement {
                        value: self.snapshot_call_graph(&update.value),
                        definite: update.definite,
                    },
                )
            })
            .collect()
    }

    pub(in crate::access) fn replaces_slot(&self, owner: Span, decl: Span) -> bool {
        self.replacements
            .get(&Region::root(decl))
            .is_some_and(|update| update.value.publications.contains_key(&owner))
    }

    pub(in crate::access) fn replace_slot(
        &mut self,
        decl: Span,
        mut value: Datum,
        definite: bool,
    ) -> bool {
        self.stamp(&mut value);
        let Some(slot) = self.slots.get_mut(&decl) else {
            return false;
        };
        slot.value = if definite {
            value.clone()
        } else {
            std::mem::take(&mut slot.value).joined(value.clone())
        };
        let region = Region::root(decl);
        self.replace_region(&region, &value, definite);
        if self.storage_captures.contains(&decl)
            && self
                .capture_owner
                .is_some_and(|owner| value.publications.contains_key(&owner))
        {
            self.record_storage_write(StorageTarget::Entry(region), &value, definite);
        }
        if !value.roots.is_empty() {
            self.replace_region(&Region::capture_slot(decl), &value, definite);
        }
        true
    }

    pub(in crate::access) fn replace_member(
        &mut self,
        slot: &Datum,
        mut value: Datum,
        definite: bool,
    ) {
        self.stamp(&mut value);
        let single = slot.roots.first().is_some_and(|first| {
            slot.roots
                .iter()
                .all(|root| root.region == first.region && root.storage_read == first.storage_read)
        });
        let publishes = self
            .capture_owner
            .is_some_and(|owner| value.publications.contains_key(&owner));
        let formal = |region: &Region| self.storage_formals.contains(&Some(region.source));
        let tracked_append = slot
            .roots
            .iter()
            .any(|root| root.region.append_parent().is_some() && formal(&root.region))
            || slot.capture_paths.keys().any(|path| {
                self.capture_owner == Some(path.owner) && path.region.append_parent().is_some()
            });
        // The first relative append needs its own ordered step. Capture
        // preceding transfers before adding the append to the ledger.
        if publishes && tracked_append && self.storage_flow.is_none() {
            self.storage_flow = Some(self.storage_prefix());
        }
        let mut writes = BTreeMap::new();
        let mut draft_paths = BTreeSet::new();
        for origin in &slot.roots {
            let region = &origin.region;
            let single_object = definite && single && !region.summarized();
            let strong_store = single_object && !region.selection.iter().any(Coordinate::is_range);
            let single_append = single_object
                && region
                    .append_parent()
                    .is_some_and(|parent| !parent.iter().any(Coordinate::is_range));
            if origin.draft && self.drafts.contains_key(&region.allocation_root()) {
                if draft_paths.insert(region) {
                    let mut stored = self.snapshot_for_draft(&value);
                    stored.freeze();
                    if let Some(working) = self.drafts.get_mut(&region.allocation_root()) {
                        working.apply_draft_update(
                            &region.selection,
                            &stored,
                            strong_store || single_append,
                        );
                    }
                }
                continue;
            }
            if strong_store && origin.draft {
                self.replacements.retain(|prior, _| {
                    prior.selection.len() <= region.selection.len()
                        || !prior.selection.starts_with(&region.selection)
                        || !prior.overlaps(region)
                });
            }
            self.replace_region(region, &value, strong_store);
            if publishes && self.storage_flow.is_some() {
                let definite = strong_store || single_append;
                // Draft writes keep the same path when an earlier step
                // replaces the object currently stored there.
                if !origin.draft
                    && let Some(parent) = &origin.storage_read
                    && let Some(member) = region.selection.last()
                {
                    let target = StorageTarget::Observed {
                        parent: parent.clone(),
                        member: member.clone(),
                    };
                    writes.insert(target, definite);
                } else if self.storage_formals.contains(&Some(region.source)) {
                    writes.insert(StorageTarget::Entry(region.clone()), definite);
                }
            }
        }
        if !slot.roots.is_empty()
            && slot
                .roots
                .iter()
                .all(|root| draft_paths.contains(&root.region))
        {
            return;
        }
        let has_entry_target =
            slot.roots.is_empty() || slot.roots.iter().any(|root| root.storage_read.is_none());
        let entirely_at_entry = slot.roots.iter().all(|root| root.storage_read.is_none());
        let captured_append_covered = single
            && writes.keys().any(|target| {
                matches!(target, StorageTarget::Entry(region) if region.append_parent().is_some())
            });
        for (path, &known) in &slot.capture_paths {
            if has_entry_target && self.capture_owner == Some(path.owner) && publishes {
                let definite = definite && entirely_at_entry && known;
                let strong_store =
                    definite && !path.region.selection.iter().any(Coordinate::is_range);
                Self::record_replacement(
                    &mut self.capture_updates,
                    &path.region,
                    &value,
                    strong_store,
                );
                if let Some(parent) = path.region.append_parent() {
                    if !captured_append_covered {
                        let single_append = definite
                            && slot.capture_paths.len() == 1
                            && !parent.iter().any(Coordinate::is_range);
                        writes.insert(StorageTarget::Entry(path.region.clone()), single_append);
                    }
                } else {
                    *writes
                        .entry(StorageTarget::Entry(path.region.clone()))
                        .or_default() |= strong_store;
                }
            }
        }
        for (target, definite) in writes {
            self.record_storage_write(target, &value, definite);
        }
    }

    pub(in crate::access) fn record_array_length(&mut self, allocation: Span, length: usize) {
        self.array_extents.insert(
            Region::allocation(allocation),
            ArrayExtent {
                minimum: length,
                exact: true,
            },
        );
    }

    pub(in crate::access) fn clear_array_extents(&mut self) {
        self.array_extents.clear();
    }

    pub(in crate::access) fn array_prefix_length(&self, array: &Datum) -> usize {
        array
            .roots
            .iter()
            .map(|root| self.array_extent(root).map_or(0, |extent| extent.minimum))
            .min()
            .unwrap_or(0)
    }

    pub(in crate::access) fn exact_array_length(&self, array: &Datum) -> Option<usize> {
        let first = self.array_extent(array.roots.first()?)?;
        (first.exact
            && array
                .roots
                .iter()
                .all(|root| self.array_extent(root) == Some(first)))
        .then_some(first.minimum)
    }

    pub(super) fn array_extent(&self, origin: &Origin) -> Option<ArrayExtent> {
        if origin.detached_snapshot {
            origin.array_extent
        } else {
            self.array_extents.get(&origin.region).copied()
        }
    }

    pub(in crate::access) fn append_coordinate(
        &mut self,
        array: &Datum,
        single_push: bool,
    ) -> Coordinate {
        if array
            .roots
            .iter()
            .any(|root| root.draft && self.drafts.contains_key(&root.region.allocation_root()))
        {
            // A draft append selects its position in the working graph.
            return Coordinate::ArrayTail(0);
        }
        if single_push
            && let Some(first) = array.roots.first()
            && !first.region.summarized()
            && !first.region.selection.iter().any(Coordinate::is_range)
            && array
                .roots
                .iter()
                .all(|root| root.region == first.region && root.storage_read.is_none())
            && let Some(extent) = self.array_extents.get_mut(&first.region)
            && extent.exact
            && let Some(next) = extent.minimum.checked_add(1)
        {
            let position = Coordinate::Index(extent.minimum.to_string());
            extent.minimum = next;
            return position;
        }
        let minimum = self.array_prefix_length(array);
        for (region, extent) in &mut self.array_extents {
            if array.roots.iter().any(|root| {
                root.region.selection.len() == region.selection.len()
                    && root.region.overlaps(region)
            }) {
                extent.exact = false;
            }
        }
        Coordinate::ArrayTail(minimum)
    }

    pub(super) fn replace_region(&mut self, region: &Region, value: &Datum, definite: bool) {
        Self::record_replacement(&mut self.replacements, region, value, definite);
    }

    pub(super) fn record_replacement(
        updates: &mut BTreeMap<Region, Replacement>,
        region: &Region,
        value: &Datum,
        definite: bool,
    ) {
        if definite {
            updates.insert(
                region.clone(),
                Replacement {
                    value: value.clone(),
                    definite,
                },
            );
        } else {
            for (key, entry) in &mut *updates {
                if key.selection.len() == region.selection.len() && key.overlaps(region) {
                    entry.value = std::mem::take(&mut entry.value).joined(value.clone());
                }
            }
            updates
                .entry(region.clone())
                .or_insert_with(|| Replacement {
                    value: value.clone(),
                    definite,
                });
        }
    }

    pub(in crate::access) fn project(
        &self,
        base: &Datum,
        coordinate: Coordinate,
        mode: Access,
    ) -> Datum {
        self.project_schema(base, coordinate, mode.as_mode())
    }

    pub(in crate::access) fn project_schema(
        &self,
        base: &Datum,
        coordinate: Coordinate,
        mode: Mode,
    ) -> Datum {
        let singleton =
            base.array_len == Some(1) || base.map_keys.as_ref().is_some_and(|keys| keys.len() == 1);
        let arbitrary_element =
            (coordinate.is_range() || coordinate == Coordinate::MapKey) && !singleton;
        let mut value = self.project_members(base, coordinate, mode, |_| true, |_| true);
        value.receive_cloned_member(mode);
        if arbitrary_element {
            // A single unknown index cannot inspect the union of its possible values.
            value.forget_results();
        }
        value
    }

    pub(super) fn project_members(
        &self,
        base: &Datum,
        coordinate: Coordinate,
        mode: Mode,
        follow: impl Fn(&Origin) -> bool,
        include_opaque: impl Fn(&Region) -> bool,
    ) -> Datum {
        if base.roots.is_empty() || self.replacements.is_empty() && self.loop_members.is_empty() {
            return base.project_schema(coordinate, mode);
        }
        let initial = base.known_member(&coordinate);
        let slot = base.slot_projection(coordinate.clone());
        let mut missing = Vec::new();
        let mut projected = None;
        let mut use_inline = false;
        let with_capture_path = |mut member: Datum, stored| {
            base.project_capture_paths(&coordinate, &mut member, stored);
            if !stored {
                base.project_storage_read(&coordinate, &mut member);
            }
            member
        };
        for (root, origin) in base.roots.iter().zip(&slot.roots) {
            if !follow(root) {
                use_inline = true;
                continue;
            }
            let region = &origin.region;
            if root.detached_snapshot {
                use_inline = true;
                if initial.is_none() && include_opaque(region) {
                    missing.push(root.clone());
                }
                continue;
            }
            let exact = self.replacements.get(region);
            if let Some(update) = exact.filter(|update| update.definite) {
                projected = join_member(projected, with_capture_path(update.value.clone(), true));
                continue;
            }
            use_inline = true;
            let matches = |key: &Region| {
                key.selection.len() == region.selection.len() && key.overlaps(region)
            };
            let mut folded = false;
            for (key, member) in &self.loop_members {
                if matches(key) {
                    folded |= key == region;
                    projected = join_member(projected, with_capture_path(member.clone(), true));
                }
            }
            for (key, update) in &self.replacements {
                if matches(key) {
                    projected =
                        join_member(projected, with_capture_path(update.value.clone(), true));
                }
            }
            if !folded && initial.is_none() && include_opaque(region) {
                missing.push(root.clone());
            }
        }
        if use_inline && let Some(initial) = initial {
            projected = join_member(projected, with_capture_path(initial, false));
        }
        if let Some(value) = &mut projected {
            base.project_known(value, &coordinate, mode);
        }
        if !missing.is_empty() {
            let fallback = Datum {
                roots: missing,
                requires_new: base.requires_new,
                capture_paths: base.capture_paths.clone(),
                ..Datum::default()
            };
            projected = join_member(projected, fallback.project_opaque(coordinate, mode));
        }
        projected.unwrap_or_default()
    }

    pub(in crate::access) fn clear_linear_obligations(&mut self) {
        self.linear_obligations.clear();
        self.linear_consumed.clear();
        self.linear_armed.clear();
    }

    pub(in crate::access) fn record_linear(
        &mut self,
        value: &mut Datum,
        span: Span,
        is_collection: bool,
    ) {
        let occ = LinearOccurrence {
            span,
            created_in: self.choices.clone(),
            is_collection,
        };
        self.linear_obligations.insert(occ.clone());
        value.linear.insert(occ);
    }

    pub(in crate::access) fn consume_datum_linear(&mut self, value: &Datum) {
        for occ in value.all_linear() {
            self.linear_consumed.insert(occ);
        }
    }

    pub(in crate::access) fn arm_datum_linear(&mut self, value: &Datum, boundary: Span) {
        for occ in value.all_linear() {
            self.linear_armed.insert(occ, boundary);
        }
    }

    pub(in crate::access) fn pending_linear(&self) -> impl Iterator<Item = &LinearOccurrence> {
        self.linear_obligations
            .difference(&self.linear_consumed)
            .filter(|occ| compatible(&occ.created_in, &self.choices))
    }

    pub(in crate::access) fn has_direct_revocation(&self, decl: Span) -> bool {
        self.revoked
            .get(&Occurrence::from(decl))
            .is_some_and(|triggers| triggers.contains_key(&None))
    }
}
