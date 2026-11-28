use super::*;

impl Datum {
    pub(in crate::access) fn mark_call_allocations<'d>(
        values: impl Iterator<Item = &'d mut Self>,
        body: Span,
    ) {
        let values: Vec<_> = values.collect();
        let mut regions = BTreeMap::<Region, BTreeSet<_>>::new();
        for (output, value) in values.iter().enumerate() {
            value.visit_origins(&mut Vec::new(), &mut |path, origin| {
                let source = origin.region.source;
                if origin.region.instance != RegionInstance::Source
                    && source.file == body.file
                    && source.start >= body.start
                    && source.end <= body.end
                {
                    regions.entry(origin.region.clone()).or_default().insert((
                        output,
                        path.to_vec(),
                        origin.mode,
                        origin.new,
                    ));
                }
            });
        }
        if !values
            .iter()
            .any(|value| value.has_array_layout() || value.creates_environment())
            && !regions.iter().any(|(region, occurrences)| {
                region.summarized()
                    || region.returned.is_some()
                    || occurrences.first().is_some_and(|(_, first, ..)| {
                        occurrences.iter().any(|(_, path, ..)| path != first)
                    })
            })
        {
            return;
        }
        // Published indices are ordered by the shape visible to the caller.
        let mut by_shape: Vec<_> = regions
            .into_iter()
            .map(|(region, paths)| (paths, region.summarized(), region))
            .collect();
        by_shape.sort_unstable();
        let identities: BTreeMap<_, _> = by_shape
            .into_iter()
            .enumerate()
            .map(|(index, (_, summarized, region))| {
                (region, AllocationIdentity { index, summarized })
            })
            .collect();
        for value in values {
            value.transform(&mut |origin| {
                origin.return_allocation = identities.get(&origin.region).copied();
            });
        }
    }

    pub(in crate::access) fn return_allocations(values: &[Self]) -> Vec<ReturnAllocation> {
        let mut allocations = BTreeSet::new();
        for value in values {
            value.visit_nodes(&mut Vec::new(), &mut |path, node| {
                for origin in &node.roots {
                    let Some(AllocationIdentity { index, summarized }) = origin.return_allocation
                    else {
                        continue;
                    };
                    allocations.insert(ReturnAllocation {
                        path: path.to_vec(),
                        index,
                        access: origin.mode,
                        new: origin.new,
                        qualified: node.requires_new,
                        summarized,
                        clone_member: origin.clone_member,
                        array_len: node.array_len,
                        array_extent: origin.array_extent,
                    });
                }
            });
        }
        allocations.into_iter().collect()
    }

    pub(super) fn compact_snapshot(&mut self, local_data: impl Fn(Span) -> bool + Copy) -> bool {
        let mut plain = true;
        for member in self.members.values_mut() {
            plain &= member.compact_snapshot(local_data);
        }
        plain &= !self.requires_new
            && !self.result_fresh
            && !self.live_callable_state
            && !self.uses_ctl_handler
            && self.linear.is_empty()
            && self.results.is_empty()
            && self.latent_effects.is_empty()
            && self.latent_operations.is_empty()
            && self.latent_effect_vars.is_empty()
            && !self.latent_open_effect
            && !self.latent_direct_open_effect
            && self.environments.is_empty()
            && self.publications.is_empty()
            && self.invocations.is_empty()
            && self.roots.iter().all(|origin| {
                origin.mode == Access::Immutable
                    && origin.region.instance != RegionInstance::Source
                    && local_data(origin.region.source)
                    && origin.callback_result.is_none()
                    && origin.snapshot_provider.is_none()
                    && origin.confined.is_none()
            });
        if plain && !self.roots.is_empty() {
            // A frozen, locally allocated graph cannot carry caller sources
            // or writable edges. Its root suffices for later projections.
            self.members.clear();
        }
        plain
    }

    pub(super) fn size(&self) -> usize {
        1 + self.roots.len() + self.members.values().map(Self::size).sum::<usize>()
    }

    pub(super) fn fold_old_allocations(&mut self, members: &mut BTreeMap<Region, Self>) {
        for member in self.members.values_mut() {
            member.fold_old_allocations(members);
        }
        if !self
            .roots
            .iter()
            .any(|root| root.region.instance == RegionInstance::PriorAllocations)
            || self.roots.iter().any(|root| {
                root.detached_snapshot || root.region.instance == RegionInstance::Source
            })
        {
            return;
        }
        let parents: BTreeSet<_> = self.roots.iter().map(|root| &root.region).collect();
        // Earlier instances can come from different branches. If a join has
        // lost the association between a parent and its fields, keep the
        // possible edges for each represented allocation.
        for (coordinate, mut member) in std::mem::take(&mut self.members) {
            member.transform(&mut |origin| origin.branches.clear());
            for parent in &parents {
                let mut slot = (*parent).clone();
                slot.selection.push(coordinate.clone());
                merge_member(members, slot, member.clone());
            }
        }
    }

    pub(super) fn remember_return_graph(
        &self,
        members: &mut BTreeMap<Region, Self>,
        extents: &mut BTreeMap<Region, Option<ArrayExtent>>,
        call: Span,
    ) {
        let allocations = self
            .roots
            .iter()
            .filter(|root| root.region.source == call && root.region.returned.is_some());
        let mut parents = BTreeSet::new();
        for root in allocations {
            parents.insert(&root.region);
            if !root.region.summarized() {
                extents
                    .entry(root.region.clone())
                    .and_modify(|known| {
                        *known = known
                            .zip(root.array_extent)
                            .map(|(left, right)| left.meet(right));
                    })
                    .or_insert(root.array_extent);
            }
        }
        for (coordinate, member) in &self.members {
            for parent in &parents {
                let mut slot = (*parent).clone();
                slot.selection.push(coordinate.clone());
                merge_member(members, slot, member.clone());
            }
            member.remember_return_graph(members, extents, call);
        }
    }

    pub(in crate::access) fn has_call_graph(&self, call: Span) -> bool {
        self.origins()
            .any(|origin| origin.region.source == call && origin.region.returned.is_some())
    }

    pub(in crate::access) fn accepts_snapshot_sources(
        &self,
        symbolic: &mut impl FnMut(&Origin) -> bool,
    ) -> bool {
        self.snapshot_graph(&[], &mut |root, owned, _| {
            root.can_freeze(owned) || symbolic(root)
        })
    }

    pub(in crate::access) fn snapshot_graph(
        &self,
        replaced: &[Vec<Coordinate>],
        inspect: &mut impl FnMut(&Origin, bool, &[Vec<Coordinate>]) -> bool,
    ) -> bool {
        self.visit_snapshot_graph(self.requires_new, replaced, inspect)
    }

    pub(in crate::access) fn snapshot_shape_depth(&self) -> usize {
        self.roots
            .iter()
            .map(|root| root.region.selection.len())
            .chain(
                self.members
                    .values()
                    .map(|member| 1 + member.snapshot_shape_depth()),
            )
            .max()
            .unwrap_or_default()
    }

    pub(in crate::access) fn widen_snapshot_graph(&mut self) {
        let live_callable_state = self.contains_live_callable_environment();
        let mut roots = BTreeSet::new();
        self.snapshot_graph(&[], &mut |origin, owned, _| {
            let new = owned && origin.new;
            let mut source = Self::source(origin.region.source, origin.mode, new);
            for root in &mut source.roots {
                root.call_scoped_access = origin.call_scoped_access;
                root.snapshot_provider = origin.snapshot_provider;
                root.detached_snapshot = origin.detached_snapshot;
                root.inherits_mode = origin.inherits_mode;
                root.entry_graph = origin.entry_graph.as_ref().map(|entry| EntryGraph {
                    callable: entry.callable,
                    new_qualified: entry.new_qualified,
                    shared_at: None,
                    via_at: Vec::new(),
                });
                roots.insert(root.clone());
            }
            true
        });
        *self = Self {
            roots: roots.into_iter().collect(),
            requires_new: self.requires_new,
            live_callable_state,
            ..Self::default()
        };
    }

    pub(super) fn visit_snapshot_graph(
        &self,
        owned: bool,
        replaced: &[Vec<Coordinate>],
        inspect: &mut impl FnMut(&Origin, bool, &[Vec<Coordinate>]) -> bool,
    ) -> bool {
        self.roots.iter().all(|root| inspect(root, owned, replaced))
            && self.members.iter().all(|(coordinate, member)| {
                let replaced: Vec<_> = replaced
                    .iter()
                    .filter_map(|path| path.strip_prefix(std::slice::from_ref(coordinate)))
                    .map(<[_]>::to_vec)
                    .collect();
                replaced.iter().any(Vec::is_empty)
                    || member.visit_snapshot_graph(
                        owned && self.environments.is_empty(),
                        &replaced,
                        inspect,
                    )
            })
    }

    pub(in crate::access) fn specialize_snapshot_sources(&mut self) {
        self.specialize_freezable_sources(self.requires_new);
    }

    pub(super) fn specialize_freezable_sources(&mut self, owned: bool) {
        for root in &mut self.roots {
            if !root.can_freeze(owned) {
                root.fix_mode(Access::Immutable);
                root.new = false;
            }
        }
        for member in self.members.values_mut() {
            member.specialize_freezable_sources(owned && self.environments.is_empty());
        }
    }

    pub(in crate::access) fn freeze(&mut self) {
        for root in &mut self.roots {
            root.fix_mode(Access::Immutable);
            root.new = false;
            root.from_variable = false;
        }
        for member in self.members.values_mut() {
            member.freeze();
        }
        self.requires_new = false;
    }

    pub(super) fn apply_draft_update(
        &mut self,
        path: &[Coordinate],
        stored: &Self,
        definite: bool,
    ) {
        let Some((coordinate, rest)) = path.split_first() else {
            *self = if definite {
                stored.clone()
            } else {
                std::mem::take(self).joined(stored.clone())
            };
            return;
        };
        let append;
        let coordinate = if matches!(coordinate, Coordinate::ArrayTail(_)) && rest.is_empty() {
            append = self.draft_append_coordinate(definite);
            &append
        } else {
            coordinate
        };
        if coordinate.is_range() {
            let mut indexed: Vec<_> = self
                .members
                .keys()
                .filter(|key| coordinate.covers(key))
                .cloned()
                .collect();
            if !indexed.contains(coordinate) {
                indexed.push(coordinate.clone());
            }
            for coordinate in indexed {
                let mut member = self.project(coordinate.clone(), Access::Immutable);
                member.apply_draft_update(rest, stored, false);
                self.members.insert(coordinate, member);
            }
        } else {
            let mut member = self.project(coordinate.clone(), Access::Immutable);
            member.apply_draft_update(rest, stored, definite);
            self.members.insert(coordinate.clone(), member);
        }
    }

    pub(super) fn draft_append_coordinate(&mut self, definite: bool) -> Coordinate {
        let extent = self
            .roots
            .iter()
            .map(|root| root.array_extent.unwrap_or_default())
            .reduce(ArrayExtent::meet)
            .unwrap_or_default();
        let next = (definite && extent.exact)
            .then(|| extent.minimum.checked_add(1))
            .flatten();
        self.array_len = self.array_len.and(next);
        for root in &mut self.roots {
            root.array_extent = Some(ArrayExtent {
                minimum: next.unwrap_or(extent.minimum),
                exact: next.is_some(),
            });
        }
        next.map_or(Coordinate::ArrayTail(extent.minimum), |_| {
            Coordinate::Index(extent.minimum.to_string())
        })
    }

    pub(in crate::access) fn join_draft_results(mut self, mut other: Self) -> Self {
        let fields: BTreeSet<_> = self
            .members
            .keys()
            .chain(other.members.keys())
            .cloned()
            .collect();
        // A store may materialize a field in just one alternative. Project
        // the corresponding entry source in the other alternative.
        let members = fields
            .into_iter()
            .map(|coordinate| {
                let left = self.project(coordinate.clone(), Access::Immutable);
                let right = other.project(coordinate.clone(), Access::Immutable);
                (coordinate, left.join_draft_results(right))
            })
            .collect();
        self.members.clear();
        other.members.clear();
        let mut result = self.joined(other);
        result.members = members;
        result
    }

    pub(in crate::access) fn receive_binding(&mut self, access: Access) {
        if access != Access::Immutable {
            self.forget_collection_layout();
        }
        for root in &mut self.roots {
            root.fix_mode(access);
            root.from_variable = false;
            if matches!(access, Access::Ref | Access::Shared) {
                root.new = false;
            }
        }
        self.requires_new = false;
    }

    pub(in crate::access) fn has_array_layout(&self) -> bool {
        self.array_len.is_some()
            || self.roots.iter().any(|root| root.array_extent.is_some())
            || self.members.values().any(Self::has_array_layout)
    }

    pub(in crate::access) fn forget_collection_layout(&mut self) {
        self.array_len = None;
        self.map_keys = None;
        for member in self.members.values_mut() {
            member.forget_collection_layout();
        }
    }
}

impl Ledger {
    pub(in crate::access) fn begin_draft(
        &mut self,
        (span, invocation): (Span, &[InvocationSite]),
        base: &Datum,
    ) -> Datum {
        let working = self.snapshot_for_draft(base);
        let mut region = Region::allocation(span);
        region.set_invocation(invocation);
        self.drafts.insert(region.clone(), working);
        let mut cursor = Datum::source(span, Access::Mut, true);
        cursor.transform(&mut |root| {
            root.region = region.clone();
            root.draft = true;
            root.confined = Some(span);
        });
        cursor
    }

    pub(in crate::access) fn finish_draft(&mut self, cursor: &Datum) -> Option<Datum> {
        let mut result = self.drafts.remove(&cursor.roots.first()?.region)?;
        result.freeze();
        Some(result)
    }

    pub(in crate::access) fn has_deferred_draft_access(&self, cursor: &Datum) -> bool {
        cursor.roots.first().is_some_and(|cursor| {
            self.storage_flow
                .iter()
                .flat_map(StorageFlow::values)
                .flat_map(Datum::origins)
                .any(|root| root.draft && root.region.allocation_root() == cursor.region)
        })
    }

    pub(in crate::access) fn read_draft(&self, cursor: &Datum) -> Option<Datum> {
        cursor.roots.iter().try_fold(None, |selected, origin| {
            if !origin.draft {
                return None;
            }
            let working = self.drafts.get(&origin.region.allocation_root())?;
            let value = origin
                .region
                .selection
                .iter()
                .fold(working.clone(), |value, step| {
                    value.project(step.clone(), Access::Immutable)
                });
            Some(join_member(selected, value))
        })?
    }

    pub(in crate::access) fn enter_capture_storage(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        includes: impl Fn(Span) -> bool,
    ) {
        self.capture_owner = Some(owner);
        self.capture_updates.clear();
        self.storage_formals = formals.to_vec();
        self.storage_captures = self.slots.keys().copied().collect();
        self.storage_flow = None;
        self.storage_samples.clear();
        for (&binding, slot) in &mut self.slots {
            if includes(binding) && !slot.value.roots.is_empty() {
                slot.value.capture_paths.insert(
                    CapturePath {
                        owner,
                        region: Region::root(binding),
                    },
                    true,
                );
            }
        }
    }

    pub(super) fn storage_prefix(&self) -> StorageFlow {
        StorageFlow::writes(self.capture_owner.map_or_else(BTreeMap::new, |owner| {
            self.call_updates(owner, &self.storage_formals, &self.storage_captures)
        }))
    }

    pub(in crate::access) fn defer_storage_call(&mut self, mut call: DeferredStorageCall) {
        let mut flow = self
            .storage_flow
            .take()
            .unwrap_or_else(|| self.storage_prefix());
        self.capture_array_extents(&mut call.receiver);
        for (_, _, argument) in &mut call.arguments {
            self.capture_array_extents(argument);
        }
        self.invalidate_callback_array_extents(
            std::iter::once(&call.receiver).chain(call.arguments.iter().map(|(_, _, value)| value)),
        );
        flow.push(StorageAction::Invoke(call));
        self.storage_flow = Some(flow);
    }

    pub(in crate::access) fn defer_storage_derive(
        &mut self,
        index: usize,
        base: &Datum,
        updater: &Datum,
    ) {
        let mut flow = self
            .storage_flow
            .take()
            .unwrap_or_else(|| self.storage_prefix());
        let base = self.snapshot_call_graph(base);
        let updater = self.snapshot_call_graph(updater);
        self.invalidate_callback_array_extents(std::iter::once(&updater));
        flow.push(StorageAction::Derive {
            index,
            base,
            updater,
        });
        self.storage_flow = Some(flow);
    }

    pub(in crate::access) fn defer_storage_clone(&mut self, index: usize, base: Datum) {
        let mut flow = self
            .storage_flow
            .take()
            .unwrap_or_else(|| self.storage_prefix());
        flow.push(StorageAction::Clone { index, base });
        self.storage_flow = Some(flow);
    }

    pub(super) fn invalidate_callback_array_extents<'a>(
        &mut self,
        operands: impl Iterator<Item = &'a Datum>,
    ) {
        if self.array_extents.is_empty() {
            return;
        }
        // A callback can reach its operands and storage already exposed to
        // the caller, including aliases retained by its environment.
        let published = self.replacements.values().filter_map(|update| {
            let owner = self.capture_owner?;
            (update.value.publications.get(&owner) == Some(&true)).then_some(&update.value)
        });
        let mut exposed = BTreeSet::new();
        let mut expose = |operand: &Datum| {
            let graph = self.snapshot(operand);
            exposed.extend(graph.origins().map(|root| root.region.clone()));
        };
        operands.for_each(&mut expose);
        published.for_each(expose);
        for (array, extent) in &mut self.array_extents {
            if exposed.iter().any(|source| source.overlaps(array)) {
                // Keep the initialized identity so an older occurrence of
                // the same array cannot restore its original length.
                *extent = ArrayExtent {
                    minimum: 0,
                    exact: false,
                };
            }
        }
    }

    pub(in crate::access) fn record_storage_read(
        &mut self,
        index: usize,
        base: &Datum,
        coordinate: Coordinate,
        mode: Mode,
        selected: &mut Datum,
    ) {
        if selected.roots.is_empty() || self.storage_flow.is_none() {
            return;
        }
        let base = self.snapshot_call_graph(base);
        if let Some(flow) = &mut self.storage_flow {
            flow.push(StorageAction::Read {
                index,
                base,
                coordinate,
                mode,
            });
        }
        for root in &mut selected.roots {
            root.storage_read = Some(StorageRead {
                index,
                path: Vec::new(),
            });
        }
    }

    pub(in crate::access) fn sample_storage(
        &mut self,
        key: (Span, Vec<InvocationSite>, usize),
        value: Datum,
    ) {
        match self.storage_samples.entry(key) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(value);
            }
            std::collections::btree_map::Entry::Occupied(mut slot) => {
                let slot = slot.get_mut();
                *slot = std::mem::take(slot).joined(value);
            }
        }
    }

    pub(in crate::access) fn sampled_storage(
        &self,
        (span, invocation): (Span, &[InvocationSite]),
        read: &StorageRead,
    ) -> Option<Datum> {
        let mut value = self
            .storage_samples
            .get(&(span, invocation.to_vec(), read.index))?
            .clone();
        for coordinate in &read.path {
            value = self.project(&value, coordinate.clone(), Access::Mut);
        }
        Some(value)
    }

    pub(in crate::access) fn with_storage_samples(&self, current: &Self) -> Cow<'_, Self> {
        if self.storage_samples == current.storage_samples {
            Cow::Borrowed(self)
        } else {
            let mut entry = self.clone();
            entry.storage_samples.clone_from(&current.storage_samples);
            Cow::Owned(entry)
        }
    }

    pub(super) fn record_storage_write(
        &mut self,
        target: StorageTarget,
        value: &Datum,
        definite: bool,
    ) {
        if self.storage_flow.is_some() {
            let value = self.snapshot_call_graph(value);
            if let Some(flow) = &mut self.storage_flow {
                flow.push(StorageAction::Write(
                    target,
                    Replacement { value, definite },
                ));
            }
        }
    }

    pub(in crate::access) fn overwritten_paths(&self, root: &Region) -> Vec<Vec<Coordinate>> {
        self.replacements
            .iter()
            .filter_map(|(path, update)| {
                let tail = path.selection.strip_prefix(&root.selection[..])?;
                (update.definite
                    && !tail.is_empty()
                    && path.overlaps(root)
                    && !path.selection.iter().any(Coordinate::is_range))
                .then(|| tail.to_vec())
            })
            .collect()
    }

    pub(in crate::access) fn snapshot_overwrites(&self, value: &Datum) -> Vec<Vec<Coordinate>> {
        let alternatives: Vec<_> = value
            .roots
            .iter()
            .map(|root| {
                if root.detached_snapshot {
                    Vec::new()
                } else {
                    self.overwritten_paths(&root.region)
                }
            })
            .collect();
        let candidates: BTreeSet<_> = alternatives.iter().flatten().collect();
        candidates
            .into_iter()
            .filter(|path| {
                alternatives
                    .iter()
                    .all(|writes| writes.iter().any(|written| path.starts_with(written)))
            })
            .cloned()
            .collect()
    }

    pub(in crate::access) fn restore_snapshot_overwrites(
        &mut self,
        value: &Datum,
        paths: &[Vec<Coordinate>],
    ) {
        for path in paths {
            let Some((step, parent_path)) = path.split_last() else {
                continue;
            };
            let Some(parent) = parent_path
                .iter()
                .try_fold(value, |node, coordinate| node.members.get(coordinate))
            else {
                continue;
            };
            if let Some(stored) = parent.members.get(step) {
                for origin in parent.slot_projection(step.clone()).roots {
                    if !origin.region.summarized()
                        && !origin.region.selection.iter().any(Coordinate::is_range)
                    {
                        self.replace_region(&origin.region, stored, true);
                    }
                }
            }
        }
    }

    pub(in crate::access) fn snapshot(&self, value: &Datum) -> Datum {
        if self.replacements.is_empty() && self.loop_members.is_empty() {
            return value.clone();
        }
        self.snapshot_members(value, &mut BTreeSet::new())
    }

    pub(in crate::access) fn snapshot_call_graph(&self, value: &Datum) -> Datum {
        let mut snapshot = self.snapshot(value);
        self.capture_array_extents(&mut snapshot);
        snapshot
    }

    pub(super) fn snapshot_for_draft(&self, value: &Datum) -> Datum {
        let mut snapshot = self.snapshot(value);
        snapshot.transform(&mut |root| {
            // Imported allocations can carry their initial extent before
            // the caller has installed it in the ledger.
            root.array_extent = self.array_extent(root).or(root.array_extent);
            root.detached_snapshot = true;
        });
        snapshot
    }

    pub(super) fn capture_array_extents(&self, value: &mut Datum) {
        value.transform(&mut |root| {
            root.array_extent = self
                .array_extent(root)
                .filter(|extent| extent.exact || extent.minimum > 0);
        });
    }

    pub(super) fn snapshot_members(
        &self,
        value: &Datum,
        ancestors: &mut BTreeSet<(Region, Access)>,
    ) -> Datum {
        let mut snapshot = value.clone();
        let regions: BTreeSet<_> = value
            .roots
            .iter()
            .filter(|root| !root.detached_snapshot)
            .map(|root| (root.region.clone(), root.mode))
            .filter(|root| !ancestors.contains(root))
            .collect();
        ancestors.extend(regions.iter().cloned());
        let mut coordinates: BTreeSet<_> = value.members.keys().cloned().collect();
        for key in self.replacements.keys().chain(self.loop_members.keys()) {
            for (region, _) in &regions {
                if key.overlaps(region)
                    && let Some(coordinate) = key.selection.get(region.selection.len())
                {
                    coordinates.insert(coordinate.clone());
                }
            }
        }
        for coordinate in coordinates {
            let member = self.project_members(
                value,
                coordinate.clone(),
                Mode::Mut,
                |root| regions.contains(&(root.region.clone(), root.mode)),
                // A symbolic root already represents its entry graph. During
                // a snapshot, invent a path only to reach a tracked store.
                |region| {
                    self.replacements.keys().any(|target| {
                        region.selection.len() <= target.selection.len() && region.overlaps(target)
                    })
                },
            );
            snapshot
                .members
                .insert(coordinate, self.snapshot_members(&member, ancestors));
        }
        for region in regions {
            ancestors.remove(&region);
        }
        snapshot
    }
}
