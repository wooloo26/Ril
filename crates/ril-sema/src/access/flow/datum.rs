use super::*;

impl Datum {
    pub(in crate::access) fn source(span: Span, mode: Access, new: bool) -> Self {
        Self {
            roots: vec![Origin {
                region: if new {
                    Region::allocation(span)
                } else {
                    Region::root(span)
                },
                mode,
                inherits_mode: false,
                callback_result: None,
                storage_read: None,
                array_extent: None,
                snapshot_provider: None,
                clone_member: false,
                detached_snapshot: false,
                return_allocation: None,
                reception: Vec::new(),
                new,
                explicit_share: false,
                from_variable: false,
                call_scoped_access: false,
                entry_graph: None,
                capture: None,
                dependencies: BTreeSet::new(),
                anchor_scopes: BTreeSet::new(),
                branches: BTreeMap::new(),
                variant: None,
                confined: None,
                draft: false,
            }],
            requires_new: new,
            ..Self::default()
        }
    }

    pub(in crate::access) fn origins(&self) -> Box<dyn Iterator<Item = &Origin> + '_> {
        Box::new(
            self.roots
                .iter()
                .chain(self.members.values().flat_map(Self::origins)),
        )
    }

    pub(in crate::access) fn enter_capture(
        &mut self,
        callable: Span,
        binding: Span,
        mode: Mode,
        inferred: bool,
        sources: &BTreeSet<Span>,
    ) {
        for root in &mut self.roots {
            if sources.contains(&root.region.source) {
                root.capture = Some(CaptureEntry {
                    callable,
                    binding,
                    inferred,
                    shared: mode == Mode::Shared,
                });
            }
        }
        for member in self.members.values_mut() {
            member.transform(&mut |origin| {
                if sources.contains(&origin.region.source) {
                    origin.capture = Some(CaptureEntry {
                        callable,
                        binding,
                        inferred,
                        shared: origin.mode == Access::Shared,
                    });
                }
            });
        }
    }

    pub(super) fn call_participants(&self, mode: Mode) -> impl Iterator<Item = (&Origin, Mode)> {
        self.roots.iter().map(move |origin| (origin, mode)).chain(
            self.members
                .values()
                .flat_map(Self::origins)
                .map(move |origin| {
                    let mode = if matches!(mode, Mode::Mut | Mode::New | Mode::Via)
                        && origin.mode == Access::Shared
                    {
                        Mode::Shared
                    } else {
                        mode
                    };
                    (origin, mode)
                }),
        )
    }

    pub(in crate::access) fn visit_origins(
        &self,
        path: &mut Vec<Coordinate>,
        visit: &mut impl FnMut(&[Coordinate], &Origin),
    ) {
        self.visit_nodes(path, &mut |path, node| {
            for origin in &node.roots {
                visit(path, origin);
            }
        });
    }

    pub(in crate::access) fn visit_nodes(
        &self,
        path: &mut Vec<Coordinate>,
        visit: &mut impl FnMut(&[Coordinate], &Self),
    ) {
        visit(path, self);
        for (coordinate, member) in &self.members {
            path.push(coordinate.clone());
            member.visit_nodes(path, visit);
            path.pop();
        }
    }

    pub(in crate::access) fn transform(&mut self, f: &mut impl FnMut(&mut Origin)) {
        self.roots.iter_mut().for_each(&mut *f);
        for member in self.members.values_mut() {
            member.transform(f);
        }
    }

    pub(in crate::access) fn retain_compatible_origins(&mut self, choices: &Choices) {
        self.roots
            .retain(|root| compatible(&root.branches, choices));
        for member in self.members.values_mut() {
            member.retain_compatible_origins(choices);
        }
    }

    pub(in crate::access) fn joined(mut self, mut other: Self) -> Self {
        self.materialize_range_alternatives(&other);
        other.materialize_range_alternatives(&self);
        if self.roots.is_empty() {
            self.capture_paths = std::mem::take(&mut other.capture_paths);
        } else if !other.roots.is_empty() {
            for (path, definite) in &mut self.capture_paths {
                *definite &= other.capture_paths.remove(path).unwrap_or(false);
            }
            self.capture_paths
                .extend(other.capture_paths.into_keys().map(|path| (path, false)));
        }
        self.roots.append(&mut other.roots);
        self.roots.sort_unstable();
        self.roots.dedup();
        // Widen branch correlations before fact growth makes nested branches impractical.
        if self.roots.len() > BRANCH_LIMIT {
            for root in &mut self.roots {
                root.branches.clear();
            }
            self.roots.sort_unstable();
            self.roots.dedup();
        }
        for (coordinate, value) in other.members {
            let slot = self.members.entry(coordinate).or_default();
            *slot = std::mem::take(slot).joined(value);
        }
        self.results.append(&mut other.results);
        self.linear.append(&mut other.linear);
        if self.array_len != other.array_len {
            self.array_len = None;
        }
        if self.map_keys != other.map_keys {
            self.map_keys = None;
        }
        self.requires_new &= other.requires_new;
        self.latent_effects.append(&mut other.latent_effects);
        self.latent_operations.append(&mut other.latent_operations);
        self.environments.append(&mut other.environments);
        for (owner, existing_storage) in other.publications {
            *self.publications.entry(owner).or_default() |= existing_storage;
        }
        for (owner, sources) in other.invocations {
            let captures = self.invocations.entry(owner).or_default();
            for (source, targets) in sources {
                captures.entry(source).or_default().extend(targets);
            }
        }
        self.live_callable_state |= other.live_callable_state;
        self.uses_ctl_handler |= other.uses_ctl_handler;
        self.is_once |= other.is_once;
        self.result_fresh &= other.result_fresh;
        self
    }

    pub(super) fn materialize_range_alternatives(&mut self, other: &Self) {
        if !self.members.keys().any(Coordinate::is_range) {
            return;
        }
        for coordinate in other.members.keys() {
            if matches!(coordinate, Coordinate::Index(_))
                && !self.members.contains_key(coordinate)
                && let Some(member) = self.known_member(coordinate)
            {
                self.members.insert(coordinate.clone(), member);
            }
        }
    }

    pub(in crate::access) fn project(&self, coordinate: Coordinate, mode: Access) -> Self {
        let mut value = self.project_schema(coordinate, mode.as_mode());
        value.receive_cloned_member(mode.as_mode());
        value
    }

    pub(super) fn project_schema(&self, coordinate: Coordinate, mode: Mode) -> Self {
        if let Some(mut member) = self.known_member(&coordinate) {
            self.project_capture_paths(&coordinate, &mut member, false);
            self.project_storage_read(&coordinate, &mut member);
            self.project_known(&mut member, &coordinate, mode);
            return member;
        }
        self.project_opaque(coordinate, mode)
    }

    pub(super) fn project_known(&self, member: &mut Self, coordinate: &Coordinate, mode: Mode) {
        if !self.roots.is_empty() && self.roots.iter().all(|root| root.draft) {
            // Access is to the draft path. The stored value may have come
            // from an immutable source that the update does not mutate.
            let path = self.project_opaque(coordinate.clone(), mode);
            member.roots = path.roots;
            member.requires_new = path.requires_new;
        } else {
            self.attenuate(member);
        }
    }

    pub(super) fn receive_cloned_member(&mut self, mode: Mode) {
        for root in &mut self.roots {
            if std::mem::take(&mut root.clone_member) {
                root.project_mode(mode);
                if matches!(mode, Mode::Ref | Mode::Shared | Mode::Via) {
                    root.new = false;
                }
            }
        }
    }

    pub(in crate::access) fn known_member(&self, coordinate: &Coordinate) -> Option<Self> {
        if coordinate.is_range() {
            self.members
                .iter()
                .filter(|(key, _)| {
                    coordinate.covers(key) || key.is_range() && key.covers(coordinate)
                })
                .map(|(_, value)| value.clone())
                .reduce(Self::joined)
        } else if let Some(value) = self.members.get(coordinate) {
            Some(value.clone())
        } else {
            let detached = self.roots.iter().any(|root| root.detached_snapshot);
            self.members
                .iter()
                .filter(|(key, _)| {
                    (matches!(coordinate, Coordinate::Index(_)) || detached)
                        && key.is_range()
                        && key.covers(coordinate)
                })
                .map(|(_, member)| member.clone())
                .reduce(Self::joined)
        }
    }

    pub(super) fn project_opaque(&self, coordinate: Coordinate, mode: Mode) -> Self {
        let roots: Vec<_> = self
            .roots
            .iter()
            .map(|origin| {
                let mut origin = origin.clone();
                origin.region.selection.push(coordinate.clone());
                if let Some(read) = &mut origin.storage_read {
                    read.path.push(coordinate.clone());
                }
                origin.array_extent = None;
                origin.snapshot_provider = None;
                origin.variant = None;
                origin.from_variable = false;
                if !origin.draft {
                    origin.project_mode(mode);
                    // The schema of an opaque member selection can expose authority
                    // which survived the transfer of its enclosing new object.
                    if matches!(mode, Mode::Ref | Mode::Shared | Mode::Via) {
                        origin.new = false;
                    }
                }
                origin
            })
            .collect();
        let mut member = Self {
            requires_new: self.requires_new && roots.iter().all(|root| root.new),
            roots,
            ..Self::default()
        };
        self.project_capture_paths(&coordinate, &mut member, false);
        member
    }

    pub(super) fn attenuate(&self, member: &mut Self) {
        member.requires_new &= self.requires_new;
        for root in &mut member.roots {
            root.from_variable = false;
            root.anchor_scopes
                .extend(self.roots.iter().flat_map(|parent| &parent.anchor_scopes));
        }
        if self.roots.iter().all(|root| !root.mode.writes()) {
            if self.roots.iter().all(|root| root.mode == Access::Immutable) {
                member.freeze();
            } else {
                member.transform(&mut |origin| {
                    origin.fix_mode(Access::Ref.project(origin.mode));
                    origin.new = false;
                });
                member.requires_new = false;
            }
        }
    }

    pub(in crate::access) fn slot_projection(&self, coordinate: Coordinate) -> Self {
        let mut roots = self.roots.clone();
        for root in &mut roots {
            // An observation selects the parent object. This coordinate
            // addresses a slot within that object.
            root.region.selection.push(coordinate.clone());
        }
        let mut slot = Self {
            roots,
            ..Self::default()
        };
        self.project_capture_paths(&coordinate, &mut slot, false);
        slot
    }

    pub(super) fn project_capture_paths(
        &self,
        coordinate: &Coordinate,
        member: &mut Self,
        stored: bool,
    ) {
        for (path, &definite) in &self.capture_paths {
            if !stored || !member.publications.contains_key(&path.owner) {
                let mut path = path.clone();
                path.region.selection.push(coordinate.clone());
                *member.capture_paths.entry(path).or_default() |= definite;
            }
        }
    }

    pub(super) fn project_storage_read(&self, coordinate: &Coordinate, member: &mut Self) {
        if let Some(read) = self
            .roots
            .first()
            .and_then(|root| root.storage_read.as_ref())
            && self
                .roots
                .iter()
                .all(|root| root.storage_read.as_ref() == Some(read))
        {
            let mut read = read.clone();
            read.path.push(coordinate.clone());
            for root in &mut member.roots {
                root.storage_read = Some(read.clone());
            }
        }
    }

    pub(in crate::access) fn creates_environment(&self) -> bool {
        !self.environments.is_empty() || self.members.values().any(Self::creates_environment)
    }

    pub(in crate::access) fn contains_live_callable_environment(&self) -> bool {
        self.live_callable_state
            || !self.environments.is_empty()
                && self
                    .members
                    .values()
                    .flat_map(Self::origins)
                    .any(|origin| origin.mode != Access::Immutable)
            || self
                .members
                .values()
                .any(Self::contains_live_callable_environment)
    }

    pub(in crate::access) fn cloned_graph(
        &self,
        span: Span,
        invocation: &[InvocationSite],
    ) -> Self {
        fn copy(
            value: &Datum,
            prototype: &Origin,
            regions: &mut BTreeMap<Region, Region>,
            member: bool,
        ) -> Datum {
            let mut roots = Vec::new();
            for original in &value.roots {
                let index = regions.len();
                let region = regions.entry(original.region.clone()).or_insert_with(|| {
                    let mut region = Region::returned(
                        prototype.region.source,
                        AllocationIdentity {
                            index,
                            summarized: original.region.summarized(),
                        },
                    );
                    region.set_invocation(&prototype.region.invocation);
                    region
                });
                roots.push(Origin {
                    region: region.clone(),
                    array_extent: original.array_extent,
                    snapshot_provider: original.snapshot_provider,
                    clone_member: member,
                    branches: original.branches.clone(),
                    variant: original.variant.clone(),
                    ..prototype.clone()
                });
            }
            let array_len = roots.first().and_then(|root| {
                let extent = root.array_extent?;
                (extent.exact && roots.iter().all(|root| root.array_extent == Some(extent)))
                    .then_some(extent.minimum)
            });
            let members = if value.environments.is_empty() {
                value
                    .members
                    .iter()
                    .map(|(key, value)| (key.clone(), copy(value, prototype, regions, true)))
                    .collect()
            } else {
                // A callable keeps the immutable sources in its environment.
                value.members.clone()
            };
            Datum {
                requires_new: !roots.is_empty(),
                roots,
                members,
                array_len,
                latent_effects: value.latent_effects.clone(),
                environments: value.environments.clone(),
                invocations: value.invocations.clone(),
                live_callable_state: value.live_callable_state,
                result_fresh: value.result_fresh,
                ..Datum::default()
            }
        }

        let mut fresh = Self::source(span, Access::Mut, true);
        let Some(prototype) = fresh.roots.first_mut() else {
            return fresh;
        };
        prototype.region.set_invocation(invocation);
        if self.roots.is_empty() {
            return fresh;
        }
        copy(self, prototype, &mut BTreeMap::new(), false)
    }

    pub(in crate::access) fn surviving_publications(
        &self,
        owner: Span,
        caller_root: bool,
        visit: &mut impl FnMut(&Self),
    ) {
        if self
            .publications
            .get(&owner)
            .is_some_and(|&existing| caller_root || existing)
        {
            visit(self);
        } else {
            for member in self.members.values() {
                member.surviving_publications(owner, caller_root, visit);
            }
        }
    }

    pub(in crate::access) fn writers(&self) -> bool {
        !self.roots.is_empty() && self.roots.iter().all(|root| root.mode.writes())
    }

    pub(in crate::access) fn returns_call_scoped_writer(&self, mode: Mode) -> bool {
        let call_scoped_writer =
            |origin: &Origin| origin.call_scoped_access && origin.mode.writes();
        (matches!(mode, Mode::Infer | Mode::New | Mode::Shared)
            && self.roots.iter().any(call_scoped_writer))
            || self
                .members
                .values()
                .flat_map(Self::origins)
                .any(call_scoped_writer)
    }

    pub(in crate::access) fn detach_handed_off_paths(&mut self) {
        let ended: BTreeSet<_> = self
            .roots
            .iter()
            .flat_map(|origin| origin.dependencies.iter().copied())
            .collect();
        self.transform(&mut |origin| {
            origin.dependencies.retain(|token| !ended.contains(token));
        });
        for root in &mut self.roots {
            root.new = true;
            root.inherits_mode = false;
            root.reception.clear();
        }
        self.requires_new = true;
    }

    pub(in crate::access) fn all_linear(&self) -> BTreeSet<LinearOccurrence> {
        let mut out = self.linear.clone();
        for member in self.members.values() {
            out.extend(member.all_linear());
        }
        out
    }

    pub(in crate::access) fn clear_linear(&mut self) {
        self.linear.clear();
        for member in self.members.values_mut() {
            member.clear_linear();
        }
    }

    pub(in crate::access) fn root_dependencies(&self) -> impl Iterator<Item = Span> + '_ {
        self.roots.iter().flat_map(|origin| {
            origin
                .dependency_spans()
                .chain(std::iter::once(origin.region.source))
        })
    }
}

pub(super) fn merge_member(members: &mut BTreeMap<Region, Datum>, slot: Region, member: Datum) {
    match members.entry(slot) {
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            let value = entry.get_mut();
            *value = std::mem::take(value).joined(member);
        }
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(member);
        }
    }
}

pub(super) fn join_member(left: Option<Datum>, right: Datum) -> Option<Datum> {
    Some(match left {
        Some(left) => left.joined(right),
        None => right,
    })
}
