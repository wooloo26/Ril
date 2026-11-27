use super::*;

impl Datum {
    pub(in crate::access) fn results(&self) -> BTreeSet<ResultOccurrence> {
        self.root_results()
            .into_iter()
            .chain(self.members.values().flat_map(Self::results))
            .collect()
    }

    pub(in crate::access) fn root_results(&self) -> BTreeSet<ResultOccurrence> {
        self.results
            .iter()
            .map(|item| item.occurrence.clone())
            .collect()
    }

    pub(in crate::access) fn collection_results(&self) -> BTreeSet<ResultOccurrence> {
        self.results
            .iter()
            .filter(|item| item.occurrence.collection_elements)
            .map(|item| item.occurrence.clone())
            .collect()
    }

    pub(in crate::access) fn guaranteed_collection_result(
        &self,
        active: &Choices,
    ) -> Option<ResultOccurrence> {
        let mut collections = self.collection_results().into_iter();
        let item = collections.next()?;
        if collections.next().is_some() || self.roots.is_empty() {
            return None;
        }
        self.roots
            .iter()
            .all(|root| self.references_result(root, &item, active))
            .then_some(item)
    }

    pub(super) fn references_result(
        &self,
        root: &Origin,
        item: &ResultOccurrence,
        choices: &Choices,
    ) -> bool {
        self.results.iter().any(|reference| {
            &reference.occurrence == item
                && reference.branches.iter().all(|(key, arm)| {
                    choices.get(key).or_else(|| root.branches.get(key)) == Some(arm)
                })
        })
    }

    pub(super) fn contains_root_result(&self, item: &ResultOccurrence, choices: &Choices) -> bool {
        // A nested result can be absent altogether on some paths, for
        // example inside the payload of a sum's other variant.
        self.roots.iter().any(|root| {
            root.branches
                .iter()
                .all(|(key, arm)| choices.get(key) == Some(arm))
        }) && self.tests_root_result(item, choices)
    }

    pub(super) fn tests_root_result(&self, item: &ResultOccurrence, choices: &Choices) -> bool {
        let mut roots = self
            .roots
            .iter()
            .filter(|root| compatible(&root.branches, choices))
            .peekable();
        roots.peek().is_some() && roots.all(|root| self.references_result(root, item, choices))
    }

    pub(super) fn contains_result(&self, item: &ResultOccurrence, choices: &Choices) -> bool {
        self.contains_root_result(item, choices)
            || self
                .members
                .values()
                .any(|member| member.contains_result(item, choices))
    }

    pub(in crate::access) fn has_root_result(&self) -> bool {
        !self.results.is_empty()
    }

    pub(in crate::access) fn set_variant(&mut self, variant: &str) {
        for root in &mut self.roots {
            root.variant = Some(variant.into());
        }
    }

    pub(in crate::access) fn forget_variants(&mut self) {
        self.transform(&mut |origin| origin.variant = None);
    }

    pub(in crate::access) fn forget_results(&mut self) {
        self.rewrite_results(&mut |_| None);
    }

    pub(in crate::access) fn choose_variant(&mut self, variant: &str, key: Occurrence, arm: usize) {
        self.set_variant(variant);
        self.transform(&mut |origin| {
            origin.branches.insert(key, arm);
        });
        self.stamp_results(&Choices::from([(key, arm)]));
    }

    pub(in crate::access) fn result_object(&self) -> Option<&Region> {
        let region = &self.roots.first()?.region;
        (region.instance == RegionInstance::Allocation
            && !region.summarized()
            && self.roots.iter().all(|root| root.region == *region))
        .then_some(region)
    }

    pub(in crate::access) fn known_variant(&self) -> Option<&str> {
        let variant = self.roots.first()?.variant.as_deref()?;
        self.roots
            .iter()
            .all(|root| root.variant.as_deref() == Some(variant))
            .then_some(variant)
    }

    pub(super) fn stamp_results(&mut self, choices: &Choices) {
        if choices.is_empty() {
            return;
        }
        self.rewrite_results(&mut |mut item| {
            item.branches
                .extend(choices.iter().map(|(&key, &arm)| (key, arm)));
            Some(item)
        });
    }

    pub(super) fn select_results(&mut self, choices: &Choices) {
        self.rewrite_results(&mut |item| compatible(&item.branches, choices).then_some(item));
    }

    pub(super) fn select_variants(&mut self, choices: &Choices) {
        self.roots
            .retain(|root| compatible(&root.branches, choices));
        for member in self.members.values_mut() {
            member.select_variants(choices);
        }
    }

    pub(super) fn rewrite_results(
        &mut self,
        transform: &mut impl FnMut(ResultReference) -> Option<ResultReference>,
    ) {
        self.results = std::mem::take(&mut self.results)
            .into_iter()
            .filter_map(&mut *transform)
            .collect();
        for member in self.members.values_mut() {
            member.rewrite_results(transform);
        }
    }

    pub(super) fn remap_results(
        &mut self,
        carried: &BTreeMap<ResultOccurrence, ResultOccurrence>,
        age_choices: impl Fn(&mut Choices),
    ) {
        if carried.is_empty() && self.results().is_empty() {
            return;
        }
        self.rewrite_results(&mut |mut item| {
            if let Some(target) = carried.get(&item.occurrence) {
                if target.places.is_empty() {
                    return None;
                }
                item.occurrence = target.clone();
            }
            age_choices(&mut item.branches);
            Some(item)
        });
    }

    pub(super) fn result_places(
        &self,
        holder: ResultHolder,
        path: &mut Vec<Coordinate>,
        results: &mut BTreeMap<ResultOccurrence, ResultOccurrence>,
    ) {
        for item in &self.results {
            if let Some(carried) = results.get_mut(&item.occurrence) {
                carried.places.insert((holder, path.clone()));
            }
        }
        for (step, member) in &self.members {
            path.push(step.clone());
            member.result_places(holder, path, results);
            path.pop();
        }
    }
}

impl Ledger {
    pub(in crate::access) fn clear_result_obligations(&mut self) {
        self.obligations.clear();
        self.pending_result_paths.clear();
        self.result_samples.clear();
        self.lost_results.clear();
    }

    pub(in crate::access) fn pending_results(&self) -> impl Iterator<Item = &ResultOccurrence> {
        self.obligations
            .difference(&self.inspected)
            .filter(|item| self.result_may_be_pending(item, &self.choices))
    }

    pub(in crate::access) fn result_pending(&self, item: &ResultOccurrence) -> bool {
        self.result_pending_on(item, &self.choices)
    }

    pub(super) fn result_pending_on(&self, item: &ResultOccurrence, choices: &Choices) -> bool {
        self.obligations.contains(item)
            && !self.inspected.contains(item)
            && self.result_may_be_pending(item, choices)
    }

    pub(super) fn result_may_be_pending(&self, item: &ResultOccurrence, choices: &Choices) -> bool {
        compatible(&item.created_in, choices)
            && self
                .pending_result_paths
                .get(item)
                .is_none_or(|paths| paths.iter().any(|branch| compatible(branch, choices)))
    }

    pub(in crate::access) fn result_inspected(&self, item: &ResultOccurrence) -> bool {
        self.inspected.contains(item) || !self.result_may_be_pending(item, &self.choices)
    }

    pub(super) fn pending_paths(
        &self,
        item: &ResultOccurrence,
        choices: &Choices,
    ) -> impl Iterator<Item = Choices> {
        let paths = self.pending_result_paths.get(item);
        paths
            .into_iter()
            .flatten()
            .filter(|path| compatible(path, choices))
            .cloned()
            .chain(paths.is_none().then(Choices::new))
    }

    pub(in crate::access) fn remember_return_graph(&mut self, value: &Datum, call: Span) {
        let mut extents = BTreeMap::new();
        value.remember_return_graph(&mut self.loop_members, &mut extents, call);
        for (region, extent) in extents {
            if let Some(extent) = extent {
                self.array_extents.entry(region).or_insert(extent);
            }
        }
    }

    pub(in crate::access) fn reset_revocations(&mut self) {
        self.revoked.clear();
    }

    pub(in crate::access) fn revoke(&mut self, token: Occurrence, origin: Option<&Origin>) {
        let mut choices = self.choices.clone();
        if let Some(origin) = origin {
            choices.extend(origin.branches.iter().map(|(&branch, &arm)| (branch, arm)));
        }
        let alternatives = self.revoked.entry(token).or_default();
        alternatives.insert(choices);
        Self::widen_choices(alternatives);
    }

    pub(super) fn widen_choices(alternatives: &mut BTreeSet<Choices>) {
        if alternatives.len() > BRANCH_LIMIT {
            alternatives.clear();
            alternatives.insert(Choices::new());
        }
    }

    pub(in crate::access) fn hold_conflicts(
        &self,
        value: &Datum,
        mode: Mode,
    ) -> Vec<AccessConflict> {
        if self.holds.is_empty() {
            return Vec::new();
        }
        let value = self.loop_snapshot(value);
        let mut result = Vec::new();
        for (held_mode, held) in &self.holds {
            result.extend(conflicts(
                &value,
                mode,
                &self.loop_snapshot(held),
                *held_mode,
            ));
        }
        result
    }

    pub(in crate::access) fn stamp(&self, value: &mut Datum) {
        value.transform(&mut |origin| {
            origin
                .branches
                .extend(self.choices.iter().map(|(&k, &v)| (k, v)));
        });
        value.stamp_results(&self.choices);
    }

    pub(in crate::access) fn take_choice(&mut self, span: Span, arm: usize) {
        let key = span.into();
        self.choices.insert(key, arm);
        let selected = Choices::from([(key, arm)]);
        for slot in self.slots.values_mut() {
            slot.value.transform(&mut |origin| {
                origin.branches.insert(key, arm);
            });
            slot.value.stamp_results(&selected);
        }
        for replacement in self
            .replacements
            .values_mut()
            .chain(self.capture_updates.values_mut())
        {
            replacement.value.transform(&mut |origin| {
                origin.branches.insert(key, arm);
            });
            replacement.value.stamp_results(&selected);
        }
    }

    pub(in crate::access) fn record_result(&mut self, value: &mut Datum, span: Span) {
        self.record_result_part(value, span, 0, &self.choices.clone(), false);
    }

    pub(in crate::access) fn record_result_part(
        &mut self,
        value: &mut Datum,
        span: Span,
        part: usize,
        choices: &Choices,
        collection_elements: bool,
    ) {
        let occurrence = ResultOccurrence {
            span,
            part,
            collection_elements,
            places: BTreeSet::new(),
            created_in: choices.clone(),
        };
        self.obligations.insert(occurrence.clone());
        value.results.insert(ResultReference {
            occurrence,
            branches: choices.clone(),
        });
    }

    pub(in crate::access) fn register_result_samples(
        &mut self,
        samples: &BTreeSet<ResultOccurrence>,
        collections: &BTreeSet<ResultOccurrence>,
    ) {
        for sample in samples {
            self.result_samples
                .insert(sample.clone(), collections.clone());
        }
    }

    pub(in crate::access) fn lose_collection_elements_at(&mut self, place: &Datum) {
        let mut lost = BTreeSet::new();
        for value in self
            .slots
            .values()
            .map(|slot| &slot.value)
            .chain(self.replacements.values().map(|update| &update.value))
            .chain(self.loop_members.values())
        {
            value.visit_nodes(&mut Vec::new(), &mut |_, node| {
                if node.roots.iter().any(|array| {
                    place.roots.iter().any(|slot| {
                        slot.region.selection.len() > array.region.selection.len()
                            && slot.overlaps(array)
                    })
                }) {
                    lost.extend(
                        node.collection_results()
                            .into_iter()
                            .filter(|item| self.result_pending(item))
                            .map(|item| item.span),
                    );
                }
            });
        }
        self.lost_results.extend(lost);
    }

    pub(in crate::access) fn covers_result_samples(
        &self,
        samples: &BTreeSet<ResultOccurrence>,
    ) -> bool {
        samples
            .iter()
            .all(|item| !self.lost_results.contains(&item.span) && !self.result_pending(item))
    }

    pub(in crate::access) fn forget_result_samples(
        &mut self,
        samples: &BTreeSet<ResultOccurrence>,
    ) {
        if samples.is_empty() {
            return;
        }
        self.obligations.retain(|item| !samples.contains(item));
        self.inspected.retain(|item| !samples.contains(item));
        self.pending_result_paths
            .retain(|item, _| !samples.contains(item));
        self.result_samples
            .retain(|item, _| !samples.contains(item));
        for value in self
            .slots
            .values_mut()
            .map(|slot| &mut slot.value)
            .chain(
                self.replacements
                    .values_mut()
                    .map(|update| &mut update.value),
            )
            .chain(self.loop_members.values_mut())
            .chain(&mut self.iteration)
            .chain(self.holds.iter_mut().map(|(_, value)| value))
        {
            value
                .rewrite_results(&mut |item| (!samples.contains(&item.occurrence)).then_some(item));
        }
    }

    pub(in crate::access) fn variant_paths(&self, value: &Datum) -> Vec<(Self, Datum)> {
        if self.obligations.is_empty() && value.results().is_empty() {
            return Vec::new();
        }
        let mut paths: BTreeSet<_> = value
            .roots
            .iter()
            .map(|root| root.branches.clone())
            .collect();
        if paths.is_empty() || paths.len() > BRANCH_LIMIT {
            paths = BTreeSet::from([Choices::new()]);
        }
        let mut discriminants: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        value.visit_nodes(&mut Vec::new(), &mut |_, node| {
            for root in &node.roots {
                for (&axis, &arm) in &root.branches {
                    if axis.discriminant.is_some() || node.has_root_result() {
                        discriminants.entry(axis).or_default().insert(arm);
                    }
                }
            }
        });
        let paths = Self::extend_result_paths(paths, discriminants);
        if paths.len() == 1 && paths.first().is_some_and(Choices::is_empty) {
            return Vec::new();
        }
        self.select_result_paths(value, paths)
    }

    pub(super) fn extend_result_paths(
        mut paths: BTreeSet<Choices>,
        axes: BTreeMap<Occurrence, BTreeSet<usize>>,
    ) -> BTreeSet<Choices> {
        // Independent choices can multiply when combined in a product.
        for (axis, arms) in axes {
            if arms.len() < 2 || paths.iter().all(|path| path.contains_key(&axis)) {
                continue;
            }
            let mut selected_paths = BTreeSet::new();
            for path in &paths {
                if path.contains_key(&axis) {
                    selected_paths.insert(path.clone());
                } else {
                    for &arm in &arms {
                        let mut selected = path.clone();
                        selected.insert(axis, arm);
                        selected_paths.insert(selected);
                    }
                }
            }
            if selected_paths.len() <= BRANCH_LIMIT {
                paths = selected_paths;
            }
        }
        paths
    }

    pub(in crate::access) fn iterable_result_paths(&self, value: &Datum) -> Vec<(Self, Datum)> {
        if value.results().is_empty() {
            return Vec::new();
        }
        let paths: BTreeSet<_> = value
            .roots
            .iter()
            .map(|root| root.branches.clone())
            .collect();
        if paths.len() > BRANCH_LIMIT
            || (paths.len() == 1 && paths.first().is_some_and(Choices::is_empty))
        {
            return Vec::new();
        }
        self.select_result_paths(value, paths)
    }

    pub(super) fn select_result_paths(
        &self,
        value: &Datum,
        paths: BTreeSet<Choices>,
    ) -> Vec<(Self, Datum)> {
        paths
            .into_iter()
            .filter(|path| compatible(path, &self.choices))
            .map(|path| {
                let mut ledger = self.clone();
                ledger
                    .choices
                    .extend(path.iter().map(|(&key, &arm)| (key, arm)));
                ledger
                    .obligations
                    .retain(|item| compatible(&item.created_in, &path));
                ledger
                    .inspected
                    .retain(|item| compatible(&item.created_in, &path));
                ledger
                    .pending_result_paths
                    .retain(|item, _| ledger.obligations.contains(item));
                for slot in ledger.slots.values_mut() {
                    slot.value.select_results(&path);
                }
                for replacement in ledger.replacements.values_mut() {
                    replacement.value.select_results(&path);
                }
                for member in ledger.loop_members.values_mut() {
                    member.select_results(&path);
                }
                let mut selected = value.clone();
                selected.select_variants(&path);
                selected.select_results(&path);
                (ledger, selected)
            })
            .collect()
    }

    pub(super) fn rebase_results(
        &mut self,
        local: impl Fn(Span) -> bool,
        age_choices: impl Fn(&mut Choices),
    ) -> BTreeMap<ResultOccurrence, ResultOccurrence> {
        let mut carried: BTreeMap<_, _> = self
            .obligations
            .iter()
            .filter(|item| local(item.span))
            .map(|item| {
                let mut target = item.clone();
                target.places.clear();
                age_choices(&mut target.created_in);
                (item.clone(), target)
            })
            .collect();
        let bindings = self
            .slots
            .iter()
            .map(|(&id, slot)| (ResultHolder::Binding(id), &slot.value));
        let iterables = self
            .iteration
            .iter()
            .enumerate()
            .map(|(id, value)| (ResultHolder::Iterable(id), value));
        let handlers = self
            .holds
            .iter()
            .enumerate()
            .map(|(id, (_, value))| (ResultHolder::Handler(id), value));
        // A carried identity is determined by its surviving paths. Different
        // evaluations of one site remain distinct when held in different slots.
        if !carried.is_empty() {
            for (holder, value) in bindings.chain(iterables).chain(handlers) {
                self.snapshot(value)
                    .result_places(holder, &mut Vec::new(), &mut carried);
            }
        }
        let rebase = |item: &ResultOccurrence| match carried.get(item) {
            Some(target) if target.places.is_empty() => None,
            Some(target) => Some(target.clone()),
            None => Some(item.clone()),
        };
        let lost: Vec<_> = self
            .pending_results()
            .filter(|item| {
                carried
                    .get(*item)
                    .is_some_and(|result| result.places.is_empty())
            })
            .map(|item| item.span)
            .collect();
        self.lost_results.extend(lost);
        let pending: BTreeSet<_> = self.pending_results().filter_map(rebase).collect();
        let mut pending_result_paths: BTreeMap<_, BTreeSet<Choices>> = BTreeMap::new();
        for item in self.pending_results() {
            let Some(target) = rebase(item) else { continue };
            let paths = pending_result_paths.entry(target).or_default();
            paths.extend(self.pending_paths(item, &self.choices).map(|mut path| {
                age_choices(&mut path);
                path
            }));
            Self::widen_choices(paths);
        }
        pending_result_paths.retain(|_, paths| !paths.contains(&Choices::new()));
        let inspected = self
            .inspected
            .iter()
            .chain(
                self.obligations
                    .iter()
                    .filter(|item| self.result_inspected(item)),
            )
            .filter_map(rebase)
            .filter(|item| !pending.contains(item))
            .collect();
        self.pending_result_paths = pending_result_paths;
        self.obligations = self.obligations.iter().filter_map(rebase).collect();
        self.inspected = inspected;
        carried
    }

    pub(in crate::access) fn inspect(&mut self, datum: &Datum) {
        self.inspect_paths(datum, false);
    }

    pub(in crate::access) fn tested_results(&self, datum: &Datum) -> BTreeSet<ResultOccurrence> {
        datum
            .root_results()
            .into_iter()
            .filter(|item| {
                let path = self
                    .choices
                    .iter()
                    .chain(&item.created_in)
                    .map(|(&key, &arm)| (key, arm))
                    .collect();
                datum.tests_root_result(item, &path)
            })
            .collect()
    }

    pub(super) fn inspect_paths(&mut self, datum: &Datum, root_only: bool) {
        let snapshot = self.loop_snapshot(datum);
        let results = if root_only {
            snapshot.root_results()
        } else {
            snapshot.results()
        };
        if results.is_empty() {
            return;
        }
        let mut axes: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        snapshot.visit_origins(&mut Vec::new(), &mut |_, origin| {
            for (&key, &arm) in &origin.branches {
                axes.entry(key).or_default().insert(arm);
            }
        });
        let paths = Self::extend_result_paths(BTreeSet::from([self.choices.clone()]), axes);
        let mut inspected = Vec::new();
        let mut narrowed = Vec::new();
        for item in results {
            if self.inspected.contains(&item) {
                continue;
            }
            let mut remaining = BTreeSet::new();
            let mut covered = false;
            for path in &paths {
                if !self.result_may_be_pending(&item, path) {
                    continue;
                }
                let choices = path
                    .iter()
                    .chain(&item.created_in)
                    .map(|(&key, &arm)| (key, arm))
                    .collect();
                if snapshot.tests_root_result(&item, &choices)
                    || !root_only && snapshot.contains_result(&item, &choices)
                {
                    covered = true;
                } else {
                    remaining.extend(self.pending_paths(&item, path).map(|mut pending| {
                        pending.extend(path.iter().map(|(&key, &arm)| (key, arm)));
                        pending
                    }));
                    Self::widen_choices(&mut remaining);
                    if remaining.contains(&Choices::new()) {
                        break;
                    }
                }
            }
            if remaining.is_empty() && covered {
                inspected.push(item);
            } else if covered
                && self.obligations.contains(&item)
                && !remaining.contains(&Choices::new())
            {
                narrowed.push((item, remaining));
            }
        }
        self.pending_result_paths.extend(narrowed);
        self.mark_inspected(inspected);
    }

    pub(in crate::access) fn mark_inspected(
        &mut self,
        results: impl IntoIterator<Item = ResultOccurrence>,
    ) {
        for item in results {
            self.pending_result_paths.remove(&item);
            self.inspected.insert(item);
        }
        // Transferring an entire collection also transfers its current
        // iteration's element. The converse does not discharge the collection.
        loop {
            let covered: Vec<_> = self
                .result_samples
                .iter()
                .filter(|(sample, collections)| {
                    self.result_pending(sample)
                        && collections.iter().all(|item| !self.result_pending(item))
                })
                .map(|(sample, _)| sample.clone())
                .collect();
            if covered.is_empty() {
                break;
            }
            for item in covered {
                self.pending_result_paths.remove(&item);
                self.inspected.insert(item);
            }
        }
    }

    pub(in crate::access) fn inspect_root(&mut self, datum: &Datum) {
        self.inspect_paths(datum, true);
    }

    pub(in crate::access) fn loop_snapshot<'d>(&self, datum: &'d Datum) -> Cow<'d, Datum> {
        if self.loop_members.is_empty() {
            Cow::Borrowed(datum)
        } else {
            Cow::Owned(self.snapshot(datum))
        }
    }

    pub(in crate::access) fn is_revoked(&self, datum: &Datum) -> bool {
        if self.revoked.is_empty() {
            return false;
        }
        self.loop_snapshot(datum).origins().any(|origin| {
            origin
                .dependencies
                .iter()
                .filter_map(|token| self.revoked.get(token))
                .any(|branches| {
                    branches.iter().any(|branch| {
                        compatible(branch, &self.choices) && compatible(branch, &origin.branches)
                    })
                })
        })
    }
}
