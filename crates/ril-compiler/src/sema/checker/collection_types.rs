use super::*;
impl Checker {
    /// These are invariant typing constraints shared by every alias to one
    /// storage node. They are monotone type inference, not branch-local state.
    pub(super) fn constrain_collection_type(&mut self, value: &Value, expected: &Ty, span: Span) {
        self.constrain_collection_graph(value, expected, span, &mut BTreeMap::new());
    }
    fn constrain_collection_graph(
        &mut self,
        value: &Value,
        expected: &Ty,
        span: Span,
        seen: &mut BTreeMap<NodeId, Vec<Ty>>,
    ) {
        let expected = self.call_inference_type(expected);
        let expected = match expected {
            Ty::Immutable(inner) => *inner,
            ty => ty,
        };
        for node in &value.origins.nodes {
            let previous = seen.entry(*node).or_default();
            if previous
                .iter()
                .any(|old| self.invariant_collection_equivalent(old, &expected))
            {
                continue;
            }
            previous.push(expected.clone());
            if matches!(expected, Ty::Array(_) | Ty::Map(..) | Ty::Set(_)) {
                if let Some(previous) = self.storage_types.get(node).cloned() {
                    if !super::types::unify_call_types(
                        &previous,
                        &expected,
                        &BTreeSet::new(),
                        &mut BTreeMap::new(),
                    ) && !self.invariant_collection_equivalent(&previous, &expected)
                    {
                        self.error(
                            "E0301",
                            span,
                            "collection aliases require one invariant element and key type",
                            [value.cause],
                        );
                    } else {
                        self.storage_types
                            .insert(*node, join_type_holes(&previous, &expected));
                    }
                } else {
                    self.storage_types.insert(*node, expected.clone());
                }
            }
            let fields: Vec<_> = self
                .fields
                .iter()
                .filter(|((parent, _), _)| parent == node)
                .map(|((_, slot), child)| (slot.clone(), child.clone()))
                .collect();
            for (slot, child) in fields {
                let child_type = match (&expected, &slot) {
                    (Ty::Array(inner) | Ty::Set(inner), Slot::Index(_) | Slot::AnyIndex) => {
                        Some(*inner.clone())
                    }
                    (Ty::Map(key, element), Slot::Field(name)) if name == "key" => {
                        let _ = element;
                        Some(*key.clone())
                    }
                    (Ty::Map(_, element), Slot::Index(_) | Slot::AnyIndex) => {
                        Some(*element.clone())
                    }
                    (Ty::Record(fields), Slot::Field(name)) => {
                        fields.get(name).map(|(_, ty)| ty.clone())
                    }
                    (Ty::Tuple(items), Slot::Tuple(index)) => items.get(*index as usize).cloned(),
                    _ => None,
                };
                if let Some(ty) = child_type {
                    self.constrain_collection_graph(&child, &ty, span, seen);
                }
            }
        }
        match &expected {
            Ty::Optional(inner) => {
                if let Some(payload) = &value.option_payload {
                    self.constrain_collection_graph(payload, inner, span, seen);
                }
            }
            Ty::Result(ok, error) => {
                if let Some(payload) = &value.result_success {
                    self.constrain_collection_graph(payload, ok, span, seen);
                }
                if let Some(payload) = &value.result_error {
                    self.constrain_collection_graph(payload, error, span, seen);
                }
                if let Some(payload) = &value.result_payload
                    && let Some(success) = value.result_tag
                {
                    self.constrain_collection_graph(
                        payload,
                        if success { ok } else { error },
                        span,
                        seen,
                    );
                }
            }
            _ => {}
        }
    }

    /// Transparent recursive aliases denote finite type graphs, even when an
    /// earlier projection has unfolded one more record layer. The visited pair
    /// proves only that recursive edge; every sibling field/mode is still checked.
    fn invariant_collection_equivalent(&self, left: &Ty, right: &Ty) -> bool {
        fn compare(
            checker: &Checker,
            left: &Ty,
            right: &Ty,
            seen: &mut BTreeSet<(String, String)>,
            depth: usize,
        ) -> bool {
            if left == right {
                return true;
            }
            if depth >= 128
                || matches!(left, Ty::Unknown | Ty::Never)
                || matches!(right, Ty::Unknown | Ty::Never)
            {
                return false;
            }
            if !seen.insert((format!("{left:?}"), format!("{right:?}"))) {
                return true;
            }
            let left = if matches!(left, Ty::Immutable(_)) {
                left.clone()
            } else {
                checker.expanded(left, &mut BTreeSet::new())
            };
            let right = if matches!(right, Ty::Immutable(_)) {
                right.clone()
            } else {
                checker.expanded(right, &mut BTreeSet::new())
            };
            match (&left, &right) {
                (Ty::Immutable(a), Ty::Immutable(b))
                | (Ty::Optional(a), Ty::Optional(b))
                | (Ty::Array(a), Ty::Array(b))
                | (Ty::Set(a), Ty::Set(b))
                | (Ty::Range(a), Ty::Range(b)) => compare(checker, a, b, seen, depth + 1),
                (Ty::Result(a, b), Ty::Result(c, d)) | (Ty::Map(a, b), Ty::Map(c, d)) => {
                    compare(checker, a, c, seen, depth + 1)
                        && compare(checker, b, d, seen, depth + 1)
                }
                (Ty::Tuple(a), Ty::Tuple(b)) => {
                    a.len() == b.len()
                        && a.iter()
                            .zip(b)
                            .all(|(a, b)| compare(checker, a, b, seen, depth + 1))
                }
                (Ty::Record(a), Ty::Record(b)) => {
                    a.len() == b.len()
                        && a.iter().all(|(name, (mode, a))| {
                            b.get(name).is_some_and(|(other, b)| {
                                mode == other && compare(checker, a, b, seen, depth + 1)
                            })
                        })
                }
                (Ty::Callable(a, r), Ty::Callable(b, s)) => {
                    a.len() == b.len()
                        && a.iter()
                            .zip(b)
                            .all(|(a, b)| compare(checker, a, b, seen, depth + 1))
                        && compare(checker, r, s, seen, depth + 1)
                }
                (
                    Ty::Applied {
                        constructor: a,
                        arguments: x,
                    },
                    Ty::Applied {
                        constructor: b,
                        arguments: y,
                    },
                ) if a == b && x.len() == y.len() => x.iter().zip(y).all(|(a, b)| match (a, b) {
                    (TypeArgument::Type(a), TypeArgument::Type(b)) => {
                        compare(checker, a, b, seen, depth + 1)
                    }
                    (
                        TypeArgument::CanonicalType { ty: a, key: x },
                        TypeArgument::CanonicalType { ty: b, key: y },
                    ) => x == y && compare(checker, a, b, seen, depth + 1),
                    _ => a == b,
                }),
                _ => left == right,
            }
        }
        compare(self, left, right, &mut BTreeSet::new(), 0)
    }
    pub(super) fn collection_type(&self, value: &Value) -> Ty {
        let fallback = self.call_inference_type(&value.ty);
        let fallback = match fallback {
            Ty::Immutable(inner) => *inner,
            ty => ty,
        };
        self.refine_storage_type(value, fallback)
    }

    /// Storage constraints may fill holes in a view, but cannot replace an
    /// already selected child identity with its inference representation.
    pub(super) fn refine_storage_type(&self, value: &Value, mut selected: Ty) -> Ty {
        for node in &value.origins.nodes {
            if let Some(ty) = self.storage_types.get(node) {
                selected = join_type_holes(&selected, ty);
            }
        }
        selected
    }
    pub(super) fn constrain_collection_insert(
        &mut self,
        source: &Value,
        value: &Value,
        key: Option<&Value>,
        span: Span,
    ) {
        let mut selected = self.collection_type(source);
        if source.construction
            && source
                .origins
                .nodes
                .iter()
                .all(|node| !self.storage_types.contains_key(node))
            && matches!(selected, Ty::Array(_))
            && source.origins.nodes.iter().all(|node| {
                self.fields
                    .iter()
                    .filter(|((parent, slot), _)| {
                        parent == node && matches!(slot, Slot::Index(_) | Slot::AnyIndex)
                    })
                    .all(|(_, child)| child.unsuffixed_numeric)
            })
            && let Ty::Array(element) = &selected
            && matches!(
                (&**element, &value.ty),
                (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
            )
        {
            selected = Ty::Array(Box::new(value.ty.clone()));
            self.require_type(source, &selected, span);
        }
        let inferred = match selected {
            Ty::Array(element) => Ty::Array(if *element == Ty::Unknown {
                Box::new(value.ty.clone())
            } else {
                self.require_type(value, &element, span);
                element
            }),
            Ty::Set(element) => Ty::Set(if *element == Ty::Unknown {
                Box::new(value.ty.clone())
            } else {
                self.require_type(value, &element, span);
                element
            }),
            Ty::Map(old_key, element) => {
                let inferred_key = if *old_key == Ty::Unknown {
                    key.map(|key| Box::new(key.ty.clone())).unwrap_or(old_key)
                } else {
                    if let Some(key) = key {
                        self.require_type(key, &old_key, span);
                    }
                    old_key
                };
                let inferred_value = if *element == Ty::Unknown {
                    Box::new(value.ty.clone())
                } else {
                    self.require_type(value, &element, span);
                    element
                };
                Ty::Map(inferred_key, inferred_value)
            }
            _ => return,
        };
        self.constrain_collection_type(source, &inferred, span);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn storage_refinement_fills_holes_without_expanding_known_child_views() {
        let mut checker = Checker::new(FileId(0));
        let node = NodeId(0);
        let packet = Ty::Named("Packet".into());
        let known = Ty::Array(Box::new(Ty::Optional(Box::new(packet.clone()))));
        let value = Value::reference(known.clone(), node, CauseId(0));
        checker.storage_types.insert(
            node,
            Ty::Array(Box::new(Ty::Optional(Box::new(Ty::Record(
                [("id".into(), (false, Ty::Int("int".into())))].into(),
            ))))),
        );
        assert_eq!(checker.refine_storage_type(&value, known.clone()), known);
        let hole = Ty::Array(Box::new(Ty::Unknown));
        checker.storage_types.insert(node, known.clone());
        assert_eq!(checker.refine_storage_type(&value, hole), known);
        assert_eq!(
            checker.refine_storage_type(&value, Ty::Array(Box::new(packet.clone()))),
            Ty::Array(Box::new(packet))
        );
    }
}
