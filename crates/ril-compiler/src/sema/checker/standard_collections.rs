use super::*;

pub(super) fn is_collection_builtin(name: &str) -> bool {
    matches!(
        name,
        "Array::first"
            | "Array::get"
            | "Array::contains"
            | "Array::pop"
            | "Array::remove"
            | "Array::reverse"
            | "Array::concat"
            | "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
            | "Array::push"
            | "Array::insert"
            | "Array::truncate"
            | "Map::get"
            | "Map::contains"
            | "Map::set"
            | "Map::remove"
            | "Map::keys"
            | "Map::values"
            | "Map::entries"
            | "Map::from"
            | "Set::from"
            | "Set::of"
            | "Set::contains"
            | "Set::insert"
            | "Set::remove"
            | "Set::values"
            | "Set::union"
            | "Set::intersect"
            | "Set::diff"
    )
}
impl Checker {
    pub(super) fn standard_collection_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_collection_builtin(name) {
            return None;
        }
        if !self.check_storage_intrinsic_inputs(name, args, span, frame) {
            return Some(self.unit(span));
        }
        if name.starts_with("Map::") {
            return Some(self.standard_map(name, args, span, frame));
        }
        if name.starts_with("Set::") {
            return Some(self.standard_set(name, args, span, frame));
        }
        let arity = match name {
            "Array::first" | "Array::pop" | "Array::reverse" => 1,
            "Array::fold" | "Array::insert" => 3,
            _ => 2,
        };
        if args.len() != arity {
            self.error(
                "E0314",
                span,
                format!("{name} requires {arity} arguments"),
                [],
            );
            return Some(self.unit(span));
        }
        let (_, source, source_span) = &args[0];
        if matches!(name, "Array::push" | "Array::insert") {
            let inserted = args.last().unwrap();
            self.constrain_collection_insert(source, &inserted.1, None, inserted.2);
        }
        let Ty::Array(element) = self.expanded(&self.collection_type(source), &mut BTreeSet::new())
        else {
            self.error(
                "E0301",
                *source_span,
                "array operation requires array data",
                [source.cause],
            );
            return Some(self.unit(span));
        };
        let writes = matches!(
            name,
            "Array::pop" | "Array::remove" | "Array::push" | "Array::insert" | "Array::truncate"
        );
        let callback_index = match name {
            "Array::map" | "Array::filter" | "Array::find" | "Array::any" | "Array::all"
            | "Array::for_each" => Some(1),
            "Array::fold" => Some(2),
            _ => None,
        };
        if callback_index.is_some() && !source.results.is_empty() {
            self.unsupported(
                span,
                "traversal requires per-element Result inspection coverage",
            );
        }
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if index == 0 && writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            let retained_value = matches!(name, "Array::push" | "Array::insert")
                && index + 1 == args.len()
                && *mode == ParameterMode::SharedMut;
            if Some(index) != callback_index && *mode != expected && !retained_value {
                self.error(
                    "E0405",
                    *argument_span,
                    "array argument mode mismatch",
                    [value.cause],
                );
            }
            if Some(index) == callback_index && *mode == ParameterMode::SharedMut {
                self.error(
                    "E0405",
                    *argument_span,
                    "traversal callback is borrowed, not retained",
                    [value.cause],
                );
            }
        }
        if writes {
            self.invalidate_array_length(source, *source_span);
            self.standard_structural_write(source, *source_span, frame);
        } else {
            self.access(source, None, Mode::Read, *source_span, frame);
        }
        let empty = self.standard_known_empty(source);
        let mut child = if empty {
            Value::scalar((*element).clone(), None, source.cause)
        } else {
            self.project(source, Slot::AnyIndex, span, frame, true)
        };
        child.ty = (*element).clone();
        self.standard_read_handle(&mut child);
        let output = match name {
            "Array::push" | "Array::insert" => {
                if name == "Array::insert" {
                    self.require_type(&args[1].1, &integer("int"), args[1].2);
                }
                let argument = args.last().unwrap();
                self.require_type(&argument.1, &element, argument.2);
                let inserted = self.standard_receive_insert(argument, frame);
                for node in &source.origins.nodes {
                    let mut summary = inserted.clone();
                    let previous: Vec<_> = self
                        .fields
                        .iter()
                        .filter_map(|((parent, slot), value)| {
                            (*parent == *node && matches!(slot, Slot::AnyIndex | Slot::Index(_)))
                                .then_some(value.clone())
                        })
                        .collect();
                    for value in previous {
                        summary = summary.join(&value, self.choice(), summary.cause);
                    }
                    self.store_field(*node, Slot::AnyIndex, summary);
                }
                if name == "Array::insert" {
                    self.standard_forget_positions(source);
                }
                self.unit(span)
            }
            "Array::truncate" => {
                self.require_type(&args[1].1, &integer("int"), args[1].2);
                if !source.results.is_empty() {
                    self.unsupported(
                        span,
                        "truncation requires exact Result membership preservation",
                    );
                }
                self.unit(span)
            }
            "Array::first" | "Array::get" | "Array::pop" | "Array::remove" => {
                if writes && !source.results.is_empty() {
                    self.unsupported(
                        span,
                        "removal requires exact Result membership preservation",
                    );
                }
                if name == "Array::remove" {
                    self.standard_forget_positions(source);
                }
                if matches!(name, "Array::get" | "Array::remove") {
                    self.require_type(&args[1].1, &integer("int"), args[1].2);
                }
                let selected = if name == "Array::first" {
                    Some(0)
                } else if matches!(name, "Array::get" | "Array::remove") {
                    if let Some(Constant::Integer(index)) = args[1].1.constant {
                        i64::try_from(index).ok()
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(index) = selected
                    && !empty
                    && index >= 0
                {
                    child = self.project(source, Slot::Index(index), span, frame, true);
                    self.standard_read_handle(&mut child);
                }
                if name == "Array::remove" {
                    child
                } else {
                    let absent = empty
                        || (name == "Array::get"
                            && matches!(args[1].1.constant, Some(Constant::Integer(index)) if index < 0));
                    if absent {
                        let mut none = self.unit(span);
                        none.ty = Ty::Optional(element.clone());
                        none.constant = None;
                        none.option_tag = Some(false);
                        none
                    } else {
                        self.standard_option(child, None, span, frame.owner)
                    }
                }
            }
            "Array::contains" => {
                self.require_type(&args[1].1, &element, args[1].2);
                self.standard_equality_type(&element, span);
                self.deep_read(source, span, frame);
                self.deep_read(&args[1].1, span, frame);
                self.standard_value(Ty::Bool, span, frame.owner, 0)
            }
            "Array::reverse" | "Array::concat" => {
                let mut sources = vec![source.clone()];
                if name == "Array::concat" {
                    self.require_type(&args[1].1, &Ty::Array(element.clone()), args[1].2);
                    self.access(&args[1].1, None, Mode::Read, args[1].2, frame);
                    sources.push(args[1].1.clone());
                }
                self.standard_copy_array(
                    &sources,
                    (*element).clone(),
                    name == "Array::reverse",
                    span,
                    frame,
                )
            }
            _ => {
                let index = callback_index.unwrap();
                let (mode, callback, callback_span) = &args[index];
                let mut callback = callback.clone();
                if *mode == ParameterMode::Read {
                    callback.permission = Permission::Read;
                } else {
                    if callback.permission != Permission::Write {
                        self.error(
                            "E0520",
                            *callback_span,
                            "mutable callback has no write authority",
                            [callback.cause],
                        );
                    }
                    self.access(&callback, None, Mode::Write, *callback_span, frame);
                }
                let mut invocation = vec![(ParameterMode::Read, child.clone(), span)];
                if name == "Array::fold" {
                    invocation.insert(0, (ParameterMode::Read, args[1].1.clone(), args[1].2));
                }
                let count = self.known_array_length(source);
                let before = self.snapshot_flow();
                let obligations = frame.obligations.clone();
                let repeated = if count.is_none_or(|count| count > 1) {
                    Some(self.begin_repeated_callback(&mut invocation, frame))
                } else {
                    None
                };
                self.active_iterations.push(source.origins.clone());
                let mut returned = self.invoke_generated_values(&callback, invocation, span, frame);
                self.active_iterations.pop();
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                if count == Some(0) {
                    self.restore_preview(&before);
                    frame.obligations = obligations;
                } else if count.is_none() {
                    let skipped = self.unit(span);
                    let executed = if returned.ty == Ty::Never {
                        returned.clone()
                    } else {
                        self.unit(span)
                    };
                    let _ = self.conditional_flow(&before, &skipped, &executed, None, span);
                }
                if count.is_some_and(|count| count > 0) && returned.ty == Ty::Never {
                    return Some(returned);
                }
                if count != Some(0) && !returned.results.is_empty() {
                    self.unsupported(
                        span,
                        "traversal Result production/inspection multiplicity proof",
                    );
                }
                if unknown_type(&returned.ty) {
                    self.unsupported(span, "traversal callback result type is unresolved");
                }
                match name {
                    "Array::map" => {
                        if count != Some(0) && !returned.origins.nodes.is_empty() {
                            self.unsupported(
                                span,
                                "mapped reference-result allocation multiplicity proof",
                            );
                        }
                        self.standard_array_with_children(
                            returned.ty.clone(),
                            if count == Some(0) {
                                vec![]
                            } else {
                                vec![returned]
                            },
                            span,
                            frame.owner,
                        )
                    }
                    "Array::filter" => {
                        self.require_type(&returned, &Ty::Bool, span);
                        let mut selected = self.standard_copy_array(
                            std::slice::from_ref(source),
                            (*element).clone(),
                            false,
                            span,
                            frame,
                        );
                        // Filtering is not a proof that every input Result survives.
                        selected.must_results.clear();
                        selected
                    }
                    "Array::find" => {
                        self.require_type(&returned, &Ty::Bool, span);
                        self.standard_option(child, empty.then_some(false), span, frame.owner)
                    }
                    "Array::any" | "Array::all" => {
                        self.require_type(&returned, &Ty::Bool, span);
                        self.standard_value(Ty::Bool, span, frame.owner, 0)
                    }
                    "Array::for_each" => {
                        self.require_type(&returned, &Ty::Unit, span);
                        self.unit(span)
                    }
                    "Array::fold" => {
                        self.require_type(&returned, &args[1].1.ty, span);
                        if !returned.ty.scalar() {
                            self.unsupported(span, "reference-valued fold accumulator fixed point");
                        }
                        if empty {
                            args[1].1.clone()
                        } else {
                            returned = returned.join(&args[1].1, self.choice(), returned.cause);
                            returned
                        }
                    }
                    _ => unreachable!(),
                }
            }
        };
        Some(output)
    }
    fn standard_known_empty(&self, source: &Value) -> bool {
        !source.origins.nodes.is_empty()
            && source.origins.nodes.iter().all(|node| {
                matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Fresh(_))
                    && self.heap.nodes[node.0 as usize].fields.is_empty()
            })
    }
    fn standard_map(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let arity = match name {
            "Map::keys" | "Map::values" | "Map::entries" | "Map::from" => 1,
            "Map::set" => 3,
            _ => 2,
        };
        if args.len() != arity {
            self.error(
                "E0314",
                span,
                format!("{name} requires {arity} arguments"),
                [],
            );
            return self.unit(span);
        }
        let (_, source, source_span) = &args[0];
        if name == "Map::from" {
            self.standard_arguments(name, args, std::slice::from_ref(&source.ty), 1, span);
            let Ty::Array(element) = self.expanded(&source.ty, &mut BTreeSet::new()) else {
                self.error(
                    "E0301",
                    *source_span,
                    "Map::from requires array pairs",
                    [source.cause],
                );
                return self.unit(span);
            };
            let Ty::Tuple(pair) = *element else {
                self.error(
                    "E0301",
                    *source_span,
                    "Map::from requires tuple pairs",
                    [source.cause],
                );
                return self.unit(span);
            };
            if pair.len() != 2 {
                self.error(
                    "E0301",
                    *source_span,
                    "Map::from requires two-element pairs",
                    [source.cause],
                );
                return self.unit(span);
            }
            self.standard_key_type(&pair[0], span, &mut BTreeSet::new());
            self.access(source, None, Mode::Read, *source_span, frame);
            let entry = self.project(source, Slot::AnyIndex, span, frame, true);
            let key = self.project(&entry, Slot::Tuple(0), span, frame, true);
            let mut value = self.project(&entry, Slot::Tuple(1), span, frame, true);
            self.standard_read_handle(&mut value);
            if !source.results.is_empty() {
                self.unsupported(span, "Map::from duplicate overwrite Result coverage proof");
            }
            return self.standard_map_value(
                pair[0].clone(),
                pair[1].clone(),
                key,
                value,
                span,
                frame.owner,
            );
        }
        if name == "Map::set" {
            self.constrain_collection_insert(source, &args[2].1, Some(&args[1].1), args[2].2);
        }
        let Ty::Map(key_ty, value_ty) =
            self.expanded(&self.collection_type(source), &mut BTreeSet::new())
        else {
            self.error(
                "E0301",
                *source_span,
                "map operation requires map data",
                [source.cause],
            );
            return self.unit(span);
        };
        self.standard_key_type(&key_ty, span, &mut BTreeSet::new());
        let writes = matches!(name, "Map::set" | "Map::remove");
        if writes && !source.results.is_empty() {
            self.unsupported(
                span,
                "map update requires exact Result membership preservation",
            );
        }
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if index == 0 && writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if !(name == "Map::set" && index == 2 && *mode == ParameterMode::SharedMut)
                && *mode != expected
            {
                self.error(
                    "E0405",
                    *argument_span,
                    "map argument mode mismatch",
                    [value.cause],
                );
            }
        }
        if writes {
            self.standard_structural_write(source, *source_span, frame);
        } else {
            self.access(source, None, Mode::Read, *source_span, frame);
        }
        if matches!(
            name,
            "Map::get" | "Map::contains" | "Map::set" | "Map::remove"
        ) {
            self.require_type(&args[1].1, &key_ty, args[1].2);
            self.deep_read(&args[1].1, args[1].2, frame);
        }
        match name {
            "Map::contains" => self.standard_value(Ty::Bool, span, frame.owner, 0),
            "Map::get" | "Map::remove" => {
                let mut value = self.project(source, Slot::AnyIndex, span, frame, true);
                self.standard_read_handle(&mut value);
                self.standard_option(value, None, span, frame.owner)
            }
            "Map::set" => {
                self.require_type(&args[2].1, &value_ty, args[2].2);
                let inserted = self.standard_receive_insert(&args[2], frame);
                for node in &source.origins.nodes {
                    let existing: Vec<_> = self
                        .fields
                        .iter()
                        .filter_map(|((parent, slot), value)| {
                            (*parent == *node && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                                .then_some(value.clone())
                        })
                        .collect();
                    let mut summary = inserted.clone();
                    for previous in existing {
                        summary = summary.join(&previous, self.choice(), summary.cause);
                    }
                    self.store_field(*node, Slot::AnyIndex, summary);
                    let mut key = args[1].1.clone();
                    self.standard_read_handle(&mut key);
                    if let Some(previous) = self
                        .fields
                        .get(&(*node, Slot::Field("key".into())))
                        .cloned()
                    {
                        key = key.join(&previous, self.choice(), key.cause);
                    }
                    self.store_field(*node, Slot::Field("key".into()), key);
                }
                self.unit(span)
            }
            "Map::keys" => {
                let key = self.project(source, Slot::Field("key".into()), span, frame, true);
                self.standard_array_with_children(*key_ty, vec![key], span, frame.owner)
            }
            "Map::values" => {
                let mut value = self.project(source, Slot::AnyIndex, span, frame, true);
                self.standard_read_handle(&mut value);
                let mut output =
                    self.standard_array_with_children(*value_ty, vec![value], span, frame.owner);
                if !source.results.is_empty() {
                    self.unsupported(span, "map enumeration Result membership coverage");
                    output.must_results.clear();
                }
                output
            }
            "Map::entries" => {
                let key = self.project(source, Slot::Field("key".into()), span, frame, true);
                let mut value = self.project(source, Slot::AnyIndex, span, frame, true);
                self.standard_read_handle(&mut value);
                let node = self.allocate(span, 1, frame.owner);
                let cause = self.heap.nodes[node.0 as usize].cause;
                let mut pair = Value::reference(
                    Ty::Tuple(vec![(*key_ty).clone(), (*value_ty).clone()]),
                    node,
                    cause,
                );
                pair.results = value.results.clone();
                pair.must_results = value.must_results.clone();
                self.store_field(node, Slot::Tuple(0), key);
                self.store_field(node, Slot::Tuple(1), value);
                let mut output = self.standard_array_with_children(
                    pair.ty.clone(),
                    vec![pair],
                    span,
                    frame.owner,
                );
                if !source.results.is_empty() {
                    self.unsupported(span, "map enumeration Result membership coverage");
                    output.must_results.clear();
                }
                output
            }
            _ => unreachable!(),
        }
    }
    fn standard_map_value(
        &mut self,
        key_ty: Ty,
        value_ty: Ty,
        key: Value,
        value: Value,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        let node = self.allocate(span, 0, owner);
        let cause = self.heap.nodes[node.0 as usize].cause;
        let mut output =
            Value::reference(Ty::Map(Box::new(key_ty), Box::new(value_ty)), node, cause);
        output.results = value.results.clone();
        self.store_field(node, Slot::Field("key".into()), key);
        self.store_field(node, Slot::AnyIndex, value);
        output
    }
    fn standard_receive_insert(
        &mut self,
        argument: &(ParameterMode, Value, Span),
        frame: &mut Frame,
    ) -> Value {
        let (mode, value, span) = argument;
        let mut value = value.clone();
        if *mode == ParameterMode::SharedMut {
            if value.temporary {
                self.unsupported(*span, "retained insertion cannot extend a temporary loan");
            }
            if value.permission != Permission::Write {
                self.error(
                    "E0520",
                    *span,
                    "retained insertion has no write authority",
                    [value.cause],
                );
            }
            for source in &value.sources {
                self.use_binding(*source, Mode::Retain, frame);
            }
            if value
                .sources
                .iter()
                .any(|source| self.bindings[*source].parameter)
            {
                frame.obligations.retention = true;
            }
        } else if value.construction {
            if value.internal_aliases && !value.marker {
                self.error(
                    "E0510",
                    *span,
                    "internally shared writable construction requires ^mut",
                    [value.cause],
                );
            }
            value.construction = false;
            value.publication = Publication::Live;
        } else {
            self.standard_read_handle(&mut value);
        }
        value
    }
    fn standard_set(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let arity = if matches!(name, "Set::from" | "Set::of" | "Set::values") {
            1
        } else {
            2
        };
        if args.len() != arity {
            self.error(
                "E0314",
                span,
                format!("{name} requires {arity} arguments"),
                [],
            );
            return self.unit(span);
        }
        let (_, source, source_span) = &args[0];
        if name == "Set::insert" {
            self.constrain_collection_insert(source, &args[1].1, None, args[1].2);
        }
        let element = match self.expanded(&self.collection_type(source), &mut BTreeSet::new()) {
            Ty::Array(element) if matches!(name, "Set::from" | "Set::of") => element,
            Ty::Set(element) if !matches!(name, "Set::from" | "Set::of") => element,
            _ => {
                self.error(
                    "E0301",
                    *source_span,
                    "set operation has wrong receiver type",
                    [source.cause],
                );
                return self.unit(span);
            }
        };
        self.standard_key_type(&element, span, &mut BTreeSet::new());
        let writes = matches!(name, "Set::insert" | "Set::remove");
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if index == 0 && writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument_span,
                    "set argument mode mismatch",
                    [value.cause],
                );
            }
        }
        if writes {
            self.standard_structural_write(source, *source_span, frame);
        } else {
            self.access(source, None, Mode::Read, *source_span, frame);
        }
        match name {
            "Set::contains" | "Set::insert" | "Set::remove" => {
                self.require_type(&args[1].1, &element, args[1].2);
                self.deep_read(&args[1].1, args[1].2, frame);
                if name == "Set::insert" {
                    for node in &source.origins.nodes {
                        let mut inserted = args[1].1.clone();
                        self.standard_read_handle(&mut inserted);
                        if let Some(previous) = self.fields.get(&(*node, Slot::AnyIndex)).cloned() {
                            inserted = inserted.join(&previous, self.choice(), inserted.cause);
                        }
                        self.store_field(*node, Slot::AnyIndex, inserted);
                    }
                }
                self.standard_value(Ty::Bool, span, frame.owner, 0)
            }
            "Set::from" | "Set::of" | "Set::values" | "Set::union" | "Set::intersect"
            | "Set::diff" => {
                let mut child = self.project(source, Slot::AnyIndex, span, frame, true);
                self.standard_read_handle(&mut child);
                if args.len() == 2 {
                    self.require_type(&args[1].1, &Ty::Set(element.clone()), args[1].2);
                    self.access(&args[1].1, None, Mode::Read, args[1].2, frame);
                    let next = self.project(&args[1].1, Slot::AnyIndex, span, frame, true);
                    child = child.join(&next, self.choice(), child.cause);
                }
                let mut output = self.standard_array_with_children(
                    (*element).clone(),
                    vec![child],
                    span,
                    frame.owner,
                );
                if name != "Set::values" {
                    output.ty = Ty::Set(element);
                }
                output
            }
            _ => unreachable!(),
        }
    }
    fn standard_key_type(&mut self, ty: &Ty, span: Span, seen: &mut BTreeSet<String>) {
        match self.expanded(ty, &mut seen.clone()) {
            Ty::Bool | Ty::Int(_) | Ty::Str | Ty::Bytes | Ty::Unit => {}
            Ty::Named(name) if matches!(name.as_str(), "Os::NativeString" | "Path::Path") => {}
            Ty::Named(name) if seen.insert(name.clone()) => {
                if let Some(declaration) = self.types.get(&name).cloned()
                    && (declaration.nominal || declaration.opaque)
                    && let Some(value) = &declaration.value
                {
                    let ty = self.ty(value);
                    self.standard_key_type(&ty, span, seen);
                } else {
                    self.error(
                        "E0328",
                        span,
                        "map/set key representation is not admitted",
                        [],
                    );
                }
            }
            Ty::Unknown | Ty::Generic(_) => {
                self.unsupported(span, "map/set key representation remains unresolved")
            }
            _ => self.error(
                "E0328",
                span,
                "map/set keys require admitted scalar value representations",
                [],
            ),
        }
    }
    pub(in crate::sema::checker) fn standard_read_handle(&self, value: &mut Value) {
        if !value.origins.nodes.is_empty() {
            value.permission = Permission::Read;
            value.construction = false;
            value.marker = false;
        }
    }
    fn standard_forget_positions(&mut self, target: &Value) {
        for node in &target.origins.nodes {
            let mut values: Vec<_> = self
                .fields
                .iter()
                .filter_map(|((parent, slot), value)| {
                    (*parent == *node && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                        .then_some(value.clone())
                })
                .collect();
            if let Some(mut summary) = values.pop() {
                for value in values {
                    summary = summary.join(&value, self.choice(), summary.cause);
                }
                self.fields.retain(|(parent, slot), _| {
                    *parent != *node || !matches!(slot, Slot::Index(_))
                });
                self.heap.nodes[node.0 as usize]
                    .fields
                    .retain(|slot, _| !matches!(slot, Slot::Index(_)));
                self.store_field(*node, Slot::AnyIndex, summary);
            }
        }
    }
    pub(super) fn standard_structural_write(
        &mut self,
        target: &Value,
        span: Span,
        frame: &mut Frame,
    ) {
        if target.permission != Permission::Write {
            self.error(
                "E0520",
                span,
                "collection receiver is read-only",
                [target.cause],
            );
        }
        for active in &self.active_iterations {
            if !self.origins_disjoint(active, &target.origins) {
                self.error(
                    "E0526",
                    span,
                    "structural mutation invalidates active traversal",
                    [target.cause],
                );
                break;
            }
        }
        self.access(target, None, Mode::Write, span, frame);
    }
    fn standard_equality_type(&mut self, ty: &Ty, span: Span) {
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Callable(..) => {
                self.error("E0305", span, "callable values do not admit equality", [])
            }
            Ty::Unknown => self.unsupported(span, "collection equality type is unresolved"),
            Ty::Array(inner) | Ty::Optional(inner) => self.standard_equality_type(&inner, span),
            Ty::Map(a, b) | Ty::Result(a, b) => {
                self.standard_equality_type(&a, span);
                self.standard_equality_type(&b, span);
            }
            Ty::Tuple(items) => {
                for item in items {
                    self.standard_equality_type(&item, span);
                }
            }
            Ty::Record(fields) => {
                for (_, (_, item)) in fields {
                    self.standard_equality_type(&item, span);
                }
            }
            _ => {}
        }
    }
    pub(super) fn standard_copy_array(
        &mut self,
        sources: &[Value],
        element: Ty,
        reverse: bool,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let mut children = vec![];
        for source in sources {
            if !source.results.is_empty() {
                self.unsupported(span, "copied collection Result membership coverage");
            }
            let mut source_children: Vec<_> = self
                .fields
                .iter()
                .filter_map(|((node, slot), value)| {
                    (source.origins.nodes.contains(node)
                        && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                    .then_some((slot.clone(), value.clone()))
                })
                .collect();
            source_children.sort_by(|a, b| a.0.cmp(&b.0));
            if reverse {
                source_children.reverse();
            }
            for (slot, _) in source_children {
                let mut child = self.project(source, slot, span, frame, true);
                if child.construction && self.construction_can_publish(&child) {
                    child.publication = Publication::Immutable;
                }
                self.standard_read_handle(&mut child);
                children.push(child);
            }
        }
        let mut output = self.standard_array_with_children(element, children, span, frame.owner);
        if sources.iter().any(|source| !source.results.is_empty()) {
            output.must_results.clear();
        }
        output
    }
    pub(in crate::sema::checker) fn standard_array_with_children(
        &mut self,
        element: Ty,
        children: Vec<Value>,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        let node = self.allocate(span, 0, owner);
        let cause = self.heap.nodes[node.0 as usize].cause;
        let mut output = Value::reference(Ty::Array(Box::new(element)), node, cause);
        let mut summarized: Option<Value> = None;
        for child in children {
            output.results.extend(&child.results);
            output.must_results.extend(&child.must_results);
            output
                .callback_parameters
                .extend(&child.callback_parameters);
            output.mutable_environment |= child.mutable_environment;
            output.observer_environment |= child.observer_environment;
            summarized = Some(if let Some(previous) = summarized {
                previous.join(&child, self.choice(), cause)
            } else {
                child
            });
        }
        if let Some(child) = summarized {
            self.store_field(node, Slot::AnyIndex, child);
        }
        self.complete_standard_array_source(&mut output, span);
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn repeated_callbacks_widen_iteration_state_and_preserve_the_zero_iteration_path() {
        for source in [
            "fn count(items:[]int)->int { var total=0; let mut step=\\_ -> {total+=1}; Array::for_each(items,mut step); total }",
            "fn example() { var total=0; let mut step=\\_:int -> {total+=1}; let items:[]int=[]; Array::for_each(items,mut step); assert(total==0) }",
            "type Cell={value:int}\nfn example() { let cell=Cell.{value:1}; var current:?Cell=Some(cell); var count=0; let mut step=\\_:int -> {count+=1; if count==2 {current=None}}; Array::for_each([1,2],mut step); let result=current }",
        ] {
            let output = check(source);
            assert!(
                output.program.is_some(),
                "{source}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        let output = check(
            "type Cell={value:int}\nfn example() { let cell=Cell.{value:1}; var current:?Cell=Some(cell); var count=0; let mut step=\\_:int -> {count+=1; if count==2 {current=Some(Cell.{value:2})}}; Array::for_each([1,2],mut step); let result=current }",
        );
        assert!(
            !output.unsupported.is_empty(),
            "reference transition on a later iteration was accepted: {:?}",
            output.diagnostics
        );
    }
}
