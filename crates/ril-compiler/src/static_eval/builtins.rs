use super::*;

impl Evaluator {
    pub(super) fn static_name(&mut self, name: &str) -> Result<StaticValue> {
        if let Some(value) = self.numeric_constant(name) {
            return Ok(value);
        }
        if let Some(value) = self.values.get(name) {
            return self.copy_static_value(value);
        }
        if self.declarations.contains_key(name) {
            return Err(Failure::Unsupported(
                "static declared constructor value contract".into(),
            ));
        }
        let normalized = name.strip_prefix("Prelude::").unwrap_or(name);
        if normalized == "None" {
            return Ok(StaticValue::Variant("Prelude::None".into(), vec![], None));
        }
        if self.functions.contains_key(name)
            || matches!(normalized, "Some" | "Ok" | "Err")
            || static_builtin(normalized)
        {
            return self.callable(name).map(StaticValue::Callable);
        }
        Err(Failure::Diagnostic(
            if primitive_type(normalized) || self.declarations.contains_key(name) {
                "E0319"
            } else {
                "E0814"
            },
            format!("{name} is not a static value"),
        ))
    }
    pub(super) fn callable(&mut self, name: &str) -> Result<StaticCallable> {
        if let Some(StaticValue::Callable(callable)) = self.values.get(name) {
            return self.copy_static_callable(callable);
        }
        if let Some(function) = self.functions.get(name) {
            if !function.is_meta {
                return Err(Failure::Diagnostic(
                    "E0810",
                    "ordinary functions cannot run in the static family".into(),
                ));
            }
            return Ok(StaticCallable::Named {
                name: name.into(),
                captured: self.function_environments.get(name).cloned(),
            });
        }
        if self.declarations.contains_key(name) {
            return Err(Failure::Unsupported(
                "static declared constructor invocation contract".into(),
            ));
        }
        let normalized = name.strip_prefix("Prelude::").unwrap_or(name);
        if static_builtin(normalized) || matches!(normalized, "Some" | "Ok" | "Err") {
            return Ok(StaticCallable::Builtin(normalized.into()));
        }
        if name.contains("::")
            || matches!(
                name,
                "clone" | "clone_immut" | "inner" | "panic" | "print" | "println"
            )
        {
            return Err(Failure::Diagnostic(
                "E0810",
                format!("{name} is a run-time-only callable"),
            ));
        }
        Err(Failure::Diagnostic(
            "E0204",
            format!("unknown static callable {name}"),
        ))
    }
    pub(super) fn bind_parameters(
        &mut self,
        parameters: &[Parameter],
        arguments: Vec<application::StaticArgument>,
    ) -> Result<()> {
        self.bind_parameters_with_sources(parameters, None, arguments)
    }
    pub(super) fn bind_parameters_from_signature(
        &mut self,
        parameters: &[Parameter],
        sources: &[Parameter],
        arguments: Vec<application::StaticArgument>,
    ) -> Result<()> {
        if parameters.len() != sources.len() {
            return Err(Failure::Unsupported(
                "static prepared signature lost its source parameters".into(),
            ));
        }
        self.bind_parameters_with_sources(parameters, Some(sources), arguments)
    }
    fn bind_parameters_with_sources(
        &mut self,
        parameters: &[Parameter],
        sources: Option<&[Parameter]>,
        arguments: Vec<application::StaticArgument>,
    ) -> Result<()> {
        let descriptors = parameters
            .iter()
            .map(application::ParameterSpec::from)
            .collect::<Vec<_>>();
        let plan = application::StaticApplicationPlan::new(
            &descriptors,
            arguments.iter().map(|argument| argument.label.clone()),
        )?;
        let mut local_names = BTreeSet::new();
        for parameter in parameters {
            application::binding_names(&parameter.pattern, &mut local_names);
        }
        for name in local_names {
            self.values.remove(&name);
            self.type_environment.mask_const(&name);
        }
        let mut arguments = arguments
            .into_iter()
            .map(|argument| Some(argument.value))
            .collect::<Vec<_>>();
        for (parameter_index, (parameter, slot)) in parameters.iter().zip(plan.slots).enumerate() {
            if parameter.mode != ParameterMode::Read {
                return Err(Failure::Diagnostic(
                    "E0810",
                    "static calls cannot acquire ordinary write authority".into(),
                ));
            }
            let mut value = match slot {
                application::ArgumentSlot::Explicit(index) => {
                    arguments[index].take().expect("one static argument slot")
                }
                application::ArgumentSlot::Default => {
                    let syntax = record_contexts::expression(
                        parameter.default.as_ref().expect("checked default slot"),
                        parameter.ty.as_ref(),
                    );
                    self.expression_expected(&syntax, false, parameter.ty.as_ref())?
                }
            };
            if let Some(ty) = &parameter.ty {
                self.retain_constant_shape(&value, ty)?;
                value = if let Some(source) =
                    sources.and_then(|sources| sources[parameter_index].ty.as_ref())
                {
                    self.ascribe_application_value_from_resolved(value, source, ty)?
                } else {
                    self.ascribe_application_value(value, ty)?
                };
            }
            if let Some(TypeExpr {
                kind: TypeKind::Name { path, arguments },
                ..
            }) = &parameter.ty
                && path == &["type"]
                && arguments.len() == 1
                && let (TypeKind::Name { path, .. }, StaticValue::Type(actual)) =
                    (&arguments[0].kind, &value)
                && path.len() == 1
            {
                self.values
                    .insert(path[0].clone(), StaticValue::Type(actual.clone()));
            }
            if !self.match_pattern(&parameter.pattern, &value)? {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "static parameter pattern mismatch".into(),
                ));
            }
        }
        Ok(())
    }
    pub(super) fn match_pattern(&mut self, pattern: &Pattern, value: &StaticValue) -> Result<bool> {
        Ok(match &pattern.kind {
            PatternKind::Wildcard => true,
            PatternKind::Name(name) => {
                self.type_environment.mask_const(name);
                self.values
                    .insert(name.clone(), self.copy_static_value(value)?);
                true
            }
            PatternKind::Literal(literal) => {
                let actual = self.expression(&Expr {
                    hir_id: None,
                    kind: ExprKind::Literal(literal.clone()),
                    span: pattern.span,
                })?;
                matches!(
                    self.binary("==", actual, value.clone())?,
                    StaticValue::Bool(true)
                )
            }
            PatternKind::Value(expression) => {
                let actual = self.expression(expression)?;
                matches!(
                    self.binary("==", actual, value.clone())?,
                    StaticValue::Bool(true)
                )
            }
            PatternKind::Tuple(patterns) => {
                let values = match value {
                    StaticValue::Tuple(values) => values.as_slice(),
                    StaticValue::Unit => &[],
                    _ => return Ok(false),
                };
                self.match_sequence(patterns, values, Some(value))?
            }
            PatternKind::Array(patterns) => {
                let Some(values) = value.array_items() else {
                    return Ok(false);
                };
                self.match_sequence(patterns, values, Some(value))?
            }
            PatternKind::Rest(_) => {
                return Err(Failure::Diagnostic(
                    "E0347",
                    "rest requires a directly enclosing tuple or array pattern".into(),
                ));
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                if let StaticValue::Record(values) = value {
                    let mut matched = true;
                    for field in fields {
                        if let Some(child) = values.get(&field.name) {
                            let child = self.copy_static_value(child)?;
                            let child = self.project_source_field(value, child, &field.name)?;
                            if !self.match_pattern(&field.pattern, &child)? {
                                matched = false;
                                break;
                            }
                        } else {
                            matched = false;
                            break;
                        }
                    }
                    if matched
                        && let Some(name) = rest_binding
                        && name != "_"
                    {
                        let rest = self.static_record_remainder(value, fields, pattern.span)?;
                        self.type_environment.mask_const(name);
                        self.values.insert(name.clone(), rest);
                    }
                    matched
                } else {
                    false
                }
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                if let StaticValue::Result(produced) = value {
                    let success = results::tag(path).ok_or_else(|| {
                        Failure::Diagnostic(
                            "E0301",
                            "constructor test does not belong to Result".into(),
                        )
                    })?;
                    self.inspect_static_result(produced.id, pattern.span)?;
                    if success != produced.success {
                        false
                    } else if arguments.is_empty() {
                        true
                    } else if arguments.len() == 1 {
                        self.match_pattern(&arguments[0], &produced.payload)?
                    } else if let StaticValue::Tuple(items) = &produced.payload {
                        if arguments.len() != items.len() {
                            false
                        } else {
                            let mut matched = true;
                            for (pattern, item) in arguments.iter().zip(items.iter()) {
                                if !self.match_pattern(pattern, item)? {
                                    matched = false;
                                    break;
                                }
                            }
                            matched
                        }
                    } else {
                        false
                    }
                } else if let StaticValue::Variant(name, payload, _) = value {
                    let tag = path.last().map(String::as_str).unwrap_or_default();
                    let actual = name.rsplit("::").next().unwrap_or(name);
                    if tag != actual {
                        false
                    } else if arguments.is_empty() {
                        true
                    } else {
                        let payload = if arguments.len() > 1 && payload.len() == 1 {
                            match &payload[0] {
                                StaticValue::Tuple(items) => items.values.as_slice(),
                                _ => payload.as_slice(),
                            }
                        } else {
                            payload.as_slice()
                        };
                        if arguments.len() != payload.len() {
                            return Ok(false);
                        }
                        let mut matched = true;
                        for (pattern, value) in arguments.iter().zip(payload) {
                            if !self.match_pattern(pattern, value)? {
                                matched = false;
                                break;
                            }
                        }
                        matched
                    }
                } else {
                    false
                }
            }
            PatternKind::Type { ty, .. } => {
                if let StaticValue::Type(actual) = value {
                    self.match_type(ty, actual, &BTreeSet::new())?
                } else {
                    false
                }
            }
            PatternKind::Alternative(patterns) => {
                let saved = self.capture_environment()?;
                let mut matched = false;
                for pattern in patterns {
                    let environment = self.copy_environment(&saved)?;
                    self.install_environment(environment);
                    if self.match_pattern(pattern, value)? {
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    self.install_environment(saved);
                }
                matched
            }
            PatternKind::Mode { .. } => {
                return Err(Failure::Diagnostic(
                    "E0810",
                    "static patterns cannot bind mutable authority".into(),
                ));
            }
            PatternKind::Error => {
                return Err(Failure::Unsupported("invalid static pattern".into()));
            }
        })
    }
    pub(super) fn field_value(&mut self, value: StaticValue, field: &str) -> Result<StaticValue> {
        let child = match &value {
            StaticValue::Record(values) => {
                let child = values.get(field).ok_or_else(|| {
                    Failure::Diagnostic("E0336", "static record field missing".into())
                })?;
                self.copy_static_value(child)?
            }
            StaticValue::Tuple(values) => {
                let index = field.parse::<usize>().map_err(|_| {
                    Failure::Diagnostic("E0337", "tuple projection requires an index".into())
                })?;
                let child = values.get(index).ok_or_else(|| {
                    Failure::Diagnostic("E0312", "static tuple index out of bounds".into())
                })?;
                self.copy_static_value(child)?
            }
            StaticValue::Variant(_, values, _) => {
                let index = field.parse::<usize>().map_err(|_| {
                    Failure::Diagnostic("E0337", "tuple projection requires an index".into())
                })?;
                if index >= values.len() {
                    return Err(Failure::Diagnostic(
                        "E0312",
                        "static tuple index out of bounds".into(),
                    ));
                } else {
                    self.copy_static_value(&values[index])?
                }
            }
            _ => {
                return Err(Failure::Diagnostic(
                    "E0337",
                    "static value has no product projection".into(),
                ));
            }
        };
        self.project_source_field(&value, child, field)
    }
    pub(super) fn index_value(
        &mut self,
        value: StaticValue,
        index: StaticValue,
        safe: bool,
    ) -> Result<StaticValue> {
        let found = match (&value, index) {
            (StaticValue::Array(values), StaticValue::Integer(index)) => {
                if index >= 0 && (index as usize) < values.len() {
                    Some(self.project_source_index(
                        &value,
                        self.copy_static_value(&values[index as usize])?,
                    )?)
                } else {
                    None
                }
            }
            (StaticValue::ArrayWindow(values), StaticValue::Integer(index)) => values
                .get(usize::try_from(index).unwrap_or(usize::MAX))
                .map(|child| {
                    let child = self.copy_static_value(child)?;
                    self.project_source_index(&value, child)
                })
                .transpose()?,
            (StaticValue::Map(entries), key) => {
                let found = entries
                    .iter()
                    .find(|(existing, _)| static_equal(existing, &key))
                    .map(|(_, child)| {
                        self.copy_static_value(child)
                            .and_then(|child| self.project_source_index(&value, child))
                    })
                    .transpose()?;
                return Ok(option(found));
            }
            _ => {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "invalid static index operation".into(),
                ));
            }
        };
        if safe {
            Ok(option(found))
        } else {
            found
                .ok_or_else(|| Failure::Diagnostic("E0831", "static index is out of bounds".into()))
        }
    }
    pub(super) fn static_builtin(
        &mut self,
        name: &str,
        args: Vec<StaticValue>,
    ) -> Result<StaticValue> {
        // Read algorithms borrow the selected sequence. The published handle
        // remains an ArrayWindow with its real backing identity.
        let args = if matches!(
            name,
            "Array::first"
                | "Array::get"
                | "Array::contains"
                | "Array::reverse"
                | "Array::concat"
                | "Array::map"
                | "Array::filter"
                | "Array::fold"
                | "Map::from"
                | "String::join"
        ) {
            args.into_iter()
                .map(|value| {
                    if let StaticValue::ArrayWindow(window) = value {
                        self.budget.work(window.len as u64 + 1)?;
                        let selected = window
                            .iter()
                            .map(|value| self.copy_static_value(value))
                            .collect::<Result<Vec<_>>>()?;
                        Ok(StaticValue::Array(StaticCollection {
                            id: window.id,
                            values: std::sync::Arc::new(selected),
                            source_type: window.source_type.clone(),
                        }))
                    } else {
                        Ok(value)
                    }
                })
                .collect::<Result<Vec<_>>>()?
        } else {
            args
        };
        match (name, args.as_slice()) {
            ("assert", [StaticValue::Bool(true), ..]) => Ok(StaticValue::Unit),
            ("assert", [StaticValue::Bool(false), ..]) => Err(Failure::Diagnostic(
                "E0830",
                "compile-time assertion failed".into(),
            )),
            ("byte_size", [StaticValue::Type(ty)]) => Ok(StaticValue::Integer(self.byte_size(ty)?)),
            ("len", [value]) => Ok(StaticValue::Integer(match value {
                StaticValue::String(value) => value.chars().count(),
                StaticValue::Bytes(value) => value.len(),
                StaticValue::Array(value) | StaticValue::Tuple(value) => value.len(),
                StaticValue::ArrayWindow(value) => value.len,
                StaticValue::Map(value) => value.len(),
                _ => {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "len requires a collection".into(),
                    ));
                }
            } as i128)),
            ("Some", values) => {
                let payload = match values {
                    [] => StaticValue::Unit,
                    [value] => value.clone(),
                    values => self.tuple(values.to_vec()),
                };
                Ok(StaticValue::Variant(
                    "Prelude::Some".into(),
                    vec![payload],
                    None,
                ))
            }
            ("Ok" | "Err", _) => {
                let payload = match args.len() {
                    0 => StaticValue::Unit,
                    1 => args.into_iter().next().unwrap(),
                    _ => self.tuple(args),
                };
                self.produce_result(name == "Ok", payload)
            }
            ("Array::first", [StaticValue::Array(values)]) => Ok(option(values.first().cloned())),
            ("Array::get", [StaticValue::Array(values), StaticValue::Integer(index)]) => {
                Ok(option(
                    usize::try_from(*index)
                        .ok()
                        .and_then(|index| values.get(index).cloned()),
                ))
            }
            ("Array::contains", [StaticValue::Array(values), value]) => Ok(StaticValue::Bool(
                values.iter().any(|existing| static_equal(existing, value)),
            )),
            ("Array::reverse", [StaticValue::Array(values)]) => {
                Ok(self.array(values.iter().rev().cloned().collect()))
            }
            ("Array::concat", [StaticValue::Array(left), StaticValue::Array(right)]) => {
                Ok(self.array(left.iter().chain(right).cloned().collect()))
            }
            (
                "Array::map" | "Array::filter" | "Array::find" | "Array::any" | "Array::all"
                | "Array::for_each",
                [StaticValue::Array(values), StaticValue::Callable(callable)],
            ) => {
                let mut output = vec![];
                for value in values {
                    self.budget.event(budget::Event::LoopIteration)?;
                    let callback = self.copy_static_callable(callable)?;
                    let argument = self.copy_static_value(value)?;
                    let result = self.invoke_callback(callback, vec![argument])?;
                    match name {
                        "Array::map" => output.push(result),
                        "Array::for_each" => {
                            if result != StaticValue::Unit {
                                return Err(Failure::Diagnostic(
                                    "E0301",
                                    "for_each callback must return unit".into(),
                                ));
                            }
                        }
                        _ => {
                            let StaticValue::Bool(selected) = result else {
                                return Err(Failure::Diagnostic(
                                    "E0301",
                                    "array predicate must return bool".into(),
                                ));
                            };
                            match name {
                                "Array::filter" if selected => output.push(value.clone()),
                                "Array::find" if selected => {
                                    return Ok(option(Some(value.clone())));
                                }
                                "Array::any" if selected => return Ok(StaticValue::Bool(true)),
                                "Array::all" if !selected => return Ok(StaticValue::Bool(false)),
                                _ => {}
                            }
                        }
                    }
                }
                self.budget.event(budget::Event::LoopIteration)?;
                Ok(match name {
                    "Array::map" | "Array::filter" => self.array(output),
                    "Array::find" => option(None),
                    "Array::any" => StaticValue::Bool(false),
                    "Array::all" => StaticValue::Bool(true),
                    _ => StaticValue::Unit,
                })
            }
            (
                "Array::fold",
                [
                    StaticValue::Array(values),
                    initial,
                    StaticValue::Callable(callable),
                ],
            ) => {
                let mut result = self.copy_static_value(initial)?;
                for value in values {
                    self.budget.event(budget::Event::LoopIteration)?;
                    let callback = self.copy_static_callable(callable)?;
                    let argument = self.copy_static_value(value)?;
                    result = self.invoke_callback(callback, vec![result, argument])?;
                }
                self.budget.event(budget::Event::LoopIteration)?;
                Ok(result)
            }
            ("Map::get", [StaticValue::Map(entries), key]) => Ok(option(
                entries
                    .iter()
                    .find(|(existing, _)| static_equal(existing, key))
                    .map(|(_, value)| value.clone()),
            )),
            ("Map::contains", [StaticValue::Map(entries), key]) => Ok(StaticValue::Bool(
                entries
                    .iter()
                    .any(|(existing, _)| static_equal(existing, key)),
            )),
            ("Map::keys", [StaticValue::Map(entries)]) => {
                Ok(self.array(entries.iter().map(|(key, _)| key.clone()).collect()))
            }
            ("Map::values", [StaticValue::Map(entries)]) => {
                Ok(self.array(entries.iter().map(|(_, value)| value.clone()).collect()))
            }
            ("Map::entries", [StaticValue::Map(entries)]) => {
                let values = entries
                    .iter()
                    .map(|(key, value)| self.tuple(vec![key.clone(), value.clone()]))
                    .collect();
                Ok(self.array(values))
            }
            ("Map::from", [StaticValue::Array(entries)]) => {
                let mut map = vec![];
                for entry in entries {
                    let StaticValue::Tuple(pair) = entry else {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "Map::from requires pairs".into(),
                        ));
                    };
                    if pair.len() != 2 {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "Map::from requires pairs".into(),
                        ));
                    }
                    if let Some((_, old)) =
                        map.iter_mut().find(|(key, _)| static_equal(key, &pair[0]))
                    {
                        *old = pair[1].clone();
                    } else {
                        map.push((pair[0].clone(), pair[1].clone()));
                    }
                }
                Ok(self.map(map))
            }
            (name, _) if name.starts_with("String::") => self.string_builtin(name, args),
            _ => Err(Failure::Diagnostic(
                "E0314",
                format!("invalid arguments to static builtin {name}"),
            )),
        }
    }
    fn string_builtin(&mut self, name: &str, args: Vec<StaticValue>) -> Result<StaticValue> {
        match (name, args.as_slice()) {
            ("String::split", [StaticValue::String(text), StaticValue::String(separator)]) => {
                Ok(self.array(if separator.is_empty() {
                    text.chars()
                        .map(|c| StaticValue::String(c.to_string()))
                        .collect()
                } else {
                    text.split(separator)
                        .map(|part| StaticValue::String(part.into()))
                        .collect()
                }))
            }
            ("String::trim", [StaticValue::String(text)]) => {
                Ok(StaticValue::String(text.trim_matches(white_space).into()))
            }
            (
                "String::contains" | "String::starts_with" | "String::ends_with",
                [StaticValue::String(text), StaticValue::String(needle)],
            ) => Ok(StaticValue::Bool(match name {
                "String::contains" => text.contains(needle),
                "String::starts_with" => text.starts_with(needle),
                _ => text.ends_with(needle),
            })),
            (
                "String::replace",
                [
                    StaticValue::String(text),
                    StaticValue::String(old),
                    StaticValue::String(new),
                ],
            ) => Ok(StaticValue::String(text.replace(old, new))),
            ("String::find", [StaticValue::String(text), StaticValue::String(needle)]) => {
                Ok(option(text.find(needle).map(|offset| {
                    StaticValue::Integer(text[..offset].chars().count() as i128)
                })))
            }
            (
                "String::slice",
                [
                    StaticValue::String(text),
                    StaticValue::Integer(start),
                    StaticValue::Integer(end),
                ],
            ) => {
                let values: Vec<_> = text.chars().collect();
                Ok(option(
                    if *start >= 0 && end >= start && *end as usize <= values.len() {
                        Some(StaticValue::String(
                            values[*start as usize..*end as usize].iter().collect(),
                        ))
                    } else {
                        None
                    },
                ))
            }
            ("String::concat", [StaticValue::String(a), StaticValue::String(b)]) => {
                Ok(StaticValue::String(a.clone() + b))
            }
            ("String::join", [StaticValue::Array(parts), StaticValue::String(separator)]) => {
                let parts = parts
                    .iter()
                    .map(|part| {
                        if let StaticValue::String(text) = part {
                            Ok(text.as_str())
                        } else {
                            Err(Failure::Diagnostic(
                                "E0301",
                                "String::join requires strings".into(),
                            ))
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(StaticValue::String(parts.join(separator)))
            }
            ("String::lines", [StaticValue::String(text)]) => {
                let mut lines: Vec<_> = text.split('\n').collect();
                if text.ends_with('\n') {
                    lines.pop();
                }
                if text.is_empty() {
                    lines.clear();
                }
                Ok(self.array(
                    lines
                        .iter()
                        .enumerate()
                        .map(|(index, line)| {
                            StaticValue::String(
                                if index + 1 < lines.len() || text.ends_with('\n') {
                                    line.strip_suffix('\r').unwrap_or(line)
                                } else {
                                    line
                                }
                                .to_string(),
                            )
                        })
                        .collect(),
                ))
            }
            ("String::scalar_at", [StaticValue::String(text), StaticValue::Integer(index)]) => {
                Ok(option(
                    usize::try_from(*index)
                        .ok()
                        .and_then(|index| text.chars().nth(index))
                        .map(|c| StaticValue::TypedInteger(i128::from(c as u32), 32, false)),
                ))
            }
            ("String::scalars", [StaticValue::String(text)]) => Ok(self.array(
                text.chars()
                    .map(|c| StaticValue::TypedInteger(i128::from(c as u32), 32, false))
                    .collect(),
            )),
            ("String::utf8", [StaticValue::String(text)]) => {
                Ok(StaticValue::Bytes(text.as_bytes().to_vec()))
            }
            ("String::byte_len", [StaticValue::String(text)]) => {
                Ok(StaticValue::Integer(text.len() as i128))
            }
            ("String::byte_offset", [StaticValue::String(text), StaticValue::Integer(index)]) => {
                let index = usize::try_from(*index).ok();
                let offset = index.and_then(|index| {
                    if index == text.chars().count() {
                        Some(text.len())
                    } else {
                        text.char_indices().nth(index).map(|(offset, _)| offset)
                    }
                });
                Ok(option(
                    offset.map(|offset| StaticValue::Integer(offset as i128)),
                ))
            }
            ("String::scalar_offset", [StaticValue::String(text), StaticValue::Integer(index)]) => {
                let offset = usize::try_from(*index)
                    .ok()
                    .filter(|index| text.is_char_boundary(*index))
                    .map(|index| text[..index].chars().count());
                Ok(option(
                    offset.map(|offset| StaticValue::Integer(offset as i128)),
                ))
            }
            _ => Err(Failure::Diagnostic(
                "E0314",
                format!("invalid static string arguments to {name}"),
            )),
        }
    }
}
fn option(value: Option<StaticValue>) -> StaticValue {
    if let Some(value) = value {
        StaticValue::Variant("Prelude::Some".into(), vec![value], None)
    } else {
        StaticValue::Variant("Prelude::None".into(), vec![], None)
    }
}
pub(super) fn static_builtin(name: &str) -> bool {
    matches!(
        name,
        "assert"
            | "len"
            | "byte_size"
            | "Array::first"
            | "Array::get"
            | "Array::contains"
            | "Array::reverse"
            | "Array::concat"
            | "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
            | "Map::get"
            | "Map::contains"
            | "Map::keys"
            | "Map::values"
            | "Map::entries"
            | "Map::from"
            | "String::split"
            | "String::trim"
            | "String::contains"
            | "String::starts_with"
            | "String::ends_with"
            | "String::replace"
            | "String::find"
            | "String::slice"
            | "String::concat"
            | "String::join"
            | "String::lines"
            | "String::scalar_at"
            | "String::scalars"
            | "String::utf8"
            | "String::byte_len"
            | "String::byte_offset"
            | "String::scalar_offset"
    )
}
fn white_space(c: char) -> bool {
    matches!(c,'\u{0009}'..='\u{000d}'|'\u{0020}'|'\u{0085}'|'\u{00a0}'|'\u{1680}'|'\u{2000}'..='\u{200a}'|'\u{2028}'|'\u{2029}'|'\u{202f}'|'\u{205f}'|'\u{3000}')
}
