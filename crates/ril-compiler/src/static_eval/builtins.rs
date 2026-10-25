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
            ("\0ril.storage.bytes_to_array", [StaticValue::Bytes(bytes)]) => Ok(self.array(
                bytes
                    .iter()
                    .map(|value| StaticValue::TypedInteger(i128::from(*value), 8, false))
                    .collect(),
            )),
            ("\0ril.storage.bytes_from_array", [input]) => {
                let values = match input {
                    StaticValue::Array(values) => values.iter().collect::<Vec<_>>(),
                    StaticValue::ArrayWindow(values) => values.iter().collect::<Vec<_>>(),
                    _ => {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "byte construction requires an array".into(),
                        ));
                    }
                };
                let bytes = values
                    .into_iter()
                    .map(|value| match value {
                        StaticValue::TypedInteger(value, 8, false) => {
                            u8::try_from(*value).map_err(|_| {
                                Failure::Diagnostic("E0301", "byte outside u8 range".into())
                            })
                        }
                        _ => Err(Failure::Diagnostic(
                            "E0301",
                            "byte construction requires u8 elements".into(),
                        )),
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(StaticValue::Bytes(bytes))
            }
            ("\0ril.storage.sqrt_f32", [StaticValue::Float(value, true)]) => {
                let result = (*value as f32).sqrt();
                Ok(StaticValue::Float(
                    f64::from(if result.is_nan() {
                        f32::from_bits(0x7fc00000)
                    } else {
                        result
                    }),
                    true,
                ))
            }
            ("\0ril.storage.sqrt_f64", [StaticValue::Float(value, false)]) => {
                let result = value.sqrt();
                Ok(StaticValue::Float(
                    if result.is_nan() {
                        f64::from_bits(0x7ff8000000000000)
                    } else {
                        result
                    },
                    false,
                ))
            }
            ("\0ril.storage.f32_bits", [StaticValue::Float(value, true)]) => {
                Ok(StaticValue::TypedInteger(
                    i128::from(if value.is_nan() {
                        0x7fc00000u32
                    } else {
                        (*value as f32).to_bits()
                    }),
                    32,
                    false,
                ))
            }
            ("\0ril.storage.f64_bits", [StaticValue::Float(value, false)]) => {
                Ok(StaticValue::TypedInteger(
                    i128::from(if value.is_nan() {
                        0x7ff8000000000000u64
                    } else {
                        value.to_bits()
                    }),
                    64,
                    false,
                ))
            }
            ("\0ril.storage.f32_from_bits", [StaticValue::TypedInteger(value, 32, false)]) => {
                let raw = u32::try_from(*value)
                    .map_err(|_| Failure::Diagnostic("E0301", "expected u32 float bits".into()))?;
                let value = f32::from_bits(raw);
                Ok(StaticValue::Float(
                    f64::from(if value.is_nan() {
                        f32::from_bits(0x7fc00000)
                    } else {
                        value
                    }),
                    true,
                ))
            }
            ("\0ril.storage.f64_from_bits", [StaticValue::TypedInteger(value, 64, false)]) => {
                let raw = u64::try_from(*value)
                    .map_err(|_| Failure::Diagnostic("E0301", "expected u64 float bits".into()))?;
                let value = f64::from_bits(raw);
                Ok(StaticValue::Float(
                    if value.is_nan() {
                        f64::from_bits(0x7ff8000000000000)
                    } else {
                        value
                    },
                    false,
                ))
            }
            ("\0ril.storage.string_scalars", [StaticValue::String(text)]) => Ok(self.array(
                text.chars()
                    .map(|value| StaticValue::TypedInteger(i128::from(value as u32), 32, false))
                    .collect(),
            )),
            ("\0ril.storage.string_utf8", [StaticValue::String(text)]) => {
                Ok(StaticValue::Bytes(text.as_bytes().to_vec()))
            }
            ("\0ril.storage.string_from_scalars", [input]) => {
                let values = match input {
                    StaticValue::Array(values) => values.iter().collect::<Vec<_>>(),
                    StaticValue::ArrayWindow(values) => values.iter().collect::<Vec<_>>(),
                    _ => {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "scalar string construction requires an array".into(),
                        ));
                    }
                };
                let mut text = String::new();
                for value in values {
                    let StaticValue::TypedInteger(value, 32, false) = value else {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "scalar string construction requires u32 elements".into(),
                        ));
                    };
                    let scalar = u32::try_from(*value)
                        .ok()
                        .and_then(char::from_u32)
                        .ok_or_else(|| {
                            Failure::Diagnostic(
                                "E0830",
                                "string construction received a nonscalar".into(),
                            )
                        })?;
                    text.push(scalar);
                }
                Ok(StaticValue::String(text))
            }
            _ => Err(Failure::Diagnostic(
                "E0314",
                format!("invalid arguments to static builtin {name}"),
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
            | "\0ril.storage.bytes_from_array"
            | "\0ril.storage.bytes_to_array"
            | "\0ril.storage.f32_bits"
            | "\0ril.storage.f32_from_bits"
            | "\0ril.storage.f64_bits"
            | "\0ril.storage.f64_from_bits"
            | "\0ril.storage.sqrt_f32"
            | "\0ril.storage.sqrt_f64"
            | "\0ril.storage.string_scalars"
            | "\0ril.storage.string_utf8"
            | "\0ril.storage.string_from_scalars"
    )
}
