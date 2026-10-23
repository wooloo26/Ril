//! One binding plan is shared by static typing and actual invocation.
//! Explicit values are evaluated before this plan supplies any default.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ParameterSpec {
    pub label: Option<String>,
    pub default: bool,
}
impl From<&Parameter> for ParameterSpec {
    fn from(parameter: &Parameter) -> Self {
        Self {
            label: match &parameter.pattern.kind {
                PatternKind::Name(name) | PatternKind::Rest(Some(name)) => Some(name.clone()),
                _ => None,
            },
            default: parameter.default.is_some(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ArgumentSlot {
    Explicit(usize),
    Default,
}

pub(super) struct StaticApplicationPlan {
    pub slots: Vec<ArgumentSlot>,
}
impl StaticApplicationPlan {
    pub fn new(
        parameters: &[ParameterSpec],
        labels: impl IntoIterator<Item = Option<String>>,
    ) -> Result<Self> {
        let mut slots = vec![None; parameters.len()];
        for (written, label) in labels.into_iter().enumerate() {
            let index = if let Some(label) = label {
                parameters
                    .iter()
                    .position(|parameter| parameter.label.as_ref() == Some(&label))
                    .ok_or_else(|| {
                        Failure::Diagnostic(
                            "E0339",
                            format!("unknown static parameter label {label}"),
                        )
                    })?
            } else {
                slots.iter().position(Option::is_none).ok_or_else(|| {
                    Failure::Diagnostic("E0314", "too many static arguments".into())
                })?
            };
            if slots[index]
                .replace(ArgumentSlot::Explicit(written))
                .is_some()
            {
                return Err(Failure::Diagnostic(
                    "E0325",
                    "static parameter supplied more than once".into(),
                ));
            }
        }
        let slots = slots
            .into_iter()
            .zip(parameters)
            .map(|(slot, parameter)| match slot {
                Some(slot) => Ok(slot),
                None if parameter.default => Ok(ArgumentSlot::Default),
                None => Err(Failure::Diagnostic(
                    "E0314",
                    "missing required static argument".into(),
                )),
            })
            .collect::<Result<_>>()?;
        Ok(Self { slots })
    }
}

#[derive(Clone)]
pub(super) struct StaticArgument {
    pub label: Option<String>,
    pub value: StaticValue,
}
impl From<StaticValue> for StaticArgument {
    fn from(value: StaticValue) -> Self {
        Self { label: None, value }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CallableView {
    pub target: Box<StaticCallable>,
    pub signature: TypeExpr,
    pub captured: environments::Environment,
}

pub(super) fn binding_names(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match &pattern.kind {
        PatternKind::Name(name) | PatternKind::Rest(Some(name)) => {
            if name != "_" {
                names.insert(name.clone());
            }
        }
        PatternKind::Tuple(items)
        | PatternKind::Array(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                binding_names(item, names);
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                binding_names(&field.pattern, names);
            }
            names.extend(rest_binding.iter().cloned());
        }
        PatternKind::Mode { pattern, .. } => binding_names(pattern, names),
        _ => {}
    }
}

impl Evaluator {
    pub(super) fn ascribe_application_value(
        &mut self,
        value: StaticValue,
        syntax: &TypeExpr,
    ) -> Result<StaticValue> {
        if !contains_callable(&value)
            && !contains_leaf(&value, |value| matches!(value, StaticValue::Result(_)))
        {
            return self.receive_source_type(value, syntax);
        }
        let resolved = self.resolve_type(syntax, &mut vec![])?;
        self.ascribe_application_value_from_resolved(value, syntax, &resolved)
    }
    pub(super) fn ascribe_application_value_from_resolved(
        &mut self,
        value: StaticValue,
        source: &TypeExpr,
        syntax: &TypeExpr,
    ) -> Result<StaticValue> {
        let mask = if contains_callable(&value) {
            self.generic_receiving_mask(source)?
        } else {
            None
        };
        let value = self.ascribe_application_resolved(
            value,
            syntax,
            mask.as_ref().map(|mask| (&mask.syntax, &mask.markers)),
        )?;
        self.receive_source_type(value, syntax)
    }
    fn ascribe_application_resolved(
        &mut self,
        value: StaticValue,
        syntax: &TypeExpr,
        mask: Option<(&TypeExpr, &BTreeSet<String>)>,
    ) -> Result<StaticValue> {
        self.charge()?;
        let mask = generic_receiving::transparent(mask);
        if let Some((
            TypeExpr {
                kind: TypeKind::Name { path, arguments },
                ..
            },
            markers,
        )) = mask
            && path.len() == 1
            && arguments.is_empty()
            && markers.contains(&path[0])
        {
            return Ok(value);
        }
        use generic_receiving::{Slot, child};
        Ok(match (value, &syntax.kind) {
            (
                StaticValue::Callable(callable),
                TypeKind::Callable {
                    parameters,
                    annotations,
                    ..
                },
            ) => {
                if !annotations.is_empty()
                    || parameters.iter().any(|parameter| {
                        parameter.mode != ParameterMode::Read || parameter.default.is_some()
                    })
                {
                    return Err(Failure::Unsupported("static destination callable has unsupported modes, defaults or obligations".into()));
                }
                let dependencies = effects::type_dependencies(syntax);
                let captured = self.capture_dependencies(&dependencies)?;
                let target = match callable {
                    StaticCallable::View(view) => view.target,
                    other => Box::new(other),
                };
                StaticValue::Callable(StaticCallable::View(Box::new(CallableView {
                    target,
                    signature: syntax.clone(),
                    captured,
                })))
            }
            (StaticValue::Array(items), TypeKind::Array { element, .. }) => {
                StaticValue::Array(StaticCollection {
                    id: items.id,
                    source_type: items.source_type.clone(),
                    values: std::sync::Arc::new(
                        items
                            .iter()
                            .cloned()
                            .map(|value| {
                                self.ascribe_application_resolved(
                                    value,
                                    element,
                                    child(mask, Slot::Element),
                                )
                            })
                            .collect::<Result<_>>()?,
                    ),
                })
            }
            (StaticValue::ArrayWindow(window), TypeKind::Array { .. }) => {
                StaticValue::ArrayWindow(window)
            }
            (StaticValue::Tuple(items), TypeKind::Tuple(types)) if items.len() == types.len() => {
                StaticValue::Tuple(StaticCollection {
                    id: items.id,
                    source_type: items.source_type.clone(),
                    values: std::sync::Arc::new(
                        items
                            .iter()
                            .cloned()
                            .zip(types)
                            .enumerate()
                            .map(|(index, (value, ty))| {
                                self.ascribe_application_resolved(
                                    value,
                                    ty,
                                    child(mask, Slot::Tuple(index)),
                                )
                            })
                            .collect::<Result<_>>()?,
                    ),
                })
            }
            (StaticValue::Record(record), TypeKind::Record { fields, row: None }) => {
                let mut values = record.storage.values.as_ref().clone();
                for field in fields {
                    if let Some(value) = values.remove(&field.name) {
                        values.insert(
                            field.name.clone(),
                            self.ascribe_application_resolved(
                                value,
                                &field.ty,
                                child(mask, Slot::Field(&field.name)),
                            )?,
                        );
                    }
                }
                StaticValue::Record(StaticRecord {
                    storage: StaticCollection {
                        id: record.storage.id,
                        source_type: record.storage.source_type.clone(),
                        values: std::sync::Arc::new(values),
                    },
                    mutable_fields: record.mutable_fields,
                })
            }
            (StaticValue::Map(items), TypeKind::Map { key, value }) => {
                StaticValue::Map(StaticCollection {
                    id: items.id,
                    source_type: items.source_type.clone(),
                    values: std::sync::Arc::new(
                        items
                            .iter()
                            .cloned()
                            .map(|(k, v)| {
                                Ok((
                                    self.ascribe_application_resolved(
                                        k,
                                        key,
                                        child(mask, Slot::MapKey),
                                    )?,
                                    self.ascribe_application_resolved(
                                        v,
                                        value,
                                        child(mask, Slot::MapValue),
                                    )?,
                                ))
                            })
                            .collect::<Result<_>>()?,
                    ),
                })
            }
            (StaticValue::Variant(name, items, metadata), TypeKind::Optional(inner))
                if name.strip_prefix("Prelude::").unwrap_or(&name) == "Some" =>
            {
                StaticValue::Variant(
                    name,
                    items
                        .into_iter()
                        .map(|value| {
                            self.ascribe_application_resolved(
                                value,
                                inner,
                                child(mask, Slot::Optional),
                            )
                        })
                        .collect::<Result<_>>()?,
                    metadata,
                )
            }
            (StaticValue::Variant(name, items, metadata), TypeKind::Name { path, arguments })
                if (path == &["Option"] || path == &["Prelude", "Option"])
                    && arguments.len() == 1
                    && name.strip_prefix("Prelude::").unwrap_or(&name) == "Some" =>
            {
                StaticValue::Variant(
                    name,
                    items
                        .into_iter()
                        .map(|value| {
                            self.ascribe_application_resolved(
                                value,
                                &arguments[0],
                                child(mask, Slot::Optional),
                            )
                        })
                        .collect::<Result<_>>()?,
                    metadata,
                )
            }
            (StaticValue::Result(mut produced), TypeKind::Name { path, arguments })
                if (path == &["Result"] || path == &["Prelude", "Result"])
                    && arguments.len() == 2 =>
            {
                produced.payload = self.ascribe_application_resolved(
                    produced.payload,
                    &arguments[usize::from(!produced.success)],
                    child(
                        mask,
                        if produced.success {
                            Slot::Success
                        } else {
                            Slot::Error
                        },
                    ),
                )?;
                if typing::closed_result_contract(self, syntax) {
                    produced.ty = Some(Box::new(syntax.clone()));
                }
                StaticValue::Result(produced)
            }
            (value, _) => value,
        })
    }
}
