//! Literal selection precedes evaluation. Stored values never regain this right.
use super::*;
use crate::numeric_literals::{
    EncodedNumber, Error, ExactLiteral, FloatFormat, NumberType, ParseLimit,
};

pub(super) fn number_type(ty: &TypeExpr) -> Option<NumberType> {
    let TypeKind::Name { path, arguments } = &ty.kind else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    let name = path.join("::");
    number_name(name.strip_prefix("Prelude::").unwrap_or(&name))
}

pub(super) fn number_name(name: &str) -> Option<NumberType> {
    Some(match name {
        "int" => NumberType::Int,
        "i8" => NumberType::I8,
        "i16" => NumberType::I16,
        "i32" => NumberType::I32,
        "i64" => NumberType::I64,
        "u8" => NumberType::U8,
        "u16" => NumberType::U16,
        "u32" => NumberType::U32,
        "u64" => NumberType::U64,
        "bigint" => NumberType::BigInt,
        "f32" => NumberType::F32,
        "f64" => NumberType::F64,
        _ => return None,
    })
}

pub(super) fn failure(error: Error) -> Failure {
    match error {
        Error::InvalidSyntax => Failure::Diagnostic("E0111", "invalid numeric literal".into()),
        Error::IncompatibleSelection => Failure::Diagnostic(
            "E0301",
            "numeric literal has an incompatible selected type".into(),
        ),
        Error::OutOfRange => Failure::Diagnostic(
            "E0326",
            "numeric literal is outside its selected type".into(),
        ),
        Error::ResourceLimit => Failure::Unsupported(
            "exact static literal exceeds implementation parsing resources".into(),
        ),
        Error::UnsupportedTarget | Error::UnsupportedDecimal => Failure::Unsupported(
            "exact static numeric selection is unavailable for this target or spelling".into(),
        ),
    }
}

pub(super) fn selected(
    text: &str,
    float: bool,
    negative: bool,
    expected: Option<NumberType>,
    layout: TargetLayout,
) -> Result<StaticValue> {
    if float
        && let Some(value) = committed_float::decode(text).map_err(|()| {
            Failure::Diagnostic("E0111", "malformed committed float witness".into())
        })?
    {
        // This is ordinary negation of a committed float, not reselection.
        return Ok(StaticValue::Float(
            if negative {
                -value.value()
            } else {
                value.value()
            },
            value.width == 32,
        ));
    }
    let limit = ParseLimit {
        max_bytes: 1_048_576,
    };
    let exact = if float {
        ExactLiteral::decimal(text, negative, limit)
    } else {
        ExactLiteral::integer(text, negative, limit)
    }
    .map_err(failure)?;
    let selected = exact.written_type().or(expected).unwrap_or(if float {
        NumberType::F64
    } else {
        NumberType::Int
    });
    Ok(match exact.select(selected, layout).map_err(failure)? {
        EncodedNumber::Integer {
            value,
            ty: NumberType::Int,
            ..
        } => StaticValue::Integer(value),
        EncodedNumber::Integer {
            value,
            bits,
            signed,
            ..
        } => StaticValue::TypedInteger(value, bits, signed),
        EncodedNumber::BigInteger(value) => StaticValue::BigInteger(value),
        EncodedNumber::Float(value) => {
            StaticValue::Float(value.as_f64(), value.format() == FloatFormat::F32)
        }
    })
}

pub(super) fn syntax(name: &str, span: Span) -> TypeExpr {
    TypeExpr {
        text: name.into(),
        kind: TypeKind::Name {
            path: vec![name.into()],
            arguments: vec![],
        },
        span,
    }
}

impl Evaluator {
    pub(super) fn numeric_arguments(
        &mut self,
        callable: &StaticCallable,
        arguments: &[Argument],
        expected: Option<&TypeExpr>,
    ) -> Result<Vec<application::StaticArgument>> {
        let saved = self.capture_environment()?;
        let parameters = (|| match callable {
            StaticCallable::Prepared(prepared) => {
                for parameter in &prepared.signature.parameters {
                    if let Some(ty) = &parameter.ty {
                        clone_work::type_syntax(&self.budget, ty)?;
                    }
                }
                Ok(Some(prepared.signature.parameters.clone()))
            }
            StaticCallable::View(view) => {
                let TypeKind::Callable { parameters, .. } = &view.signature.kind else {
                    return Err(Failure::Unsupported(
                        "static callable view signature".into(),
                    ));
                };
                Ok(Some(parameters.clone()))
            }
            StaticCallable::Lambda { parameters, .. } => Ok(Some(parameters.clone())),
            StaticCallable::Named { name, captured } => {
                self.install_environment(self.declaration_environment(*captured)?);
                let function = self.functions.get(name).cloned().ok_or_else(|| {
                    Failure::Unsupported("static parameter target declaration".into())
                })?;
                if !function.generics.is_empty()
                    && expected.is_some_and(|ty| number_type(ty).is_some())
                {
                    return Err(Failure::Unsupported(
                        "static generic result context requires complete application preparation"
                            .into(),
                    ));
                }
                let mut parameters = self.static_parameter_witnesses(&function)?;
                for parameter in &mut parameters {
                    if let Some(TypeExpr {
                        kind: TypeKind::Name { path, arguments },
                        ..
                    }) = &parameter.ty
                        && path.len() == 1
                        && arguments.is_empty()
                        && let Some(generic) = function
                            .generics
                            .iter()
                            .find(|generic| generic.name == path[0])
                        && let Some(
                            bound @ TypeExpr {
                                kind: TypeKind::Record { .. },
                                ..
                            },
                        ) = &generic.bound
                    {
                        clone_work::type_syntax(&self.budget, bound)?;
                        parameter.ty = Some(bound.clone());
                    }
                }
                Ok(Some(parameters))
            }
            StaticCallable::Builtin(_) => Ok(None),
        })();
        self.install_environment(saved);
        let parameters = parameters?;
        let mut contexts = vec![None; arguments.len()];
        if let Some(parameters) = parameters {
            let descriptors = parameters
                .iter()
                .map(application::ParameterSpec::from)
                .collect::<Vec<_>>();
            let plan = application::StaticApplicationPlan::new(
                &descriptors,
                arguments.iter().map(|argument| argument.label.clone()),
            )?;
            for (parameter, slot) in parameters.into_iter().zip(plan.slots) {
                if let application::ArgumentSlot::Explicit(index) = slot {
                    contexts[index] = parameter.ty;
                }
            }
        } else if let StaticCallable::Builtin(name) = callable
            && matches!(
                name.strip_prefix("Prelude::").unwrap_or(name),
                "Some" | "Ok" | "Err"
            )
        {
            let name = name.strip_prefix("Prelude::").unwrap_or(name);
            let payload = expected.and_then(|ty| match &ty.kind {
                TypeKind::Optional(inner) => Some((**inner).clone()),
                TypeKind::Name { path, arguments }
                    if (path == &["Option"] || path == &["Prelude", "Option"])
                        && arguments.len() == 1 =>
                {
                    Some(arguments[0].clone())
                }
                TypeKind::Name { path, arguments }
                    if (path == &["Result"] || path == &["Prelude", "Result"])
                        && arguments.len() == 2 =>
                {
                    Some(arguments[usize::from(name == "Err")].clone())
                }
                _ => None,
            });
            if arguments.len() == 1 {
                contexts[0] = payload;
            } else if let Some(TypeExpr {
                kind: TypeKind::Tuple(types),
                ..
            }) = payload
                && types.len() == arguments.len()
            {
                contexts = types.into_iter().map(Some).collect();
            }
        }
        arguments
            .iter()
            .zip(contexts)
            .map(|(argument, expected)| {
                Ok(application::StaticArgument {
                    label: argument.label.clone(),
                    value: self.expression_expected(&argument.value, false, expected.as_ref())?,
                })
            })
            .collect()
    }

    pub(super) fn numeric_literal(
        &mut self,
        text: &str,
        float: bool,
        negative: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        self.budget
            .work(u64::try_from(text.len()).unwrap_or(u64::MAX))?;
        selected(
            text,
            float,
            negative,
            expected.and_then(number_type),
            self.layout,
        )
    }

    pub(super) fn numeric_context_witness(&self, ty: &TypeExpr, depth: usize) -> Result<TypeExpr> {
        if depth >= 64 {
            return Err(Failure::Unsupported(
                "static argument annotation witness exceeds structural depth".into(),
            ));
        }
        let mut resolved = ty.clone();
        match &mut resolved.kind {
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                if let Some(declaration) = self.declarations.get(&name) {
                    let key = types::TypeInstanceKey::new(
                        name.clone(),
                        self.function_environments.get(&name).copied(),
                        arguments,
                    );
                    if let Some(witness) = self.alias_instances.get(&key) {
                        return Ok(witness.clone());
                    }
                    if declaration.generics.is_empty()
                        && arguments.is_empty()
                        && !declaration.nominal
                        && !declaration.opaque
                        && declaration.variants.is_empty()
                        && let Some(value) = &declaration.value
                    {
                        return self.numeric_context_witness(value, depth + 1);
                    }
                    return Err(Failure::Unsupported(
                        "static argument requires a prepared alias instance witness".into(),
                    ));
                }
                for argument in arguments {
                    *argument = self.numeric_context_witness(argument, depth + 1)?;
                }
            }
            TypeKind::Optional(inner) => {
                **inner = self.numeric_context_witness(inner, depth + 1)?
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    *item = self.numeric_context_witness(item, depth + 1)?;
                }
            }
            TypeKind::Array { element, .. } => {
                **element = self.numeric_context_witness(element, depth + 1)?
            }
            TypeKind::Map { key, value } => {
                **key = self.numeric_context_witness(key, depth + 1)?;
                **value = self.numeric_context_witness(value, depth + 1)?;
            }
            TypeKind::Record { fields, row: None } => {
                for field in fields {
                    field.ty = self.numeric_context_witness(&field.ty, depth + 1)?;
                }
            }
            TypeKind::Callable {
                parameters, result, ..
            } => {
                for parameter in parameters {
                    if let Some(ty) = &mut parameter.ty {
                        *ty = self.numeric_context_witness(ty, depth + 1)?;
                    }
                }
                if let Some(result) = result {
                    **result = self.numeric_context_witness(result, depth + 1)?;
                }
            }
            _ => return Err(Failure::Unsupported(
                "static numeric argument context requires an already elaborated annotation witness"
                    .into(),
            )),
        }
        Ok(resolved)
    }

    pub(super) fn rigid_numeric_peer(&self, expression: &Expr) -> Option<TypeExpr> {
        if let ExprKind::Binary {
            operator,
            left,
            right,
        } = &expression.kind
            && matches!(
                operator.as_str(),
                "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^"
            )
        {
            return self
                .rigid_numeric_peer(left)
                .or_else(|| self.rigid_numeric_peer(right));
        }
        let name = match &expression.kind {
            ExprKind::Name(name) => Some(name.clone()),
            ExprKind::Path(path) => Some(path.join("::")),
            _ => None,
        };
        if let Some(value) = name.as_ref().and_then(|name| self.values.get(name)) {
            let name = match value {
                StaticValue::Integer(_) => "int".into(),
                StaticValue::TypedInteger(_, bits, signed) => {
                    format!("{}{bits}", if *signed { 'i' } else { 'u' })
                }
                StaticValue::Float(_, true) => "f32".into(),
                StaticValue::Float(_, false) => "f64".into(),
                StaticValue::BigInteger(_) => "bigint".into(),
                _ => return None,
            };
            return Some(syntax(&name, expression.span));
        }
        let (literal, negative) = match &expression.kind {
            ExprKind::Literal(literal) => (literal, false),
            ExprKind::Unary { operator, operand } if operator == "-" => {
                let ExprKind::Literal(literal) = &operand.kind else {
                    return None;
                };
                (literal, true)
            }
            _ => return None,
        };
        let limit = ParseLimit {
            max_bytes: 1_048_576,
        };
        let exact = match literal {
            Literal::Integer(text) => ExactLiteral::integer(text, negative, limit),
            Literal::Float(text) => ExactLiteral::decimal(text, negative, limit),
            _ => return None,
        }
        .ok()?;
        let name = format!("{:?}", exact.written_type()?).to_lowercase();
        Some(syntax(&name, expression.span))
    }
}
