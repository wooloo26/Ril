//! Immutable complete type views carried by evaluated collection handles.
//! Neither backing cardinality nor a bound view supplies a declared type.
use super::*;
use crate::sema::model::SourceTypeWitness;
use std::sync::Arc;

impl Evaluator {
    pub(super) fn source_type_witness(
        &self,
        syntax: TypeExpr,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        clone_work::type_syntax(&self.budget, &syntax)?;
        let Some(syntax) = crate::sema::checker::normalize_closed_source_syntax(
            &syntax,
            &self.declarations,
            self.layout,
        ) else {
            return Ok(None);
        };
        let key = normalized_argument_key(&syntax);
        self.budget.work(key.len() as u64)?;
        let witness = SourceTypeWitness { syntax, key };
        Ok(witness.validate_closed().then(|| Arc::new(witness)))
    }

    /// Substitute already bound immutable type values. Computations/defaults
    /// are not executed to recover metadata; their earlier witness is required.
    fn frozen_source_syntax(&self, syntax: &TypeExpr) -> Result<Option<TypeExpr>> {
        fn substitute(
            evaluator: &Evaluator,
            syntax: &TypeExpr,
            depth: usize,
            nodes: &mut usize,
        ) -> Result<Option<TypeExpr>> {
            *nodes += 1;
            if depth >= 64 || *nodes > 4096 {
                return Ok(None);
            }
            if let TypeKind::Name { path, arguments } = &syntax.kind
                && arguments.is_empty()
                && let Some(StaticValue::Type(actual)) = evaluator.values.get(&path.join("::"))
            {
                clone_work::type_syntax(&evaluator.budget, actual)?;
                return Ok(Some(actual.clone()));
            }
            clone_work::type_syntax(&evaluator.budget, syntax)?;
            let Ok(mut output) = evaluator.numeric_context_witness(syntax, depth) else {
                return Ok(None);
            };
            let mut child = |syntax: &TypeExpr| substitute(evaluator, syntax, depth + 1, nodes);
            match &mut output.kind {
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    for argument in arguments {
                        let Some(actual) = child(argument)? else {
                            return Ok(None);
                        };
                        *argument = actual;
                    }
                }
                TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
                    let Some(actual) = child(inner)? else {
                        return Ok(None);
                    };
                    **inner = actual;
                }
                TypeKind::Map { key, value } => {
                    let Some(actual_key) = child(key)? else {
                        return Ok(None);
                    };
                    let Some(actual_value) = child(value)? else {
                        return Ok(None);
                    };
                    **key = actual_key;
                    **value = actual_value;
                }
                TypeKind::Record { fields, row: None } => {
                    for field in fields {
                        let Some(actual) = child(&field.ty)? else {
                            return Ok(None);
                        };
                        field.ty = actual;
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        if let Some(ty) = &mut parameter.ty {
                            let Some(actual) = child(ty)? else {
                                return Ok(None);
                            };
                            *ty = actual;
                        }
                    }
                    if let Some(result) = result {
                        let Some(actual) = child(result)? else {
                            return Ok(None);
                        };
                        **result = actual;
                    }
                }
                _ => return Ok(None),
            }
            Ok(Some(output))
        }
        substitute(self, syntax, 0, &mut 0)
    }

    pub(super) fn receive_source_type(
        &self,
        mut value: StaticValue,
        resolved: &TypeExpr,
    ) -> Result<StaticValue> {
        if (value.collection_id().is_some() || matches!(value, StaticValue::Variant(..)))
            && let Some(syntax) = self.frozen_source_syntax(resolved)?
            && let Some(witness) = self.source_type_witness(syntax)?
        {
            set_view(&mut value, witness);
        }
        Ok(value)
    }

    pub(super) fn infer_source_type(
        &self,
        mut value: StaticValue,
        span: Span,
    ) -> Result<StaticValue> {
        if value.collection_id().is_some()
            && view(&value).is_none()
            && let Some(witness) = self.complete_source_type(&value, span)?
        {
            set_view(&mut value, witness);
        }
        Ok(value)
    }

    pub(super) fn complete_source_type(
        &self,
        value: &StaticValue,
        span: Span,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        Derive {
            evaluator: self,
            memo: BTreeMap::new(),
            active: BTreeSet::new(),
            nodes: 0,
            span,
        }
        .value(value, 0)
    }

    pub(super) fn project_source_field(
        &self,
        base: &StaticValue,
        child: StaticValue,
        label: &str,
    ) -> Result<StaticValue> {
        let Some(witness) = view(base) else {
            return Ok(child);
        };
        let syntax = match &witness.syntax.kind {
            TypeKind::Record { fields, .. } => fields
                .iter()
                .find(|field| field.name == label)
                .map(|field| &field.ty),
            TypeKind::Tuple(items) => label
                .parse::<usize>()
                .ok()
                .and_then(|index| items.get(index)),
            _ => None,
        };
        match syntax {
            Some(syntax) => self.receive_source_type(child, syntax),
            None => Ok(child),
        }
    }

    pub(super) fn project_source_index(
        &self,
        base: &StaticValue,
        child: StaticValue,
    ) -> Result<StaticValue> {
        let Some(witness) = view(base) else {
            return Ok(child);
        };
        let syntax = match &witness.syntax.kind {
            TypeKind::Array { element, .. } => Some(&**element),
            TypeKind::Map { value, .. } => Some(&**value),
            _ => None,
        };
        match syntax {
            Some(syntax) => self.receive_source_type(child, syntax),
            None => Ok(child),
        }
    }
}

pub(super) fn view(value: &StaticValue) -> Option<&Arc<SourceTypeWitness>> {
    match value {
        StaticValue::Array(value) | StaticValue::Tuple(value) => value.source_type.as_ref(),
        StaticValue::Record(value) => value.storage.source_type.as_ref(),
        StaticValue::Map(value) => value.source_type.as_ref(),
        StaticValue::Variant(_, _, metadata) => metadata.as_ref(),
        _ => None,
    }
}
fn set_view(value: &mut StaticValue, witness: Arc<SourceTypeWitness>) {
    match value {
        StaticValue::Array(value) | StaticValue::Tuple(value) => value.source_type = Some(witness),
        StaticValue::Record(value) => value.storage.source_type = Some(witness),
        StaticValue::Map(value) => value.source_type = Some(witness),
        StaticValue::Variant(_, _, metadata) => *metadata = Some(witness),
        _ => {}
    }
}

struct Derive<'a> {
    evaluator: &'a Evaluator,
    memo: BTreeMap<u64, Option<Arc<SourceTypeWitness>>>,
    active: BTreeSet<u64>,
    nodes: usize,
    span: Span,
}
impl Derive<'_> {
    fn syntax(&self, witness: &SourceTypeWitness) -> Result<TypeExpr> {
        clone_work::type_syntax(&self.evaluator.budget, &witness.syntax)?;
        Ok(witness.syntax.clone())
    }
    fn value(
        &mut self,
        value: &StaticValue,
        depth: usize,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        self.evaluator.budget.work(1)?;
        self.nodes += 1;
        if depth >= 64 || self.nodes > 4096 {
            return Ok(None);
        }
        if let Some(witness) = view(value) {
            return Ok(Some(witness.clone()));
        }
        let id = value.collection_id();
        if let Some(id) = id {
            if let Some(witness) = self.memo.get(&id) {
                return Ok(witness.clone());
            }
            if !self.active.insert(id) {
                return Ok(None);
            }
        }
        let result = self.inner(value, depth);
        if let Some(id) = id {
            self.active.remove(&id);
            if let Ok(witness) = &result {
                self.memo.insert(id, witness.clone());
            }
        }
        result
    }
    fn homogeneous<'a>(
        &mut self,
        values: impl Iterator<Item = &'a StaticValue>,
        depth: usize,
    ) -> Result<Option<TypeExpr>> {
        let mut selected: Option<Arc<SourceTypeWitness>> = None;
        for value in values {
            let Some(witness) = self.value(value, depth + 1)? else {
                return Ok(None);
            };
            if selected.as_ref().is_some_and(|old| old.key != witness.key) {
                return Ok(None);
            }
            selected = Some(witness);
        }
        selected
            .as_ref()
            .map(|witness| self.syntax(witness))
            .transpose()
    }
    fn inner(
        &mut self,
        value: &StaticValue,
        depth: usize,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        let primitive = match value {
            StaticValue::Integer(_) => Some("int".to_owned()),
            StaticValue::TypedInteger(_, bits, signed) => {
                Some(format!("{}{bits}", if *signed { 'i' } else { 'u' }))
            }
            StaticValue::Float(_, narrow) => Some(if *narrow { "f32" } else { "f64" }.into()),
            StaticValue::BigInteger(_) => Some("bigint".into()),
            StaticValue::Bool(_) => Some("bool".into()),
            StaticValue::String(_) => Some("str".into()),
            StaticValue::Bytes(_) => Some("bytes".into()),
            _ => None,
        };
        if let Some(name) = primitive {
            return self
                .evaluator
                .source_type_witness(numeric_contexts::syntax(&name, self.span));
        }
        let kind = match value {
            StaticValue::Unit => TypeKind::Tuple(vec![]),
            StaticValue::Array(values) => {
                let Some(element) = self.homogeneous(values.iter(), depth)? else {
                    return Ok(None);
                };
                TypeKind::Array {
                    length: None,
                    element: Box::new(element),
                }
            }
            StaticValue::Tuple(values) => {
                let mut types = Vec::new();
                for value in values {
                    let Some(witness) = self.value(value, depth + 1)? else {
                        return Ok(None);
                    };
                    types.push(self.syntax(&witness)?);
                }
                TypeKind::Tuple(types)
            }
            StaticValue::Record(values) => {
                let mut fields = Vec::new();
                for (name, value) in values.iter() {
                    self.evaluator.budget.work(name.len() as u64 + 1)?;
                    let Some(witness) = self.value(value, depth + 1)? else {
                        return Ok(None);
                    };
                    fields.push(TypeField {
                        name: name.clone(),
                        mutable: values.mutable_fields.contains(name),
                        ty: self.syntax(&witness)?,
                        span: self.span,
                    });
                }
                TypeKind::Record { fields, row: None }
            }
            StaticValue::Map(values) => {
                let Some(key) = self.homogeneous(values.iter().map(|(key, _)| key), depth)? else {
                    return Ok(None);
                };
                let Some(value) = self.homogeneous(values.iter().map(|(_, value)| value), depth)?
                else {
                    return Ok(None);
                };
                TypeKind::Map {
                    key: Box::new(key),
                    value: Box::new(value),
                }
            }
            StaticValue::Variant(name, values, _)
                if name.trim_start_matches("Prelude::") == "Some" && values.len() == 1 =>
            {
                let Some(witness) = self.value(&values[0], depth + 1)? else {
                    return Ok(None);
                };
                TypeKind::Optional(Box::new(self.syntax(&witness)?))
            }
            StaticValue::Result(produced) => {
                return produced
                    .ty
                    .as_deref()
                    .map(|syntax| {
                        clone_work::type_syntax(&self.evaluator.budget, syntax)?;
                        self.evaluator.source_type_witness(syntax.clone())
                    })
                    .unwrap_or(Ok(None));
            }
            StaticValue::Callable(StaticCallable::Prepared(prepared)) => {
                let mut parameters = prepared.signature.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                let syntax = TypeExpr {
                    text: String::new(),
                    span: self.span,
                    kind: TypeKind::Callable {
                        parameters,
                        result: prepared.signature.result.clone().map(Box::new),
                        annotations: self.evaluator.functions[&prepared.name].annotations.clone(),
                    },
                };
                return self.evaluator.source_type_witness(syntax);
            }
            StaticValue::Callable(StaticCallable::View(view)) => {
                clone_work::type_syntax(&self.evaluator.budget, &view.signature)?;
                return self.evaluator.source_type_witness(view.signature.clone());
            }
            StaticValue::Callable(StaticCallable::Named { name, captured }) => {
                let Some(signature) = self.evaluator.frozen_static_signature(name, *captured)
                else {
                    return Ok(None);
                };
                let mut parameters = Vec::new();
                for parameter in &signature.parameters {
                    let Some(ty) = &parameter.ty else {
                        return Ok(None);
                    };
                    clone_work::type_syntax(&self.evaluator.budget, ty)?;
                    parameters.push(Parameter {
                        pattern: parameter.pattern.clone(),
                        mode: parameter.mode,
                        ty: Some(ty.clone()),
                        default: None,
                        span: parameter.span,
                    });
                }
                let result = signature
                    .result
                    .as_ref()
                    .map(|ty| {
                        clone_work::type_syntax(&self.evaluator.budget, ty)?;
                        Ok(Box::new(ty.clone()))
                    })
                    .transpose()?;
                TypeKind::Callable {
                    parameters,
                    result,
                    annotations: vec![],
                }
            }
            StaticValue::Callable(StaticCallable::Lambda {
                parameters,
                return_type: Some(result),
                ..
            }) => {
                let mut inputs = Vec::new();
                for parameter in parameters {
                    let Some(ty) = &parameter.ty else {
                        return Ok(None);
                    };
                    clone_work::type_syntax(&self.evaluator.budget, ty)?;
                    inputs.push(Parameter {
                        pattern: parameter.pattern.clone(),
                        mode: parameter.mode,
                        ty: Some(ty.clone()),
                        default: None,
                        span: parameter.span,
                    });
                }
                clone_work::type_syntax(&self.evaluator.budget, result)?;
                TypeKind::Callable {
                    parameters: inputs,
                    result: Some(result.clone()),
                    annotations: vec![],
                }
            }
            _ => return Ok(None),
        };
        self.evaluator.source_type_witness(TypeExpr {
            kind,
            text: String::new(),
            span: self.span,
        })
    }
}
