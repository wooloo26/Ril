//! Static pattern selection keeps the backing graph of immutable array views.
use super::*;

impl Evaluator {
    pub(super) fn static_record_remainder(
        &mut self,
        source: &StaticValue,
        fields: &[PatternField],
        span: Span,
    ) -> Result<StaticValue> {
        let StaticValue::Record(values) = source else {
            return Err(Failure::Diagnostic(
                "E0301",
                "record rest requires a record".into(),
            ));
        };
        let removed: BTreeSet<_> = fields.iter().map(|field| field.name.clone()).collect();
        self.budget.work(fields.len() as u64 + 1)?;
        let mut members = BTreeMap::new();
        let mut mutable = BTreeSet::new();
        for (name, value) in values.iter() {
            self.budget.work(name.len() as u64 + 1)?;
            if !removed.contains(name) {
                members.insert(name.clone(), self.copy_static_value(value)?);
                if values.mutable_fields.contains(name) {
                    mutable.insert(name.clone());
                }
            }
        }
        let mut remainder = self.record(members, mutable);
        if let Some(witness) = source_types::view(source) {
            let source_type = self.project_source_schema(
                witness,
                &[ril_compiler_core::projection::TypeProjection::RecordRemainder(removed)],
                span,
            )?;
            if let StaticValue::Record(record) = &mut remainder {
                record.storage.source_type = source_type;
            }
        }
        Ok(remainder)
    }

    pub(super) fn match_sequence(
        &mut self,
        patterns: &[Pattern],
        values: &[StaticValue],
        array: Option<&StaticValue>,
    ) -> Result<bool> {
        self.budget.work(patterns.len() as u64 + 1)?;
        let mut rest = None;
        for (index, pattern) in patterns.iter().enumerate() {
            if matches!(pattern.kind, PatternKind::Rest(_)) && rest.replace(index).is_some() {
                return Err(Failure::Diagnostic(
                    "E0347",
                    "one sequence pattern permits at most one rest".into(),
                ));
            }
        }
        let minimum = patterns.len() - usize::from(rest.is_some());
        if values.len() < minimum || (rest.is_none() && values.len() != minimum) {
            return Ok(false);
        }
        for (index, pattern) in patterns.iter().enumerate() {
            if let PatternKind::Rest(name) = &pattern.kind {
                if let Some(name) = name {
                    let source = array
                        .filter(|source| source.array_items().is_some())
                        .ok_or_else(|| {
                            Failure::Diagnostic(
                                "E0120",
                                "tuple rest cannot introduce a binding".into(),
                            )
                        })?;
                    if name != "_" {
                        let value = self.static_array_window(
                            source,
                            index,
                            patterns.len() - index - 1,
                            pattern.span,
                        )?;
                        self.type_environment.mask_const(name);
                        self.values.insert(name.clone(), value);
                    }
                }
                continue;
            }
            let actual = if rest.is_some_and(|rest| index > rest) {
                values.len() - (patterns.len() - index)
            } else {
                index
            };
            let child = self.copy_static_value(&values[actual])?;
            let child = if let Some(source) = array {
                if source.array_items().is_some() {
                    self.project_source_index(source, child)?
                } else {
                    self.project_source_field(source, child, &actual.to_string())?
                }
            } else {
                child
            };
            if !self.match_pattern(pattern, &child)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn static_array_window(
        &mut self,
        source: &StaticValue,
        prefix: usize,
        suffix: usize,
        span: Span,
    ) -> Result<StaticValue> {
        let (backing, offset, length) = match source {
            StaticValue::Array(values) => (values.clone(), 0, values.len()),
            StaticValue::ArrayWindow(window) => (window.backing.clone(), window.start, window.len),
            _ => {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "array remainder requires an array".into(),
                ));
            }
        };
        self.budget.work(4)?;
        let len = length
            .checked_sub(prefix)
            .and_then(|length| length.checked_sub(suffix))
            .ok_or_else(|| {
                Failure::Diagnostic("E0301", "array pattern exceeds its source length".into())
            })?;
        let start = offset
            .checked_add(prefix)
            .ok_or_else(|| Failure::Unsupported("static window offset overflow".into()))?;
        let source_type = self.array_remainder_source(source, prefix, suffix, span)?;
        let id = self.next_collection;
        self.next_collection = id
            .checked_add(1)
            .ok_or_else(|| Failure::Unsupported("static window identities exhausted".into()))?;
        Ok(StaticValue::ArrayWindow(Box::new(StaticArrayWindow {
            id,
            backing,
            start,
            len,
            source_type,
        })))
    }

    fn array_remainder_source(
        &self,
        source: &StaticValue,
        prefix: usize,
        suffix: usize,
        span: Span,
    ) -> Result<Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>> {
        let Some(witness) = source_types::view(source) else {
            return Ok(None);
        };
        let prefix = u32::try_from(prefix)
            .map_err(|_| Failure::Unsupported("static rest coordinate limit".into()))?;
        let suffix = u32::try_from(suffix)
            .map_err(|_| Failure::Unsupported("static rest coordinate limit".into()))?;
        self.project_source_schema(
            witness,
            &[ril_compiler_core::projection::TypeProjection::ArrayRemainder { prefix, suffix }],
            span,
        )
    }
}
