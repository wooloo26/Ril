//! Sequence matching uses actual shape facts for control, while Source
//! dimensions remain the responsibility of the original type projection.
use super::*;

pub(super) fn sequence_rest(patterns: &[Pattern]) -> Option<usize> {
    patterns
        .iter()
        .position(|pattern| matches!(pattern.kind, PatternKind::Rest(_)))
}

impl Checker {
    pub(in crate::sema::checker) fn binding_pattern_match(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        frame: &mut Frame,
    ) -> Option<bool> {
        self.binding_pattern_match_depth(pattern, value, frame, 0)
    }

    fn binding_pattern_match_depth(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        frame: &mut Frame,
        depth: usize,
    ) -> Option<bool> {
        let edges = match &pattern.kind {
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items) => items.len(),
            PatternKind::Record { fields, .. } => fields.len(),
            PatternKind::Constructor { arguments, .. } => arguments.len(),
            PatternKind::Literal(Literal::Integer(text)) => text.len().div_ceil(32),
            _ => 0,
        };
        if depth >= 128 || !self.application_effect.admit(2 + edges) {
            self.unsupported(
                pattern.span,
                "pattern decision exceeds its shared work bound",
            );
            return None;
        }
        match &pattern.kind {
            PatternKind::Name(_) | PatternKind::Wildcard | PatternKind::Rest(_) => Some(true),
            PatternKind::Mode { pattern, .. } => {
                self.binding_pattern_match_depth(pattern, value, frame, depth + 1)
            }
            PatternKind::Literal(literal) => {
                let expected = match literal {
                    Literal::Bool(value) => Some(Constant::Bool(*value)),
                    Literal::Unit => Some(Constant::Unit),
                    Literal::Integer(text) => integer_literal(text).map(Constant::Integer),
                    _ => None,
                };
                value
                    .constant
                    .as_ref()
                    .zip(expected.as_ref())
                    .map(|(actual, expected)| actual == expected)
            }
            PatternKind::Tuple(parts) => {
                let items = match self.expanded(&value.ty, &mut BTreeSet::new()) {
                    Ty::Tuple(items) => items,
                    Ty::Unit => Vec::new(),
                    _ => return Some(false),
                };
                let rest = sequence_rest(parts);
                let required = parts.len() - usize::from(rest.is_some());
                if items.len() < required || (rest.is_none() && items.len() != required) {
                    return Some(false);
                }
                let mut matched = Some(true);
                for (index, part) in parts.iter().enumerate() {
                    if matches!(part.kind, PatternKind::Rest(_)) {
                        continue;
                    }
                    let coordinate = if rest.is_some_and(|rest| index > rest) {
                        items.len() - (parts.len() - index)
                    } else {
                        index
                    };
                    let child = self.project(
                        value,
                        Slot::Tuple(coordinate as u32),
                        part.span,
                        frame,
                        true,
                    );
                    matched = and_match(
                        matched,
                        self.binding_pattern_match_depth(part, &child, frame, depth + 1),
                    );
                    if matched == Some(false) {
                        break;
                    }
                }
                matched
            }
            PatternKind::Array(parts) => {
                if !matches!(self.expanded(&value.ty, &mut BTreeSet::new()), Ty::Array(_)) {
                    return Some(false);
                }
                let rest = sequence_rest(parts);
                let required = parts.len() - usize::from(rest.is_some());
                let length = self.known_array_length(value);
                let mut matched = length.map(|length| {
                    if rest.is_some() {
                        length >= required as u64
                    } else {
                        length == required as u64
                    }
                });
                if matched == Some(false) {
                    return matched;
                }
                if required == 0 && rest.is_some() {
                    return Some(true);
                }
                for (index, part) in parts.iter().enumerate() {
                    if matches!(part.kind, PatternKind::Rest(_)) {
                        continue;
                    }
                    let coordinate = if rest.is_some_and(|rest| index > rest) {
                        length
                            .and_then(|length| length.checked_sub((parts.len() - index) as u64))
                            .and_then(|index| i64::try_from(index).ok())
                    } else {
                        i64::try_from(index).ok()
                    };
                    let child = self.project(
                        value,
                        coordinate.map(Slot::Index).unwrap_or(Slot::AnyIndex),
                        part.span,
                        frame,
                        true,
                    );
                    matched = and_match(
                        matched,
                        self.binding_pattern_match_depth(part, &child, frame, depth + 1),
                    );
                    if matched == Some(false) {
                        break;
                    }
                }
                matched
            }
            PatternKind::Record { fields, .. } => {
                if !matches!(
                    self.expanded(&value.ty, &mut BTreeSet::new()),
                    Ty::Record(_) | Ty::OpenRecord { .. }
                ) {
                    return Some(false);
                }
                let mut matched = Some(true);
                for field in fields {
                    let child = self.project(
                        value,
                        Slot::Field(field.name.clone()),
                        field.span,
                        frame,
                        true,
                    );
                    matched = and_match(
                        matched,
                        self.binding_pattern_match_depth(&field.pattern, &child, frame, depth + 1),
                    );
                    if matched == Some(false) {
                        break;
                    }
                }
                matched
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                let tag = self.resolved_pattern_tag(path, value, frame)?;
                let matched = self.constructor_tag_match(value, &tag);
                if matched == Some(false) || arguments.is_empty() {
                    return matched;
                }
                let payload = match tag.as_str() {
                    "Some" => value.option_payload.as_deref(),
                    "Ok" => value.result_success.as_deref().or_else(|| {
                        (value.result_tag == Some(true))
                            .then_some(value.result_payload.as_deref())
                            .flatten()
                    }),
                    "Err" => value.result_error.as_deref().or_else(|| {
                        (value.result_tag == Some(false))
                            .then_some(value.result_payload.as_deref())
                            .flatten()
                    }),
                    _ => value.variant_witness(&tag),
                }?;
                let payload = payload.clone();
                let nested = constructor_payload_pattern(arguments, pattern.span);
                and_match(
                    matched,
                    self.binding_pattern_match_depth(&nested, &payload, frame, depth + 1),
                )
            }
            PatternKind::Alternative(parts) => {
                let mut matched = Some(false);
                for part in parts {
                    matched = or_match(
                        matched,
                        self.binding_pattern_match_depth(part, value, frame, depth + 1),
                    );
                    if matched == Some(true) {
                        break;
                    }
                }
                matched
            }
            PatternKind::Value(expression) => {
                let ExprKind::Range {
                    start,
                    end,
                    inclusive,
                } = &expression.kind
                else {
                    return None;
                };
                let Constant::Integer(actual) = value.constant.as_ref()? else {
                    return None;
                };
                let lower = match start.as_deref() {
                    Some(value) => Some(pattern_integer(value)?),
                    None => None,
                };
                let upper = match end.as_deref() {
                    Some(value) => Some(pattern_integer(value)?),
                    None => None,
                };
                Some(
                    lower.is_none_or(|lower| *actual >= lower)
                        && upper.is_none_or(|upper| {
                            if *inclusive {
                                *actual <= upper
                            } else {
                                *actual < upper
                            }
                        }),
                )
            }
            _ => None,
        }
    }
}

fn integer_literal(text: &str) -> Option<i128> {
    let text = text.replace('_', "");
    let text = [
        "bigint", "int", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64",
    ]
    .iter()
    .find_map(|suffix| text.strip_suffix(suffix))
    .unwrap_or(&text);
    let (digits, radix) =
        if let Some(text) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
            (text, 16)
        } else if let Some(text) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O")) {
            (text, 8)
        } else if let Some(text) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
            (text, 2)
        } else {
            (text, 10)
        };
    i128::from_str_radix(digits, radix).ok()
}

pub(super) fn array_patterns_exhaustive(patterns: &[&Pattern]) -> bool {
    let universal = |items: &[Pattern]| {
        items
            .iter()
            .all(|item| matches!(item.kind, PatternKind::Rest(_)) || structurally_irrefutable(item))
    };
    let mut exact = BTreeSet::new();
    let mut minimum = None;
    for pattern in patterns {
        let PatternKind::Array(items) = &pattern.kind else {
            continue;
        };
        if !universal(items) {
            continue;
        }
        if sequence_rest(items).is_some() {
            minimum = Some(minimum.map_or(items.len() - 1, |previous: usize| {
                previous.min(items.len() - 1)
            }));
        } else {
            exact.insert(items.len());
        }
    }
    let Some(minimum) = minimum else {
        return false;
    };
    exact.len() >= minimum && exact.into_iter().take(minimum).eq(0..minimum)
}

impl Checker {
    pub(in crate::sema::checker) fn array_value_patterns_exhaustive(
        &self,
        value: &Value,
        patterns: &[Pattern],
    ) -> bool {
        if !matches!(self.expanded(&value.ty, &mut BTreeSet::new()), Ty::Array(_)) {
            return false;
        }
        let Some(length) = self.known_array_length(value) else {
            return false;
        };
        patterns.iter().flat_map(flat_patterns).any(|pattern| {
            let PatternKind::Array(items) = &pattern.kind else {
                return false;
            };
            let rest = sequence_rest(items);
            let required = (items.len() - usize::from(rest.is_some())) as u64;
            (if rest.is_some() {
                length >= required
            } else {
                length == required
            }) && items.iter().all(|item| {
                matches!(item.kind, PatternKind::Rest(_)) || structurally_irrefutable(item)
            })
        })
    }
}

pub(super) fn sequence_subsumes(first: &[Pattern], second: &[Pattern]) -> bool {
    let first_rest = sequence_rest(first);
    let second_rest = sequence_rest(second);
    let first_required = first.len() - usize::from(first_rest.is_some());
    let second_required = second.len() - usize::from(second_rest.is_some());
    if first_rest.is_none() {
        return second_rest.is_none()
            && first.len() == second.len()
            && first
                .iter()
                .zip(second)
                .all(|(first, second)| pattern_subsumes(first, second));
    }
    if first_required > second_required {
        return false;
    }
    let prefix = first_rest.unwrap();
    let suffix = first.len() - prefix - 1;
    if let Some(second_rest) = second_rest {
        let second_suffix = second.len() - second_rest - 1;
        if prefix > second_rest || suffix > second_suffix {
            return first.iter().all(|item| {
                matches!(item.kind, PatternKind::Rest(_)) || structurally_irrefutable(item)
            });
        }
    }
    first[..prefix]
        .iter()
        .zip(&second[..prefix])
        .all(|(first, second)| pattern_subsumes(first, second))
        && first[first.len() - suffix..]
            .iter()
            .zip(&second[second.len() - suffix..])
            .all(|(first, second)| pattern_subsumes(first, second))
}
