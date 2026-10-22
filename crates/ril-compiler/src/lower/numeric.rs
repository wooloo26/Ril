//! Numeric emission uses verified original sites in the selected invocation view.
use super::*;
use crate::sema::{
    numeric_selection::{NumericSelection, NumericSite, NumericUse},
    source_types::WorkLimit,
};
use ril_compiler_core::ids::{ExprId, NumericSelectionId, PatternId};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum NumericNode {
    Expression(ExprId),
    Pattern(PatternId),
}

impl From<NumericSite> for NumericNode {
    fn from(site: NumericSite) -> Self {
        match site {
            NumericSite::Expression { literal, .. } => Self::Expression(literal),
            NumericSite::Pattern(id) => Self::Pattern(id),
        }
    }
}

/// A lowering-local index, shared by all actual specialization views. It adds
/// no semantic facts and never refreshes the work allowance in a nested view.
pub(super) struct NumericIndex {
    known: BTreeSet<(Option<CallableOwner>, NumericNode)>,
    work: RefCell<WorkLimit>,
}

#[derive(Clone, Copy)]
enum Choice {
    Unique(NumericSelectionId),
    Conflict,
}

pub(super) struct NumericView {
    selected: BTreeMap<(Option<CallableOwner>, NumericSite), Choice>,
}

fn charge(work: &mut WorkLimit, units: usize) -> Result<(), NotImplemented> {
    work.charge(units)
        .map_err(|error| unsupported(format!("numeric lowering work: {error}")))
}

fn map_work(work: &mut WorkLimit, len: usize) -> Result<(), NotImplemented> {
    charge(work, 1 + len.checked_ilog2().unwrap_or(0) as usize)
}

fn encoding_work(
    work: &mut WorkLimit,
    encoded: &crate::numeric_literals::EncodedNumber,
) -> Result<(), NotImplemented> {
    let units = match encoded {
        crate::numeric_literals::EncodedNumber::BigInteger(value) => usize::try_from(value.bits())
            .ok()
            .and_then(|bits| bits.checked_add(2))
            .ok_or_else(|| {
                unsupported("numeric encoding work exceeds the implementation domain")
            })?,
        _ => 1,
    };
    charge(work, units)
}

impl NumericIndex {
    pub(super) fn new(uses: &[NumericUse], mut work: WorkLimit) -> Result<Self, NotImplemented> {
        charge(&mut work, uses.len())?;
        let mut known = BTreeSet::new();
        for usage in uses {
            map_work(&mut work, known.len())?;
            known.insert((usage.birth.context.owner, usage.site.into()));
        }
        Ok(Self {
            known,
            work: RefCell::new(work),
        })
    }

    pub(super) fn view(
        &self,
        selected: &[NumericSelection],
        uses: &[NumericUse],
        original: &[NumericSelection],
        layout: TargetLayout,
    ) -> Result<NumericView, NotImplemented> {
        let mut work = self.work.borrow_mut();
        charge(&mut work, selected.len())?;
        let mut view = NumericView {
            selected: BTreeMap::new(),
        };
        for fact in selected {
            charge(&mut work, 2)?;
            let usage = uses
                .get(fact.literal.0 as usize)
                .filter(|usage| {
                    usage.id == fact.literal
                        && usage.selection == Some(fact.id)
                        && usage.site == fact.site
                        && usage.birth == fact.birth
                })
                .ok_or_else(|| {
                    unsupported("numeric selection has no matching actual literal birth")
                })?;
            let original_fact = original.get(fact.id.0 as usize).ok_or_else(|| {
                unsupported("numeric lowering selection is outside its original arena")
            })?;
            encoding_work(&mut work, &fact.encoded)?;
            encoding_work(&mut work, &original_fact.encoded)?;
            if fact.layout != layout || original_fact != fact {
                return Err(unsupported(
                    "numeric lowering selection is not the verified target receipt",
                ));
            }
            if let NumericSite::Expression {
                immediate_minus, ..
            } = fact.site
                && usage.exact.is_negative() != immediate_minus.is_some()
            {
                return Err(unsupported(
                    "numeric literal sign must be consumed at its original unary boundary",
                ));
            }
            map_work(&mut work, view.selected.len())?;
            match view.selected.entry((fact.birth.context.owner, fact.site)) {
                Entry::Vacant(entry) => {
                    entry.insert(Choice::Unique(fact.id));
                }
                Entry::Occupied(mut entry) => {
                    if let Choice::Unique(previous) = *entry.get() {
                        charge(&mut work, 1)?;
                        let previous = original
                            .get(previous.0 as usize)
                            .ok_or_else(|| unsupported("numeric view lost its original receipt"))?;
                        encoding_work(&mut work, &previous.encoded)?;
                        encoding_work(&mut work, &fact.encoded)?;
                        if previous.ty != fact.ty || previous.encoded != fact.encoded {
                            entry.insert(Choice::Conflict);
                        }
                    }
                }
            }
        }
        Ok(view)
    }

    fn selection(
        &self,
        view: &NumericView,
        owner: Option<CallableOwner>,
        site: NumericSite,
    ) -> Result<Option<NumericSelectionId>, NotImplemented> {
        let mut work = self.work.borrow_mut();
        map_work(&mut work, view.selected.len())?;
        match view.selected.get(&(owner, site)) {
            Some(Choice::Unique(id)) => Ok(Some(*id)),
            Some(Choice::Conflict) => Err(unsupported(
                "one emitted numeric literal has incompatible actual selections",
            )),
            None => {
                map_work(&mut work, self.known.len())?;
                if self.known.contains(&(owner, site.into())) {
                    Err(unsupported(
                        "numeric literal lacks a selection in its actual invocation view",
                    ))
                } else {
                    Ok(None)
                }
            }
        }
    }
}

impl Lower<'_> {
    pub(super) fn selected_numeric_literal(
        &self,
        site: NumericSite,
    ) -> Result<Option<ir::Literal>, NotImplemented> {
        let Some(id) =
            self.numeric_index
                .selection(&self.numeric_view, self.callable_owner, site)?
        else {
            return Ok(None);
        };
        let mut work = self.numeric_index.work.borrow_mut();
        charge(&mut work, 1)?;
        let selection = self
            .all_facts
            .numeric_selections
            .get(id.0 as usize)
            .filter(|selection| selection.id == id)
            .ok_or_else(|| unsupported("numeric view lost its original selection"))?;
        encoding_work(&mut work, &selection.encoded)?;
        Ok(Some(match &selection.encoded {
            crate::numeric_literals::EncodedNumber::Integer {
                value,
                bits,
                signed,
                ..
            } => ir::Literal::Integer {
                value: *value,
                bits: *bits,
                signed: *signed,
            },
            crate::numeric_literals::EncodedNumber::BigInteger(value) => {
                ir::Literal::BigInteger(value.to_string())
            }
            crate::numeric_literals::EncodedNumber::Float(value) => ir::Literal::Float {
                value: value.as_f64(),
                bits: match value.format() {
                    crate::numeric_literals::FloatFormat::F32 => 32,
                    crate::numeric_literals::FloatFormat::F64 => 64,
                },
            },
        }))
    }

    pub(super) fn literal(
        &self,
        literal: &ast::Literal,
        site: Option<NumericSite>,
    ) -> Result<ir::Literal, NotImplemented> {
        if matches!(literal, ast::Literal::Integer(_) | ast::Literal::Float(_))
            && let Some(site) = site
            && let Some(selected) = self.selected_numeric_literal(site)?
        {
            return Ok(selected);
        }
        Ok(match literal {
            ast::Literal::Unit => ir::Literal::Unit,
            ast::Literal::Bool(value) => ir::Literal::Bool(*value),
            ast::Literal::Integer(text) => {
                if let Some(digits) = text.strip_suffix("bigint") {
                    ir::Literal::BigInteger(digits.replace('_', ""))
                } else {
                    self.integer(text)?
                }
            }
            ast::Literal::Float(text) => {
                match crate::static_eval::committed_float::decode(text) {
                    Ok(Some(committed)) => {
                        return Ok(ir::Literal::Float {
                            value: committed.value(),
                            bits: committed.width,
                        });
                    }
                    Err(()) => {
                        return Err(unsupported(
                            "invalid committed floating-point literal witness",
                        ));
                    }
                    Ok(None) => {}
                }
                let (text, bits) = if let Some(value) = text.strip_suffix("f32") {
                    (value, 32)
                } else {
                    let bits = 64;
                    (text.strip_suffix("f64").unwrap_or(text), bits)
                };
                ir::Literal::Float {
                    value: if bits == 32 {
                        f64::from(
                            text.replace('_', "")
                                .parse::<f32>()
                                .map_err(|_| unsupported("invalid floating literal"))?,
                        )
                    } else {
                        text.replace('_', "")
                            .parse::<f64>()
                            .map_err(|_| unsupported("invalid floating literal"))?
                    },
                    bits,
                }
            }
            ast::Literal::String(text) => {
                ir::Literal::String(decode_text(&text[1..text.len() - 1])?)
            }
            ast::Literal::RawString(text) => ir::Literal::String(text[1..text.len() - 1].into()),
            ast::Literal::Bytes(text) => {
                ir::Literal::Bytes(decode_bytes(&text[2..text.len() - 1])?)
            }
        })
    }
}

/// Compare emitted code shapes through the verified receipt while leaving the
/// original observation's unresolved numeric identity intact.
pub(super) fn resolved_type(
    facts: &crate::sema::SemanticFacts,
    raw: &crate::sema::model::Ty,
) -> Result<crate::sema::model::Ty, NotImplemented> {
    use crate::sema::numeric_selection::{NumericHoleState, selected_ty};
    let crate::sema::model::Ty::NumericHole(id) = raw else {
        return Ok(raw.clone());
    };
    let hole = facts
        .numeric_holes
        .get(id.0 as usize)
        .filter(|hole| hole.id == *id)
        .ok_or_else(|| unsupported("emitted numeric shape has no original producer"))?;
    let NumericHoleState::Committed { resolution, .. } = &hole.state else {
        return Err(unsupported(
            "emitted numeric shape has no committed resolution",
        ));
    };
    Ok(selected_ty(resolution.number_type))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        numeric_literals::{ExactLiteral, NumberType, ParseLimit},
        sema::{
            application_effect::OccurrenceIdentity, copy_templates::InstanceId,
            effect_identity::InvocationContext, facts::ScopeId, numeric_selection::NumericBirth,
        },
    };
    use ril_compiler_core::{
        diagnostic::CauseId,
        ids::{ActivationEpochId, NumericHoleId, NumericUseId},
        source::FileId,
    };

    fn site(id: u32) -> NumericSite {
        NumericSite::Expression {
            literal: ExprId(id),
            immediate_minus: None,
        }
    }

    fn receipts(inputs: &[(NumericSite, NumberType)]) -> (Vec<NumericUse>, Vec<NumericSelection>) {
        let mut uses = Vec::new();
        let mut selections = Vec::new();
        for (index, (site, ty)) in inputs.iter().copied().enumerate() {
            let id = index as u32;
            let (source, negative) = match site {
                NumericSite::Expression {
                    literal,
                    immediate_minus,
                } => (
                    immediate_minus.unwrap_or(literal),
                    immediate_minus.is_some(),
                ),
                NumericSite::Pattern(_) => (ExprId(100), false),
            };
            let exact = ExactLiteral::integer("1", negative, ParseLimit { max_bytes: 8 }).unwrap();
            let birth = NumericBirth {
                occurrence: OccurrenceIdentity {
                    source,
                    activation: ActivationEpochId(id),
                },
                scope: ScopeId(0),
                context: InvocationContext {
                    invocation: Some(InstanceId(id)),
                    owner: Some(CallableOwner::Global),
                    closure: None,
                    closure_invocation: None,
                    budget_validation: false,
                    default_use: None,
                },
                allocation_epoch: 0,
            };
            let span = Span {
                file: FileId(0),
                start: 0,
                end: 1,
            };
            let cause = CauseId(0);
            uses.push(NumericUse {
                id: NumericUseId(id),
                hole: NumericHoleId(id),
                selection: Some(NumericSelectionId(id)),
                site,
                birth,
                exact: exact.clone(),
                span,
                cause,
            });
            selections.push(NumericSelection {
                id: NumericSelectionId(id),
                literal: NumericUseId(id),
                site,
                birth,
                span,
                ty,
                layout: TargetLayout::POINTER64,
                encoded: exact.select(ty, TargetLayout::POINTER64).unwrap(),
                cause,
            });
        }
        (uses, selections)
    }

    #[test]
    fn numeric_views_merge_equal_receipts_and_preserve_conflicts_until_query() {
        let (uses, selections) = receipts(&[
            (site(1), NumberType::Int),
            (site(1), NumberType::Int),
            (site(1), NumberType::F64),
            (site(2), NumberType::Int),
        ]);
        let index = NumericIndex::new(&uses, WorkLimit::new(1_000)).unwrap();
        let equal = index
            .view(
                &selections[..2],
                &uses,
                &selections,
                TargetLayout::POINTER64,
            )
            .unwrap();
        assert_eq!(
            index
                .selection(&equal, Some(CallableOwner::Global), site(1))
                .unwrap(),
            Some(NumericSelectionId(0))
        );
        let conflicted = index
            .view(&selections, &uses, &selections, TargetLayout::POINTER64)
            .unwrap();
        assert!(
            index
                .selection(&conflicted, Some(CallableOwner::Global), site(1))
                .is_err()
        );
        assert_eq!(
            index
                .selection(&conflicted, Some(CallableOwner::Global), site(2))
                .unwrap(),
            Some(NumericSelectionId(3))
        );
    }

    #[test]
    fn numeric_view_missing_receipts_keep_sign_and_pattern_node_identity() {
        let signed = NumericSite::Expression {
            literal: ExprId(1),
            immediate_minus: Some(ExprId(2)),
        };
        let (uses, selections) = receipts(&[
            (signed, NumberType::Int),
            (NumericSite::Pattern(PatternId(1)), NumberType::Int),
        ]);
        let index = NumericIndex::new(&uses, WorkLimit::new(1_000)).unwrap();
        let absent = index
            .view(&[], &uses, &selections, TargetLayout::POINTER64)
            .unwrap();
        assert!(
            index
                .selection(&absent, Some(CallableOwner::Global), signed)
                .is_err()
        );
        assert!(
            index
                .selection(&absent, Some(CallableOwner::Global), site(1))
                .is_err()
        );
        assert_eq!(
            index
                .selection(&absent, Some(CallableOwner::Global), site(3))
                .unwrap(),
            None
        );
        assert_eq!(index.selection(&absent, None, site(1)).unwrap(), None);
        let actual = index
            .view(&selections, &uses, &selections, TargetLayout::POINTER64)
            .unwrap();
        assert_eq!(
            index
                .selection(&actual, Some(CallableOwner::Global), signed)
                .unwrap(),
            Some(NumericSelectionId(0))
        );
        assert_eq!(
            index
                .selection(
                    &actual,
                    Some(CallableOwner::Global),
                    NumericSite::Pattern(PatternId(1))
                )
                .unwrap(),
            Some(NumericSelectionId(1))
        );
        assert!(
            index
                .selection(&actual, Some(CallableOwner::Global), site(1))
                .is_err()
        );
    }

    #[test]
    fn numeric_view_rejects_a_broken_typed_receipt_reference() {
        let (mut uses, selections) = receipts(&[(site(1), NumberType::Int)]);
        let index = NumericIndex::new(&uses, WorkLimit::new(1_000)).unwrap();
        uses[0].selection = None;
        assert!(
            index
                .view(&selections, &uses, &selections, TargetLayout::POINTER64)
                .is_err()
        );
    }

    #[test]
    fn numeric_views_share_one_allowance_and_reject_zero_work() {
        let (uses, selections) = receipts(&[(site(1), NumberType::Int)]);
        assert!(NumericIndex::new(&uses, WorkLimit::new(0)).is_err());
        let exhausted = NumericIndex::new(&uses, WorkLimit::new(2)).unwrap();
        assert!(
            exhausted
                .view(&selections, &uses, &selections, TargetLayout::POINTER64)
                .is_err()
        );
        let empty = NumericIndex::new(&[], WorkLimit::new(0)).unwrap();
        let empty_view = empty.view(&[], &[], &[], TargetLayout::POINTER64).unwrap();
        assert!(empty.selection(&empty_view, None, site(1)).is_err());
    }
}
