//! Bounded evaluation of retained numeric terms. This never edits an emission.
use super::*;
use crate::numeric_literals::{ExactLiteral, ParseLimit};
use num_traits::ToPrimitive;

pub(super) fn charge(work: &mut usize, count: usize) -> Result<(), SourceTypesError> {
    *work = work
        .checked_sub(count)
        .ok_or(SourceTypesError::BudgetExceeded)?;
    Ok(())
}

pub(crate) fn number_type(ty: &Ty) -> Option<NumberType> {
    [
        NumberType::Int,
        NumberType::I8,
        NumberType::I16,
        NumberType::I32,
        NumberType::I64,
        NumberType::U8,
        NumberType::U16,
        NumberType::U32,
        NumberType::U64,
        NumberType::BigInt,
        NumberType::F32,
        NumberType::F64,
    ]
    .into_iter()
    .find(|number| selected_ty(*number) == *ty)
}

pub(crate) fn arithmetic_constant(
    selected: NumberType,
    constant: Option<Constant>,
    layout: TargetLayout,
) -> Option<Constant> {
    let Some(Constant::Integer(number)) = constant else {
        return constant;
    };
    if matches!(selected, NumberType::F32 | NumberType::F64) {
        return None;
    }
    let text = number.to_string();
    let (text, negative) = text
        .strip_prefix('-')
        .map_or((text.as_str(), false), |text| (text, true));
    ExactLiteral::integer(text, negative, ParseLimit { max_bytes: 128 })
        .ok()?
        .select(selected, layout)
        .ok()?;
    Some(Constant::Integer(number))
}

pub(crate) fn encoded_constant(encoded: &EncodedNumber) -> Option<Constant> {
    match encoded {
        EncodedNumber::Integer { value, .. } => Some(Constant::Integer(*value)),
        EncodedNumber::BigInteger(value) => value.to_i128().map(Constant::Integer),
        EncodedNumber::Float(_) => None,
    }
}

pub(super) fn clone_resolution(
    value: &NumericResolution,
    work: &mut usize,
) -> Result<NumericResolution, SourceTypesError> {
    charge(
        work,
        1 + value.dependencies.uses.len() + value.dependencies.selections.len(),
    )?;
    if let Some(EncodedNumber::BigInteger(value)) = &value.encoded {
        charge(work, value.bits().div_ceil(8) as usize)?;
    }
    Ok(value.clone())
}

pub(crate) fn evaluate(
    holes: &[NumericHole],
    uses: &[NumericUse],
    selections: &[NumericSelection],
    root: NumericHoleId,
    selected: NumberType,
    layout: TargetLayout,
    work: &mut usize,
) -> Result<NumericResolution, SourceTypesError> {
    evaluate_cached(
        NumericInputs {
            holes,
            uses,
            selections,
            layout,
        },
        root,
        selected,
        work,
        &mut BTreeMap::new(),
    )
}

#[derive(Clone, Copy)]
pub(crate) struct NumericInputs<'a> {
    pub(crate) holes: &'a [NumericHole],
    pub(crate) uses: &'a [NumericUse],
    pub(crate) selections: &'a [NumericSelection],
    pub(crate) layout: TargetLayout,
}

pub(crate) fn evaluate_cached(
    input: NumericInputs<'_>,
    root: NumericHoleId,
    selected: NumberType,
    work: &mut usize,
    memo: &mut BTreeMap<NumericHoleId, NumericResolution>,
) -> Result<NumericResolution, SourceTypesError> {
    Solver {
        holes: input.holes,
        uses: input.uses,
        selections: input.selections,
        selected,
        layout: input.layout,
        active: BTreeSet::new(),
        memo,
        work,
    }
    .hole(root, 0)
}

struct Solver<'a, 'w> {
    holes: &'a [NumericHole],
    uses: &'a [NumericUse],
    selections: &'a [NumericSelection],
    selected: NumberType,
    layout: TargetLayout,
    active: BTreeSet<NumericHoleId>,
    memo: &'w mut BTreeMap<NumericHoleId, NumericResolution>,
    work: &'w mut usize,
}

impl Solver<'_, '_> {
    fn operand(
        &mut self,
        operand: &NumericOperand,
        depth: usize,
    ) -> Result<NumericResolution, SourceTypesError> {
        charge(self.work, 1)?;
        if let Some(hole) = operand.hole {
            return self.hole(hole, depth + 1);
        }
        if number_type(&operand.ty) != Some(self.selected) {
            return Err(SourceTypesError::Unresolved);
        }
        charge(
            self.work,
            1 + operand.dependencies.uses.len() + operand.dependencies.selections.len(),
        )?;
        clone_resolution(
            &NumericResolution {
                number_type: self.selected,
                constant: operand.constant.clone(),
                encoded: None,
                dependencies: operand.dependencies.clone(),
            },
            self.work,
        )
    }

    fn hole(
        &mut self,
        id: NumericHoleId,
        depth: usize,
    ) -> Result<NumericResolution, SourceTypesError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        if let Some(cached) = self.memo.get(&id) {
            if cached.number_type != self.selected {
                return Err(SourceTypesError::Unresolved);
            }
            return clone_resolution(cached, self.work);
        }
        if !self.active.insert(id) {
            return Err(SourceTypesError::Unresolved);
        }
        let hole = self
            .holes
            .get(id.0 as usize)
            .filter(|hole| hole.id == id)
            .ok_or(SourceTypesError::MissingNode)?;
        if hole.domain == NumericDomain::FloatOnly
            && !matches!(self.selected, NumberType::F32 | NumberType::F64)
        {
            return Err(SourceTypesError::Unresolved);
        }
        let mut result = NumericResolution {
            number_type: self.selected,
            constant: None,
            encoded: None,
            dependencies: NumericDependencies::default(),
        };
        match &hole.term {
            NumericTerm::Literal(use_id) => {
                let use_ = self
                    .uses
                    .get(use_id.0 as usize)
                    .filter(|use_| use_.id == *use_id && use_.hole == id)
                    .ok_or(SourceTypesError::MissingNode)?;
                let cost = use_.exact.magnitude().map_or_else(
                    || use_.exact.decimal_magnitude().map_or(0, str::len),
                    |n| n.bits().div_ceil(8) as usize,
                );
                charge(self.work, cost + 1)?;
                let encoded = use_
                    .exact
                    .select(self.selected, self.layout)
                    .map_err(|_| SourceTypesError::Unresolved)?;
                let selection_id = use_.selection.ok_or(SourceTypesError::MissingNode)?;
                let selection = self
                    .selections
                    .get(selection_id.0 as usize)
                    .filter(|selection| {
                        selection.id == selection_id && selection.literal == *use_id
                    })
                    .ok_or(SourceTypesError::MissingNode)?;
                if selection.site != use_.site
                    || selection.birth != use_.birth
                    || selection.ty != self.selected
                    || selection.layout != self.layout
                    || selection.encoded != encoded
                {
                    return Err(SourceTypesError::Unresolved);
                }
                result.constant = encoded_constant(&encoded);
                result.encoded = Some(encoded);
                result.dependencies.uses.insert(*use_id);
                result.dependencies.selections.insert(selection.id);
            }
            NumericTerm::Unary { operator, operand } => {
                charge(self.work, operator.len())?;
                if operator != "-" {
                    return Err(SourceTypesError::Unresolved);
                }
                let operand = self.operand(operand, depth)?;
                result.dependencies = operand.dependencies;
                result.constant = match operand.constant {
                    Some(Constant::Integer(n)) => n.checked_neg().map(Constant::Integer),
                    _ => None,
                };
            }
            NumericTerm::Binary {
                operator,
                left,
                right,
            } => {
                charge(self.work, operator.len())?;
                if !matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") {
                    return Err(SourceTypesError::Unresolved);
                }
                let left = self.operand(left, depth)?;
                let right = self.operand(right, depth)?;
                charge(
                    self.work,
                    left.dependencies.uses.len()
                        + left.dependencies.selections.len()
                        + right.dependencies.uses.len()
                        + right.dependencies.selections.len(),
                )?;
                result.dependencies.include(&left.dependencies);
                result.dependencies.include(&right.dependencies);
                result.constant = match (&left.constant, &right.constant, operator.as_str()) {
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "+") => {
                        a.checked_add(*b).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "-") => {
                        a.checked_sub(*b).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "*") => {
                        a.checked_mul(*b).map(Constant::Integer)
                    }
                    _ => None,
                };
            }
            NumericTerm::Join(_) => return Err(SourceTypesError::Unresolved),
        }
        result.constant = arithmetic_constant(self.selected, result.constant, self.layout);
        self.active.remove(&id);
        let retained = clone_resolution(&result, self.work)?;
        charge(self.work, 1)?;
        self.memo.insert(id, retained);
        Ok(result)
    }
}
