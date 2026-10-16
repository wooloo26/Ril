//! Pure static loop execution. Loop targets belong to one invocation; lexical
//! block environments and immutable value handles remain separate from control.
use super::*;

#[derive(Clone)]
pub(super) struct Frame {
    pub target: u64,
    pub expected: Option<TypeExpr>,
    pub unit: bool,
}
pub(super) struct Transfer {
    pub target: u64,
    pub exit: Exit,
}
pub(super) enum Exit {
    Next,
    Last(Box<StaticValue>),
}

enum Cursor {
    Array {
        values: StaticCollection<Vec<StaticValue>>,
        index: usize,
    },
    Map {
        values: StaticCollection<Vec<(StaticValue, StaticValue)>>,
        index: usize,
    },
    Range(Box<RangeCursor>),
}

struct RangeCursor {
    current: StaticValue,
    end: Option<StaticValue>,
    inclusive: bool,
    advance: bool,
    done: bool,
}

const _: () = assert!(std::mem::size_of::<Exit>() <= 2 * std::mem::size_of::<usize>());
const _: () = assert!(std::mem::size_of::<Cursor>() <= 64);
impl Cursor {
    fn next(&mut self, evaluator: &mut Evaluator) -> Result<Option<StaticValue>> {
        match self {
            Self::Array { values, index } => {
                let value = values
                    .get(*index)
                    .map(|value| evaluator.copy_static_value(value))
                    .transpose()?;
                if value.is_some() {
                    *index += 1;
                }
                Ok(value)
            }
            Self::Map { values, index } => {
                if let Some((key, value)) = values.get(*index) {
                    let key = evaluator.copy_static_value(key)?;
                    let value = evaluator.copy_static_value(value)?;
                    *index += 1;
                    Ok(Some(evaluator.tuple(vec![key, value])))
                } else {
                    Ok(None)
                }
            }
            Self::Range(cursor) => {
                let RangeCursor {
                    current,
                    end,
                    inclusive,
                    advance,
                    done,
                } = cursor.as_mut();
                if *done {
                    return Ok(None);
                }
                if *advance {
                    *current = evaluator.binary("+", current.clone(), integer_like(current, 1)?)?;
                }
                if let Some(end) = end {
                    let past = evaluator.binary(
                        if *inclusive { ">" } else { ">=" },
                        current.clone(),
                        end.clone(),
                    )?;
                    if past == StaticValue::Bool(true) {
                        *done = true;
                        return Ok(None);
                    }
                    if *inclusive && static_equal(current, end) {
                        *done = true;
                    }
                }
                *advance = true;
                Ok(Some(current.clone()))
            }
        }
    }
}
fn integer_like(value: &StaticValue, number: i128) -> Result<StaticValue> {
    Ok(match value {
        StaticValue::Integer(_) => StaticValue::Integer(number),
        StaticValue::TypedInteger(_, bits, signed) => {
            StaticValue::TypedInteger(number, *bits, *signed)
        }
        StaticValue::BigInteger(_) => StaticValue::BigInteger(number.into()),
        _ => {
            return Err(Failure::Diagnostic(
                "E0327",
                "static range endpoints require integer values".into(),
            ));
        }
    })
}

impl Evaluator {
    fn new_loop_frame(&mut self, expected: Option<&TypeExpr>, unit: bool) -> Result<Frame> {
        let target = self.next_loop_target;
        self.next_loop_target = target.checked_add(1).ok_or_else(|| {
            Failure::Unsupported("static loop target identities exhausted".into())
        })?;
        Ok(Frame {
            target,
            expected: expected.cloned(),
            unit,
        })
    }
    /// The condition/source is outside this loop's body target. The body alone
    /// installs it, so a transfer in an inner condition still targets its outer
    /// lexical loop. Every block entry allocates its own declaration environment.
    fn loop_body(
        &mut self,
        body: &Block,
        pattern: Option<(&Pattern, &StaticValue)>,
        frame: &Frame,
    ) -> Result<StaticValue> {
        let saved = self.capture_environment()?;
        self.loop_frames.push(frame.clone());
        let result = (|| {
            if let Some((pattern, value)) = pattern
                && !self.match_pattern(pattern, value)?
            {
                return Err(Failure::Diagnostic(
                    "E0345",
                    "static for pattern must be irrefutable".into(),
                ));
            }
            self.block_expected(body, false, None)
        })();
        self.loop_frames.pop();
        self.install_environment(saved);
        result
    }
    pub(super) fn loop_control(
        &mut self,
        operation: ControlOperation,
        value: Option<&Expr>,
    ) -> Result<StaticValue> {
        let frame = self.loop_frames.last().cloned().ok_or_else(|| {
            Failure::Diagnostic(
                "E0707",
                "loop control has no enclosing static loop body".into(),
            )
        })?;
        let exit = match operation {
            ControlOperation::Next => Exit::Next,
            ControlOperation::Last => {
                let value = value.map_or(Ok(StaticValue::Unit), |value| {
                    self.expression_expected(value, false, frame.expected.as_ref())
                })?;
                if frame.unit && value != StaticValue::Unit {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "while and for last values must be unit".into(),
                    ));
                }
                Exit::Last(Box::new(value))
            }
            _ => unreachable!("loop transfer operation"),
        };
        Err(Failure::Loop(Transfer {
            target: frame.target,
            exit,
        }))
    }
    pub(super) fn evaluate_loop(
        &mut self,
        body: &Block,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        let frame = self.new_loop_frame(expected, false)?;
        loop {
            self.budget.event(budget::Event::LoopIteration)?;
            match self.loop_body(body, None, &frame) {
                Ok(_) => {}
                Err(Failure::Loop(Transfer { target, exit })) if target == frame.target => {
                    match exit {
                        Exit::Next => {}
                        Exit::Last(value) => return Ok(*value),
                    }
                }
                Err(failure) => return Err(failure),
            }
        }
    }
    pub(super) fn evaluate_while(&mut self, condition: &Expr, body: &Block) -> Result<StaticValue> {
        let frame = self.new_loop_frame(None, true)?;
        loop {
            self.budget.event(budget::Event::LoopIteration)?;
            match self.expression(condition)? {
                StaticValue::Bool(false) => return Ok(StaticValue::Unit),
                StaticValue::Bool(true) => {}
                _ => {
                    return Err(Failure::Diagnostic(
                        "E0350",
                        "static while condition must be bool".into(),
                    ));
                }
            }
            match self.loop_body(body, None, &frame) {
                Ok(_) => {}
                Err(Failure::Loop(Transfer { target, exit })) if target == frame.target => {
                    match exit {
                        Exit::Next => {}
                        Exit::Last(_) => return Ok(StaticValue::Unit),
                    }
                }
                Err(failure) => return Err(failure),
            }
        }
    }
    fn for_cursor(&mut self, iterable: &Expr) -> Result<Cursor> {
        if let ExprKind::Range {
            start,
            end,
            inclusive,
        } = &iterable.kind
        {
            let context = start
                .as_deref()
                .and_then(|start| self.rigid_numeric_peer(start))
                .or_else(|| end.as_deref().and_then(|end| self.rigid_numeric_peer(end)));
            let start = start
                .as_deref()
                .map(|value| self.expression_expected(value, false, context.as_ref()))
                .transpose()?;
            let end = end
                .as_deref()
                .map(|value| self.expression_expected(value, false, context.as_ref()))
                .transpose()?;
            let current = match (start, &end) {
                (Some(start), _) => start,
                (None, Some(end)) => integer_like(end, 0)?,
                (None, None) => StaticValue::Integer(0),
            };
            integer_like(&current, 1)?;
            if let Some(end) = &end {
                integer_like(end, 1)?;
                self.binary("<=", current.clone(), end.clone())?;
            }
            return Ok(Cursor::Range(Box::new(RangeCursor {
                current,
                end,
                inclusive: *inclusive,
                advance: false,
                done: false,
            })));
        }
        match self.expression(iterable)? {
            StaticValue::Array(values) => Ok(Cursor::Array { values, index: 0 }),
            StaticValue::Map(values) => Ok(Cursor::Map { values, index: 0 }),
            _ => Err(Failure::Diagnostic(
                "E0355",
                "static for requires an array, map or integer range".into(),
            )),
        }
    }
    pub(super) fn evaluate_for(
        &mut self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &Block,
    ) -> Result<StaticValue> {
        let mut cursor = self.for_cursor(iterable)?;
        let frame = self.new_loop_frame(None, true)?;
        loop {
            self.budget.event(budget::Event::LoopIteration)?;
            let Some(value) = cursor.next(self)? else {
                return Ok(StaticValue::Unit);
            };
            match self.loop_body(body, Some((pattern, &value)), &frame) {
                Ok(_) => {}
                Err(Failure::Loop(Transfer { target, exit })) if target == frame.target => {
                    match exit {
                        Exit::Next => {}
                        Exit::Last(_) => return Ok(StaticValue::Unit),
                    }
                }
                Err(failure) => return Err(failure),
            }
        }
    }
}
