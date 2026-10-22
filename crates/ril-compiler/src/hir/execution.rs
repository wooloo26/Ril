//! Control cursors over original HIR identities. These plans contain no value,
//! heap, Source view or evaluation occurrence. A host advances a child only
//! after its actual evaluation completes; suspension keeps the cursor pending.
//! Taking a reduction transfers the original operation to the host. It does
//! not establish normal completion, and may itself produce a suspension.
use super::{
    application::{ApplicationKind, EvaluationRole},
    blocks::{BlockIndex, BlockIndexError},
    nodes::{self as hir, HirProgram},
};
use ril_compiler_core::ids::{BlockAnchor, ExprId, PatternId, StmtId};
use std::sync::Arc;

const MAX_DEPTH: usize = 128;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ExecutionError {
    #[error("HIR execution cursor work budget exhausted")]
    Budget,
    #[error("HIR execution cursor depth exceeded")]
    Depth,
    #[error("HIR execution cursor node is absent: {0:?}")]
    MissingNode(hir::NodeId),
    #[error("HIR node is not an ordinary application: {0:?}")]
    NotApplication(ExprId),
    #[error("HIR execution cursor does not support {kind} at {root:?}")]
    Unsupported { root: ExprId, kind: &'static str },
    #[error("HIR application is invalid: {0}")]
    InvalidApplication(&'static str),
    #[error("HIR execution cursor completed a different or out-of-order child")]
    UnexpectedChild,
    #[error("HIR execution cursor received a different guard or decision kind")]
    UnexpectedGuard,
    #[error("HIR execution cursor is not ready for this reduction")]
    UnexpectedReduction,
    #[error("HIR execution cursor reduction was already consumed")]
    AlreadyReduced,
    #[error("HIR block index differs from the original block at {0:?}")]
    BlockContext(BlockAnchor),
    #[error(transparent)]
    Block(#[from] BlockIndexError),
}

fn charge(work: &mut usize, count: usize) -> Result<(), ExecutionError> {
    *work = work.checked_sub(count).ok_or(ExecutionError::Budget)?;
    Ok(())
}

fn ordinal(index: usize) -> Result<u32, ExecutionError> {
    index.try_into().map_err(|_| ExecutionError::Budget)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorRoot {
    Expression(ExprId),
    Block(BlockAnchor),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildId {
    Expression(ExprId),
    Statement(StmtId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildRole {
    Application(EvaluationRole),
    Tuple(u32),
    Array(u32),
    MapKey(u32),
    MapValue(u32),
    RecordField(u32),
    RecordSpread(u32),
    Interpolation(u32),
    Operand,
    BinaryLeft,
    BinaryRight,
    Receiver,
    ProjectionKey,
    Index,
    RangeStart,
    RangeEnd,
    Condition,
    Then,
    Else,
    MatchValue,
    MatchGuard(u32),
    MatchBody(u32),
    ControlValue,
    BlockStatement { ordinal: u32, tail: bool },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChildStep {
    pub root: CursorRoot,
    pub role: ChildRole,
    pub child: ChildId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazyOperator {
    And,
    Or,
    Coalesce,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardKind {
    Lazy(LazyOperator),
    If,
    MatchPattern { arm: u32, pattern: PatternId },
    MatchGuard { arm: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GuardRequest {
    pub root: CursorRoot,
    pub kind: GuardKind,
}

/// The host supplies an actual decision, or explores separate cloned cursors
/// for abstract alternatives. Unknown is never interpreted as false here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardAnswer {
    Boolean(bool),
    PayloadPresent(bool),
    PatternMatched(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReductionKind {
    Application,
    Leaf,
    Tuple,
    Array,
    Map,
    Record,
    Interpolation,
    Generic,
    Unary,
    Binary,
    Field,
    ComputedField,
    Index,
    Range,
    Is,
    Control,
    /// `??` still needs its original reducer: an evaluated Result fallback
    /// is a handler to invoke, rather than an already computed result value.
    Lazy {
        operator: LazyOperator,
        evaluated_right: bool,
    },
    If {
        selected: Option<ChildRole>,
    },
    Match {
        arm: Option<u32>,
    },
    Block {
        tail: Option<(StmtId, ExprId)>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reduction {
    pub root: CursorRoot,
    pub kind: ReductionKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorAction {
    Child(ChildStep),
    Guard(GuardRequest),
    Reduce(Reduction),
    Reduced,
}

#[derive(Debug, Clone, Copy)]
struct MatchCase {
    pattern: PatternId,
    guard: Option<ChildStep>,
    body: ChildStep,
}

#[derive(Debug, Clone)]
enum Plan {
    Strict {
        children: Arc<[ChildStep]>,
        reduction: ReductionKind,
    },
    Lazy {
        operator: LazyOperator,
        left: ChildStep,
        right: ChildStep,
    },
    If {
        condition: ChildStep,
        then_branch: ChildStep,
        else_branch: Option<ChildStep>,
    },
    Match {
        value: ChildStep,
        arms: Arc<[MatchCase]>,
    },
}

#[derive(Debug, Clone, Copy)]
enum Stage {
    Strict(usize),
    LazyLeft,
    LazyDecision,
    LazyRight,
    LazyReduce(bool),
    IfCondition,
    IfDecision,
    IfBranch(bool),
    IfReduce(bool),
    MatchValue,
    MatchPattern(usize),
    MatchGuard(usize),
    MatchGuardDecision(usize),
    MatchBody(usize),
    MatchReduce(Option<u32>),
    Reduced,
}

/// Cloning a suspended control position shares the immutable ID plan. Hosts
/// retain their own pending value packets and guards; no AST is cloned.
#[derive(Debug, Clone)]
pub struct ExecutionCursor {
    root: CursorRoot,
    plan: Plan,
    stage: Stage,
    depth: usize,
}

impl ExecutionCursor {
    fn strict(
        root: CursorRoot,
        children: Vec<ChildStep>,
        reduction: ReductionKind,
        depth: usize,
    ) -> Self {
        Self {
            root,
            plan: Plan::Strict {
                children: children.into(),
                reduction,
            },
            stage: Stage::Strict(0),
            depth,
        }
    }

    /// A shallow original-node plan. Child cursors must use `child_depth()`;
    /// loops and unsupported operations are explicit errors, never empty work.
    pub fn expression(
        hir: &HirProgram,
        blocks: &BlockIndex,
        root: ExprId,
        depth: usize,
        work: &mut usize,
    ) -> Result<Self, ExecutionError> {
        charge(work, 1)?;
        if depth > MAX_DEPTH {
            return Err(ExecutionError::Depth);
        }
        let node = hir
            .expression(root)
            .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(root)))?;
        if matches!(node.kind, hir::ExprKind::Call { .. })
            || matches!(&node.kind, hir::ExprKind::Binary { operator, .. } if matches!(operator.as_str(), "|>" | "!>"))
        {
            let (_, children) = application_children(hir, root, work)?;
            return Ok(Self::strict(
                CursorRoot::Expression(root),
                children,
                ReductionKind::Application,
                depth,
            ));
        }
        if matches!(node.kind, hir::ExprKind::Block(_)) {
            return Self::block(hir, blocks, BlockAnchor::ExpressionBody(root), depth, work);
        }
        let owner = CursorRoot::Expression(root);
        let child = |role, id| ChildStep {
            root: owner,
            role,
            child: ChildId::Expression(id),
        };
        let mut children = Vec::new();
        macro_rules! add {
            ($role:expr, $id:expr) => {{
                charge(work, 1)?;
                let id = $id;
                hir.expression(id)
                    .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(id)))?;
                children.push(child($role, id));
                Ok::<(), ExecutionError>(())
            }};
        }
        let reduction = match &node.kind {
            hir::ExprKind::Literal(_)
            | hir::ExprKind::Name(_)
            | hir::ExprKind::Path(_)
            | hir::ExprKind::Lambda { .. }
            | hir::ExprKind::Accessor(_)
            | hir::ExprKind::TypeValue(_)
            | hir::ExprKind::KeyOf(_)
            | hir::ExprKind::Ambient => ReductionKind::Leaf,
            hir::ExprKind::Tuple(items) | hir::ExprKind::Array(items) => {
                let tuple = matches!(node.kind, hir::ExprKind::Tuple(_));
                for (index, id) in items.iter().enumerate() {
                    add!(
                        if tuple {
                            ChildRole::Tuple(ordinal(index)?)
                        } else {
                            ChildRole::Array(ordinal(index)?)
                        },
                        *id
                    )?;
                }
                if tuple {
                    ReductionKind::Tuple
                } else {
                    ReductionKind::Array
                }
            }
            hir::ExprKind::Map(entries) => {
                for (index, (key, value)) in entries.iter().enumerate() {
                    add!(ChildRole::MapKey(ordinal(index)?), *key)?;
                    add!(ChildRole::MapValue(ordinal(index)?), *value)?;
                }
                ReductionKind::Map
            }
            hir::ExprKind::Record { members, .. } => {
                for (index, member) in members.iter().enumerate() {
                    match member {
                        hir::RecordMember::Field { value, .. } => {
                            add!(ChildRole::RecordField(ordinal(index)?), *value)?
                        }
                        hir::RecordMember::Spread(value) => {
                            add!(ChildRole::RecordSpread(ordinal(index)?), *value)?
                        }
                    }
                }
                ReductionKind::Record
            }
            hir::ExprKind::Interpolated(parts) => {
                charge(work, parts.len())?;
                for (index, part) in parts.iter().enumerate() {
                    if let hir::StringPart::Interpolation { expression, .. } = part {
                        add!(ChildRole::Interpolation(ordinal(index)?), *expression)?;
                    }
                }
                ReductionKind::Interpolation
            }
            hir::ExprKind::Generic { base, .. } => {
                add!(ChildRole::Receiver, *base)?;
                ReductionKind::Generic
            }
            hir::ExprKind::Unary { operand, .. } => {
                add!(ChildRole::Operand, *operand)?;
                ReductionKind::Unary
            }
            hir::ExprKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "&&" | "||" | "??") => {
                add!(ChildRole::BinaryLeft, *left)?;
                add!(ChildRole::BinaryRight, *right)?;
                let operator = match operator.as_str() {
                    "&&" => LazyOperator::And,
                    "||" => LazyOperator::Or,
                    _ => LazyOperator::Coalesce,
                };
                return Ok(Self {
                    root: owner,
                    plan: Plan::Lazy {
                        operator,
                        left: children[0],
                        right: children[1],
                    },
                    stage: Stage::LazyLeft,
                    depth,
                });
            }
            hir::ExprKind::Binary { left, right, .. } => {
                add!(ChildRole::BinaryLeft, *left)?;
                add!(ChildRole::BinaryRight, *right)?;
                ReductionKind::Binary
            }
            hir::ExprKind::Field { base, .. } => {
                add!(ChildRole::Receiver, *base)?;
                ReductionKind::Field
            }
            hir::ExprKind::ComputedField { base, key } => {
                add!(ChildRole::Receiver, *base)?;
                add!(ChildRole::ProjectionKey, *key)?;
                ReductionKind::ComputedField
            }
            hir::ExprKind::Index { base, index, .. } => {
                add!(ChildRole::Receiver, *base)?;
                add!(ChildRole::Index, *index)?;
                ReductionKind::Index
            }
            hir::ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    add!(ChildRole::RangeStart, *start)?;
                }
                if let Some(end) = end {
                    add!(ChildRole::RangeEnd, *end)?;
                }
                ReductionKind::Range
            }
            hir::ExprKind::Is { value, .. } => {
                add!(ChildRole::Operand, *value)?;
                ReductionKind::Is
            }
            hir::ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    add!(ChildRole::ControlValue, *value)?;
                }
                ReductionKind::Control
            }
            hir::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                add!(ChildRole::Condition, *condition)?;
                add!(ChildRole::Then, *then_branch)?;
                if let Some(branch) = else_branch {
                    add!(ChildRole::Else, *branch)?;
                }
                return Ok(Self {
                    root: owner,
                    plan: Plan::If {
                        condition: children[0],
                        then_branch: children[1],
                        else_branch: children.get(2).copied(),
                    },
                    stage: Stage::IfCondition,
                    depth,
                });
            }
            hir::ExprKind::Match { value, arms, .. } => {
                add!(ChildRole::MatchValue, *value)?;
                let value = children[0];
                charge(work, arms.len())?;
                let mut cases = Vec::with_capacity(arms.len());
                for (index, arm) in arms.iter().enumerate() {
                    let index = ordinal(index)?;
                    charge(work, 2 + usize::from(arm.guard.is_some()))?;
                    hir.pattern(arm.pattern).ok_or(ExecutionError::MissingNode(
                        hir::NodeId::Pattern(arm.pattern),
                    ))?;
                    hir.expression(arm.body)
                        .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(arm.body)))?;
                    if let Some(guard) = arm.guard {
                        hir.expression(guard)
                            .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(guard)))?;
                    }
                    cases.push(MatchCase {
                        pattern: arm.pattern,
                        guard: arm.guard.map(|id| child(ChildRole::MatchGuard(index), id)),
                        body: child(ChildRole::MatchBody(index), arm.body),
                    });
                }
                charge(work, cases.len())?;
                return Ok(Self {
                    root: owner,
                    plan: Plan::Match {
                        value,
                        arms: cases.into(),
                    },
                    stage: Stage::MatchValue,
                    depth,
                });
            }
            hir::ExprKind::Loop(_) | hir::ExprKind::While { .. } | hir::ExprKind::For { .. } => {
                return Err(ExecutionError::Unsupported {
                    root,
                    kind: "loop control",
                });
            }
            hir::ExprKind::Derive { .. } => {
                return Err(ExecutionError::Unsupported {
                    root,
                    kind: "copy derivation",
                });
            }
            hir::ExprKind::Error => {
                return Err(ExecutionError::Unsupported {
                    root,
                    kind: "recovery node",
                });
            }
            hir::ExprKind::Call { .. } | hir::ExprKind::Block(_) => {
                unreachable!("handled before strict planning")
            }
        };
        charge(work, children.len())?;
        Ok(Self::strict(owner, children, reduction, depth))
    }

    pub fn block(
        hir: &HirProgram,
        blocks: &BlockIndex,
        anchor: BlockAnchor,
        depth: usize,
        work: &mut usize,
    ) -> Result<Self, ExecutionError> {
        charge(work, 1)?;
        if depth > MAX_DEPTH {
            return Err(ExecutionError::Depth);
        }
        let block = blocks.block_with_budget(anchor, work)?;
        let original = match anchor {
            BlockAnchor::FunctionBody(id) => hir.statement(id).and_then(|node| match &node.kind {
                hir::StmtKind::Function(function) => function.body.as_ref(),
                _ => None,
            }),
            BlockAnchor::ExpressionBody(id) => {
                hir.expression(id).and_then(|node| match &node.kind {
                    hir::ExprKind::Block(block) | hir::ExprKind::Loop(block) => Some(block),
                    hir::ExprKind::While { body, .. } | hir::ExprKind::For { body, .. } => {
                        Some(body)
                    }
                    _ => None,
                })
            }
        }
        .ok_or(ExecutionError::BlockContext(anchor))?;
        charge(work, original.statements.len())?;
        charge(work, original.where_items.len())?;
        if original.statements != block.statements || original.where_items != block.where_items {
            return Err(ExecutionError::BlockContext(anchor));
        }
        let tail = blocks.tail_with_budget(anchor, work)?;
        if tail != BlockIndex::structural_tail(hir, original, work)? {
            return Err(ExecutionError::BlockContext(anchor));
        }
        charge(work, block.statements.len())?;
        let root = CursorRoot::Block(anchor);
        let mut children = Vec::with_capacity(block.statements.len());
        for (index, id) in block.statements.iter().enumerate() {
            hir.statement(*id)
                .ok_or(ExecutionError::MissingNode(hir::NodeId::Stmt(*id)))?;
            children.push(ChildStep {
                root,
                role: ChildRole::BlockStatement {
                    ordinal: ordinal(index)?,
                    tail: tail.is_some_and(|(statement, _)| statement == *id),
                },
                child: ChildId::Statement(*id),
            });
        }
        charge(work, children.len())?;
        Ok(Self::strict(
            root,
            children,
            ReductionKind::Block { tail },
            depth,
        ))
    }

    pub fn root(&self) -> CursorRoot {
        self.root
    }
    pub fn child_depth(&self) -> Result<usize, ExecutionError> {
        self.depth
            .checked_add(1)
            .filter(|depth| *depth <= MAX_DEPTH)
            .ok_or(ExecutionError::Depth)
    }

    /// Repeated queries are stable until a completed child or actual guard is
    /// acknowledged. Merely requesting work never advances a suspended child.
    pub fn action(&self, work: &mut usize) -> Result<CursorAction, ExecutionError> {
        charge(work, 1)?;
        let reduce = |kind| {
            CursorAction::Reduce(Reduction {
                root: self.root,
                kind,
            })
        };
        let guard = |kind| {
            CursorAction::Guard(GuardRequest {
                root: self.root,
                kind,
            })
        };
        let action = match (&self.plan, self.stage) {
            (_, Stage::Reduced) => CursorAction::Reduced,
            (
                Plan::Strict {
                    children,
                    reduction,
                },
                Stage::Strict(index),
            ) => children
                .get(index)
                .copied()
                .map_or_else(|| reduce(*reduction), CursorAction::Child),
            (Plan::Lazy { left, .. }, Stage::LazyLeft) => CursorAction::Child(*left),
            (Plan::Lazy { operator, .. }, Stage::LazyDecision) => guard(GuardKind::Lazy(*operator)),
            (Plan::Lazy { right, .. }, Stage::LazyRight) => CursorAction::Child(*right),
            (Plan::Lazy { operator, .. }, Stage::LazyReduce(evaluated_right)) => {
                reduce(ReductionKind::Lazy {
                    operator: *operator,
                    evaluated_right,
                })
            }
            (Plan::If { condition, .. }, Stage::IfCondition) => CursorAction::Child(*condition),
            (Plan::If { .. }, Stage::IfDecision) => guard(GuardKind::If),
            (
                Plan::If {
                    then_branch,
                    else_branch,
                    ..
                },
                Stage::IfBranch(selected),
            ) => {
                if selected {
                    CursorAction::Child(*then_branch)
                } else {
                    else_branch.map_or_else(
                        || reduce(ReductionKind::If { selected: None }),
                        CursorAction::Child,
                    )
                }
            }
            (Plan::If { .. }, Stage::IfReduce(selected)) => reduce(ReductionKind::If {
                selected: Some(if selected {
                    ChildRole::Then
                } else {
                    ChildRole::Else
                }),
            }),
            (Plan::Match { value, .. }, Stage::MatchValue) => CursorAction::Child(*value),
            (Plan::Match { arms, .. }, Stage::MatchPattern(index)) => arms.get(index).map_or_else(
                || reduce(ReductionKind::Match { arm: None }),
                |arm| {
                    guard(GuardKind::MatchPattern {
                        arm: index as u32,
                        pattern: arm.pattern,
                    })
                },
            ),
            (Plan::Match { arms, .. }, Stage::MatchGuard(index)) => {
                CursorAction::Child(arms[index].guard.ok_or(ExecutionError::UnexpectedGuard)?)
            }
            (Plan::Match { .. }, Stage::MatchGuardDecision(index)) => {
                guard(GuardKind::MatchGuard {
                    arm: ordinal(index)?,
                })
            }
            (Plan::Match { arms, .. }, Stage::MatchBody(index)) => {
                CursorAction::Child(arms[index].body)
            }
            (Plan::Match { .. }, Stage::MatchReduce(arm)) => reduce(ReductionKind::Match { arm }),
            _ => return Err(ExecutionError::UnexpectedReduction),
        };
        if matches!(action, CursorAction::Child(_)) {
            self.child_depth()?;
        }
        Ok(action)
    }

    pub fn complete(&mut self, child: ChildStep, work: &mut usize) -> Result<(), ExecutionError> {
        charge(work, 1)?;
        if self.action(work)? != CursorAction::Child(child) {
            return Err(ExecutionError::UnexpectedChild);
        }
        self.stage = match self.stage {
            Stage::Strict(index) => Stage::Strict(index + 1),
            Stage::LazyLeft => Stage::LazyDecision,
            Stage::LazyRight => Stage::LazyReduce(true),
            Stage::IfCondition => Stage::IfDecision,
            Stage::IfBranch(selected) => Stage::IfReduce(selected),
            Stage::MatchValue => Stage::MatchPattern(0),
            Stage::MatchGuard(index) => Stage::MatchGuardDecision(index),
            Stage::MatchBody(index) => Stage::MatchReduce(Some(ordinal(index)?)),
            _ => return Err(ExecutionError::UnexpectedChild),
        };
        Ok(())
    }

    pub fn choose(
        &mut self,
        request: GuardRequest,
        answer: GuardAnswer,
        work: &mut usize,
    ) -> Result<(), ExecutionError> {
        charge(work, 1)?;
        if self.action(work)? != CursorAction::Guard(request) {
            return Err(ExecutionError::UnexpectedGuard);
        }
        let next = match (request.kind, answer) {
            (GuardKind::Lazy(LazyOperator::And), GuardAnswer::Boolean(true))
            | (GuardKind::Lazy(LazyOperator::Or), GuardAnswer::Boolean(false))
            | (GuardKind::Lazy(LazyOperator::Coalesce), GuardAnswer::PayloadPresent(false)) => {
                Stage::LazyRight
            }
            (GuardKind::Lazy(LazyOperator::And | LazyOperator::Or), GuardAnswer::Boolean(_))
            | (GuardKind::Lazy(LazyOperator::Coalesce), GuardAnswer::PayloadPresent(true)) => {
                Stage::LazyReduce(false)
            }
            (GuardKind::If, GuardAnswer::Boolean(selected)) => Stage::IfBranch(selected),
            (GuardKind::MatchPattern { arm, .. }, GuardAnswer::PatternMatched(false))
            | (GuardKind::MatchGuard { arm }, GuardAnswer::Boolean(false)) => {
                Stage::MatchPattern(arm as usize + 1)
            }
            (GuardKind::MatchPattern { arm, .. }, GuardAnswer::PatternMatched(true)) => {
                let Plan::Match { arms, .. } = &self.plan else {
                    return Err(ExecutionError::UnexpectedGuard);
                };
                if arms[arm as usize].guard.is_some() {
                    Stage::MatchGuard(arm as usize)
                } else {
                    Stage::MatchBody(arm as usize)
                }
            }
            (GuardKind::MatchGuard { arm }, GuardAnswer::Boolean(true)) => {
                Stage::MatchBody(arm as usize)
            }
            _ => return Err(ExecutionError::UnexpectedGuard),
        };
        self.stage = next;
        Ok(())
    }

    pub fn reduce(&mut self, reduction: Reduction, work: &mut usize) -> Result<(), ExecutionError> {
        charge(work, 1)?;
        match self.action(work)? {
            CursorAction::Reduce(actual) if actual == reduction => {
                self.stage = Stage::Reduced;
                Ok(())
            }
            CursorAction::Reduced => Err(ExecutionError::AlreadyReduced),
            _ => Err(ExecutionError::UnexpectedReduction),
        }
    }
}

fn application_children(
    hir: &HirProgram,
    root: ExprId,
    work: &mut usize,
) -> Result<(ApplicationKind, Vec<ChildStep>), ExecutionError> {
    charge(work, 1)?;
    let node = hir
        .expression(root)
        .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(root)))?;
    let count = match &node.kind {
        hir::ExprKind::Call { arguments, .. } => arguments.len().checked_add(1),
        hir::ExprKind::Binary {
            operator, right, ..
        } if matches!(operator.as_str(), "|>" | "!>") => {
            charge(work, 1)?;
            let right = hir
                .expression(*right)
                .ok_or(ExecutionError::MissingNode(hir::NodeId::Expr(*right)))?;
            match &right.kind {
                hir::ExprKind::Derive { base: None, .. } => {
                    return Err(ExecutionError::Unsupported {
                        root,
                        kind: "copy pipeline",
                    });
                }
                hir::ExprKind::Call { arguments, .. } => arguments.len().checked_add(2),
                _ => Some(2),
            }
        }
        _ => return Err(ExecutionError::NotApplication(root)),
    }
    .ok_or(ExecutionError::Budget)?;
    // HirApplication admits child IDs and copies only operand metadata. Pay
    // before it allocates, and before allocating the owned ID sequence below.
    charge(work, count.checked_mul(3).ok_or(ExecutionError::Budget)?)?;
    let application = hir
        .application(root)
        .map_err(ExecutionError::InvalidApplication)?
        .ok_or(ExecutionError::NotApplication(root))?;
    let children = application
        .evaluation_order()
        .map(|role| {
            let expression =
                application
                    .expression(role)
                    .ok_or(ExecutionError::InvalidApplication(
                        "application role is absent",
                    ))?;
            Ok(ChildStep {
                root: CursorRoot::Expression(root),
                role: ChildRole::Application(role),
                child: ChildId::Expression(expression),
            })
        })
        .collect::<Result<Vec<_>, ExecutionError>>()?;
    Ok((application.kind, children))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ApplicationChild {
    pub root: ExprId,
    pub role: EvaluationRole,
    pub expression: ExprId,
}

/// Production entry point for the sema application evaluator. The cursor
/// owns original IDs, so evaluating a child may mutably borrow the checker.
#[derive(Debug, Clone)]
pub struct ApplicationCursor {
    cursor: ExecutionCursor,
    kind: ApplicationKind,
    len: usize,
}

impl ApplicationCursor {
    pub fn new(hir: &HirProgram, root: ExprId, work: &mut usize) -> Result<Self, ExecutionError> {
        let (kind, children) = application_children(hir, root, work)?;
        let len = children.len();
        Ok(Self {
            cursor: ExecutionCursor::strict(
                CursorRoot::Expression(root),
                children,
                ReductionKind::Application,
                0,
            ),
            kind,
            len,
        })
    }
    pub fn kind(&self) -> ApplicationKind {
        self.kind
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn position(&self) -> usize {
        match self.cursor.stage {
            Stage::Strict(index) => index,
            _ => self.len,
        }
    }
    /// Original syntax strictly after the pending child, for static checking
    /// of an unreachable suffix. This neither completes the pending child nor
    /// grants an evaluation occurrence to any returned expression.
    pub fn later_children(
        &self,
        work: &mut usize,
    ) -> Result<Vec<ApplicationChild>, ExecutionError> {
        charge(work, 1)?;
        let Stage::Strict(index) = self.cursor.stage else {
            return Err(ExecutionError::AlreadyReduced);
        };
        let Plan::Strict { children, .. } = &self.cursor.plan else {
            return Err(ExecutionError::UnexpectedChild);
        };
        let start = index
            .checked_add(1)
            .ok_or(ExecutionError::Budget)?
            .min(children.len());
        let later = &children[start..];
        charge(work, later.len())?;
        later
            .iter()
            .map(|step| match *step {
                ChildStep {
                    root: CursorRoot::Expression(root),
                    role: ChildRole::Application(role),
                    child: ChildId::Expression(expression),
                } => Ok(ApplicationChild {
                    root,
                    role,
                    expression,
                }),
                _ => Err(ExecutionError::UnexpectedChild),
            })
            .collect()
    }
    pub fn pending(&self, work: &mut usize) -> Result<Option<ApplicationChild>, ExecutionError> {
        match self.cursor.action(work)? {
            CursorAction::Child(ChildStep {
                root: CursorRoot::Expression(root),
                role: ChildRole::Application(role),
                child: ChildId::Expression(expression),
            }) => Ok(Some(ApplicationChild {
                root,
                role,
                expression,
            })),
            CursorAction::Reduce(_) => Ok(None),
            CursorAction::Reduced => Err(ExecutionError::AlreadyReduced),
            _ => Err(ExecutionError::UnexpectedChild),
        }
    }
    pub fn complete(
        &mut self,
        child: ApplicationChild,
        work: &mut usize,
    ) -> Result<(), ExecutionError> {
        self.cursor.complete(
            ChildStep {
                root: CursorRoot::Expression(child.root),
                role: ChildRole::Application(child.role),
                child: ChildId::Expression(child.expression),
            },
            work,
        )
    }
    pub fn reduce(&mut self, work: &mut usize) -> Result<ExprId, ExecutionError> {
        let CursorRoot::Expression(root) = self.cursor.root else {
            return Err(ExecutionError::UnexpectedReduction);
        };
        self.cursor.reduce(
            Reduction {
                root: self.cursor.root,
                kind: ReductionKind::Application,
            },
            work,
        )?;
        Ok(root)
    }
}

#[cfg(test)]
#[path = "execution_tests.rs"]
mod tests;
