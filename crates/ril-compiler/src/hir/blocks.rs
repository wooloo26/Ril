//! Immutable block identities reconstructed from real HIR edges. This index
//! locates syntax; it supplies no normal-completion, Source or access proof.
use super::nodes::{self as hir, HirProgram, NodeId, WalkError};
use ril_compiler_core::ids::{BlockAnchor, ExprId, StmtId};
use ril_syntax::ast;
use std::collections::{BTreeMap, BTreeSet};

const BUILD_WORK: usize = 1_000_000;
const QUERY_WORK: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BlockIndexError {
    #[error("block index work budget exhausted")]
    Budget,
    #[error("block index HIR node is absent: {0:?}")]
    MissingNode(NodeId),
    #[error("source block statement has no HIR identity")]
    MissingStatementIdentity,
    #[error("block repeats a statement identity: {0:?}")]
    DuplicateStatement(StmtId),
    #[error("block anchor has no actual directly owned block: {0:?}")]
    UnknownAnchor(BlockAnchor),
}

#[derive(Debug, Clone)]
struct IndexedBlock {
    syntax: hir::Block,
    tail: Option<(StmtId, ExprId)>,
}

/// An owned, bounded copy of block member IDs and cached structural tails.
/// Build once per HIR revision. Queries never scan the rest of the HIR and do
/// not depend on the order of spans or the shape of an AST preview suffix.
#[derive(Debug, Clone, Default)]
pub struct BlockIndex {
    blocks: BTreeMap<BlockAnchor, IndexedBlock>,
    /// None is a real statement outside a directly owned block (e.g. a module
    /// declaration). Absence is an invalid statement ID in this HIR revision.
    members: BTreeMap<StmtId, Option<BlockAnchor>>,
}

fn charge(work: &mut usize, cost: usize) -> Result<(), BlockIndexError> {
    *work = work.checked_sub(cost).ok_or(BlockIndexError::Budget)?;
    Ok(())
}

fn lookup_cost(entries: usize) -> usize {
    entries.checked_ilog2().unwrap_or(0) as usize + 1
}

impl BlockIndex {
    /// Query a directly owned block in the current HIR without rebuilding an
    /// index for one producer occurrence. The same structural-tail rule backs
    /// the cached independent index below.
    pub(crate) fn tail_from_hir(
        hir: &HirProgram,
        anchor: BlockAnchor,
        work: &mut usize,
    ) -> Result<Option<(StmtId, ExprId)>, BlockIndexError> {
        charge(work, 1)?;
        let block = match anchor {
            BlockAnchor::FunctionBody(id) => match &hir
                .statement(id)
                .ok_or(BlockIndexError::MissingNode(NodeId::Stmt(id)))?
                .kind
            {
                hir::StmtKind::Function(function) => function.body.as_ref(),
                _ => None,
            },
            BlockAnchor::ExpressionBody(id) => match &hir
                .expression(id)
                .ok_or(BlockIndexError::MissingNode(NodeId::Expr(id)))?
                .kind
            {
                hir::ExprKind::Block(block) | hir::ExprKind::Loop(block) => Some(block),
                hir::ExprKind::While { body, .. } | hir::ExprKind::For { body, .. } => Some(body),
                _ => None,
            },
        }
        .ok_or(BlockIndexError::UnknownAnchor(anchor))?;
        Self::structural_tail(hir, block, work)
    }

    pub fn new(hir: &HirProgram) -> Result<Self, BlockIndexError> {
        let mut work = BUILD_WORK;
        Self::new_with_budget(hir, &mut work)
    }

    pub fn new_with_budget(hir: &HirProgram, work: &mut usize) -> Result<Self, BlockIndexError> {
        charge(work, 1)?;
        let mut index = Self::default();
        let mut failure = None;
        // The structural walk independently checks every reached child ID,
        // including non-block children. Its frontier is bounded before growth.
        hir.walk(*work, |node, _| {
            if failure.is_some() {
                return;
            }
            let admit = (|| -> Result<(), BlockIndexError> {
                charge(work, 1)?;
                match node {
                    NodeId::Stmt(id) => {
                        charge(work, lookup_cost(index.members.len()))?;
                        index.members.entry(id).or_insert(None);
                        let statement = hir
                            .statement(id)
                            .ok_or(BlockIndexError::MissingNode(node))?;
                        if let hir::StmtKind::Function(function) = &statement.kind
                            && let Some(block) = &function.body
                        {
                            index.admit(hir, BlockAnchor::FunctionBody(id), block, work)?;
                        }
                    }
                    NodeId::Expr(id) => {
                        let expression = hir
                            .expression(id)
                            .ok_or(BlockIndexError::MissingNode(node))?;
                        let block = match &expression.kind {
                            hir::ExprKind::Block(block) | hir::ExprKind::Loop(block) => Some(block),
                            hir::ExprKind::While { body, .. } | hir::ExprKind::For { body, .. } => {
                                Some(body)
                            }
                            _ => None,
                        };
                        if let Some(block) = block {
                            index.admit(hir, BlockAnchor::ExpressionBody(id), block, work)?;
                        }
                    }
                    _ => {}
                }
                Ok(())
            })();
            if let Err(error) = admit {
                failure = Some(error);
            }
        })
        .map_err(|error| match error {
            WalkError::Budget => BlockIndexError::Budget,
            WalkError::MissingNode(node) => BlockIndexError::MissingNode(node),
        })?;
        if let Some(error) = failure {
            return Err(error);
        }
        Ok(index)
    }

    fn admit(
        &mut self,
        hir: &HirProgram,
        anchor: BlockAnchor,
        block: &hir::Block,
        work: &mut usize,
    ) -> Result<(), BlockIndexError> {
        charge(work, lookup_cost(self.blocks.len()))?;
        if self.blocks.contains_key(&anchor) {
            return Err(BlockIndexError::UnknownAnchor(anchor));
        }
        for id in block.statements.iter().chain(&block.where_items) {
            charge(work, lookup_cost(self.members.len()))?;
            hir.statement(*id)
                .ok_or(BlockIndexError::MissingNode(NodeId::Stmt(*id)))?;
            let member = self.members.entry(*id).or_insert(None);
            if member.replace(anchor).is_some() {
                return Err(BlockIndexError::DuplicateStatement(*id));
            }
        }
        let tail = Self::structural_tail(hir, block, work)?;
        // Charge the copied member edges before allocating the owned lists.
        charge(work, block.statements.len())?;
        charge(work, block.where_items.len())?;
        self.blocks.insert(
            anchor,
            IndexedBlock {
                syntax: block.clone(),
                tail,
            },
        );
        Ok(())
    }

    /// Reconstruct from the supplied HIR revision, so consumers can reject a
    /// cached tail whose member IDs survived a change to statement structure.
    pub(super) fn structural_tail(
        hir: &HirProgram,
        block: &hir::Block,
        work: &mut usize,
    ) -> Result<Option<(StmtId, ExprId)>, BlockIndexError> {
        let mut tail = None;
        // where_items are declarations, not the block's executed suffix.
        // Evaluate only the ordered statements when selecting its tail.
        charge(work, block.statements.len())?;
        for &id in &block.statements {
            let statement = hir
                .statement(id)
                .ok_or(BlockIndexError::MissingNode(NodeId::Stmt(id)))?;
            match &statement.kind {
                hir::StmtKind::Function(_)
                | hir::StmtKind::Type { .. }
                | hir::StmtKind::Effect { .. } => continue,
                hir::StmtKind::Expr {
                    expression,
                    terminated: false,
                } => {
                    charge(work, 1)?;
                    let expression_node = hir
                        .expression(*expression)
                        .ok_or(BlockIndexError::MissingNode(NodeId::Expr(*expression)))?;
                    tail = (!matches!(expression_node.kind, hir::ExprKind::Control { .. }))
                        .then_some((id, *expression));
                }
                _ => tail = None,
            }
        }
        Ok(tail)
    }

    pub fn block(&self, anchor: BlockAnchor) -> Result<&hir::Block, BlockIndexError> {
        let mut work = QUERY_WORK;
        self.block_with_budget(anchor, &mut work)
    }

    pub fn block_with_budget(
        &self,
        anchor: BlockAnchor,
        work: &mut usize,
    ) -> Result<&hir::Block, BlockIndexError> {
        charge(work, lookup_cost(self.blocks.len()))?;
        self.blocks
            .get(&anchor)
            .map(|block| &block.syntax)
            .ok_or(BlockIndexError::UnknownAnchor(anchor))
    }

    pub fn source_block(&self, block: &ast::Block) -> Result<Option<BlockAnchor>, BlockIndexError> {
        let mut work = QUERY_WORK;
        self.source_block_with_budget(block, &mut work)
    }

    pub fn source_block_with_budget(
        &self,
        block: &ast::Block,
        work: &mut usize,
    ) -> Result<Option<BlockAnchor>, BlockIndexError> {
        charge(work, 1)?;
        let count = block
            .statements
            .len()
            .checked_add(block.where_items.len())
            .ok_or(BlockIndexError::Budget)?;
        if count == 0 {
            // Several real blocks can be empty. None has a Source-producing
            // statement; an equal span cannot select one of those blocks.
            return Ok(None);
        }
        charge(
            work,
            count
                .checked_mul(lookup_cost(self.members.len()) + lookup_cost(count))
                .ok_or(BlockIndexError::Budget)?,
        )?;
        let mut ids = BTreeSet::new();
        let mut candidate = None;
        let mut agrees = true;
        for statement in block.statements.iter().chain(&block.where_items) {
            let id = statement
                .hir_id
                .ok_or(BlockIndexError::MissingStatementIdentity)?;
            if !ids.insert(id) {
                return Err(BlockIndexError::DuplicateStatement(id));
            }
            let owner = self
                .members
                .get(&id)
                .ok_or(BlockIndexError::MissingNode(NodeId::Stmt(id)))?;
            if let Some(owner) = owner {
                if let Some(candidate) = candidate {
                    agrees &= candidate == *owner;
                } else {
                    candidate = Some(*owner);
                }
            } else {
                agrees = false;
            }
        }
        let Some(anchor) = candidate.filter(|_| agrees) else {
            return Ok(None);
        };
        let original = self.block_with_budget(anchor, work)?;
        charge(work, count)?;
        let same = original.statements.len() == block.statements.len()
            && original.where_items.len() == block.where_items.len()
            && original
                .statements
                .iter()
                .zip(&block.statements)
                .all(|(id, statement)| statement.hir_id == Some(*id))
            && original
                .where_items
                .iter()
                .zip(&block.where_items)
                .all(|(id, statement)| statement.hir_id == Some(*id));
        Ok(same.then_some(anchor))
    }

    /// A structural candidate only. Its real evaluation may still be Never,
    /// conditional or interrupted; a dynamic answer receipt must prove that.
    pub fn tail(&self, anchor: BlockAnchor) -> Result<Option<(StmtId, ExprId)>, BlockIndexError> {
        let mut work = QUERY_WORK;
        self.tail_with_budget(anchor, &mut work)
    }

    pub fn tail_with_budget(
        &self,
        anchor: BlockAnchor,
        work: &mut usize,
    ) -> Result<Option<(StmtId, ExprId)>, BlockIndexError> {
        charge(work, lookup_cost(self.blocks.len()))?;
        self.blocks
            .get(&anchor)
            .map(|block| block.tail)
            .ok_or(BlockIndexError::UnknownAnchor(anchor))
    }
}
