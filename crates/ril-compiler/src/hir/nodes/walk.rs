//! One exhaustive structural traversal used by analysis and editor consumers.
//! Structural order is not an evaluation order; e.g. assignment execution
//! still evaluates its RHS before its destination in the semantic checker.
use super::*;
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum WalkError {
    #[error("HIR node {0:?} is absent")]
    MissingNode(NodeId),
    #[error("HIR traversal budget exhausted")]
    Budget,
}

impl HirProgram {
    /// Return direct structural children, bounded before each allocation.
    /// Origin anchors and lexical owners are references, not child edges.
    pub fn children(&self, id: NodeId, limit: usize) -> Result<Vec<NodeId>, WalkError> {
        let mut children = Vec::new();
        self.child_edges(id, &mut |child| {
            if children.len() >= limit {
                return Err(WalkError::Budget);
            }
            children.push(child);
            Ok(())
        })?;
        Ok(children)
    }
    /// Visit every source and explicitly generated node once, without recursive
    /// calls. The budget bounds nodes and the pending frontier, including wide
    /// siblings. IDs are paired with this program; spans never select identity.
    pub fn walk(
        &self,
        budget: usize,
        visit: impl FnMut(NodeId, &NodeInfo),
    ) -> Result<(), WalkError> {
        let roots = self
            .roots
            .iter()
            .copied()
            .map(NodeId::Stmt)
            .chain(self.generated_roots.iter().copied().map(NodeId::Expr));
        self.walk_from(roots, budget, visit)
    }
    pub fn walk_from(
        &self,
        roots: impl IntoIterator<Item = NodeId>,
        mut budget: usize,
        mut visit: impl FnMut(NodeId, &NodeInfo),
    ) -> Result<(), WalkError> {
        let mut pending = Vec::new();
        for root in roots {
            if pending.len() >= budget {
                return Err(WalkError::Budget);
            }
            pending.push(root);
        }
        pending.reverse();
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            budget = budget.checked_sub(1).ok_or(WalkError::Budget)?;
            let info = self.info(id).ok_or(WalkError::MissingNode(id))?;
            visit(id, info);
            let available = budget.checked_sub(pending.len()).ok_or(WalkError::Budget)?;
            let children = self.children(id, available)?;
            pending.extend(children.into_iter().rev());
        }
        Ok(())
    }
    fn child_edges(
        &self,
        id: NodeId,
        edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
    ) -> Result<(), WalkError> {
        fn expr(
            id: ExprId,
            edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
        ) -> Result<(), WalkError> {
            edge(NodeId::Expr(id))
        }
        fn ty(
            id: TypeExprId,
            edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
        ) -> Result<(), WalkError> {
            edge(NodeId::Type(id))
        }
        fn pattern(
            id: PatternId,
            edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
        ) -> Result<(), WalkError> {
            edge(NodeId::Pattern(id))
        }
        fn parameters(
            values: &[Parameter],
            edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
        ) -> Result<(), WalkError> {
            for parameter in values {
                pattern(parameter.pattern, edge)?;
                if let Some(id) = parameter.ty {
                    ty(id, edge)?;
                }
                if let Some(id) = parameter.default {
                    expr(id, edge)?;
                }
            }
            Ok(())
        }
        fn block(
            block: &Block,
            edge: &mut impl FnMut(NodeId) -> Result<(), WalkError>,
        ) -> Result<(), WalkError> {
            for id in block.statements.iter().chain(&block.where_items) {
                edge(NodeId::Stmt(*id))?;
            }
            Ok(())
        }
        match id {
            NodeId::Expr(id) => match &self
                .expression(id)
                .ok_or(WalkError::MissingNode(NodeId::Expr(id)))?
                .kind
            {
                ExprKind::Literal(_)
                | ExprKind::Name(_)
                | ExprKind::Path(_)
                | ExprKind::Accessor(_)
                | ExprKind::Ambient
                | ExprKind::Error => {}
                ExprKind::Interpolated(parts) => {
                    for part in parts {
                        match part {
                            StringPart::Text(_) => {}
                            StringPart::Interpolation { expression, .. } => {
                                expr(*expression, edge)?
                            }
                        }
                    }
                }
                ExprKind::Generic { base, arguments } => {
                    expr(*base, edge)?;
                    for id in arguments {
                        ty(*id, edge)?;
                    }
                }
                ExprKind::Tuple(items) | ExprKind::Array(items) => {
                    for id in items {
                        expr(*id, edge)?;
                    }
                }
                ExprKind::Map(items) => {
                    for (a, b) in items {
                        expr(*a, edge)?;
                        expr(*b, edge)?;
                    }
                }
                ExprKind::Record {
                    ty: annotation,
                    members,
                } => {
                    if let Some(id) = annotation {
                        ty(*id, edge)?;
                    }
                    for member in members {
                        match member {
                            RecordMember::Field { value, .. } | RecordMember::Spread(value) => {
                                expr(*value, edge)?
                            }
                        }
                    }
                }
                ExprKind::Unary { operand, .. } => expr(*operand, edge)?,
                ExprKind::Binary { left, right, .. } => {
                    expr(*left, edge)?;
                    expr(*right, edge)?;
                }
                ExprKind::Call { callee, arguments } => {
                    expr(*callee, edge)?;
                    for arg in arguments {
                        expr(arg.value, edge)?;
                    }
                }
                ExprKind::Field { base, .. } => expr(*base, edge)?,
                ExprKind::ComputedField { base, key } => {
                    expr(*base, edge)?;
                    expr(*key, edge)?;
                }
                ExprKind::Index { base, index, .. } => {
                    expr(*base, edge)?;
                    expr(*index, edge)?;
                }
                ExprKind::Lambda {
                    parameters: params,
                    return_type,
                    body,
                    ..
                } => {
                    parameters(params, edge)?;
                    if let Some(id) = return_type {
                        ty(*id, edge)?;
                    }
                    expr(*body, edge)?;
                }
                ExprKind::Block(body) | ExprKind::Loop(body) => block(body, edge)?,
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    expr(*condition, edge)?;
                    expr(*then_branch, edge)?;
                    if let Some(id) = else_branch {
                        expr(*id, edge)?;
                    }
                }
                ExprKind::Match { value, arms, .. } => {
                    expr(*value, edge)?;
                    for arm in arms {
                        pattern(arm.pattern, edge)?;
                        if let Some(id) = arm.guard {
                            expr(id, edge)?;
                        }
                        expr(arm.body, edge)?;
                    }
                }
                ExprKind::Is { value, pattern: id } => {
                    expr(*value, edge)?;
                    pattern(*id, edge)?;
                }
                ExprKind::While { condition, body } => {
                    expr(*condition, edge)?;
                    block(body, edge)?;
                }
                ExprKind::For {
                    iterable,
                    pattern: id,
                    body,
                } => {
                    expr(*iterable, edge)?;
                    pattern(*id, edge)?;
                    block(body, edge)?;
                }
                ExprKind::Control { value, .. } => {
                    if let Some(id) = value {
                        expr(*id, edge)?;
                    }
                }
                ExprKind::TypeValue(id) | ExprKind::KeyOf(id) => ty(*id, edge)?,
                ExprKind::Derive { base, recipe } => {
                    if let Some(id) = base {
                        expr(*id, edge)?;
                    }
                    expr(*recipe, edge)?;
                }
                ExprKind::Range { start, end, .. } => {
                    if let Some(id) = start {
                        expr(*id, edge)?;
                    }
                    if let Some(id) = end {
                        expr(*id, edge)?;
                    }
                }
            },
            NodeId::Stmt(id) => match &self
                .statement(id)
                .ok_or(WalkError::MissingNode(NodeId::Stmt(id)))?
                .kind
            {
                StmtKind::Binding {
                    pattern: id,
                    ty: annotation,
                    value,
                    fallback,
                    ..
                } => {
                    pattern(*id, edge)?;
                    if let Some(id) = annotation {
                        ty(*id, edge)?;
                    }
                    expr(*value, edge)?;
                    if let Some(id) = fallback {
                        expr(*id, edge)?;
                    }
                }
                StmtKind::Function(function) => {
                    for id in &function.generics {
                        edge(NodeId::Generic(*id))?;
                    }
                    parameters(&function.parameters, edge)?;
                    if let Some(id) = function.return_type {
                        ty(id, edge)?;
                    }
                    for id in &function.signature_where {
                        edge(NodeId::Stmt(*id))?;
                    }
                    if let Some(body) = &function.body {
                        block(body, edge)?;
                    }
                }
                StmtKind::Type {
                    generics,
                    value,
                    variants,
                    ..
                } => {
                    for id in generics {
                        edge(NodeId::Generic(*id))?;
                    }
                    if let Some(id) = value {
                        ty(*id, edge)?;
                    }
                    for variant in variants {
                        for id in &variant.generics {
                            edge(NodeId::Generic(*id))?;
                        }
                        if let Some(id) = variant.payload {
                            ty(id, edge)?;
                        }
                        if let Some(id) = variant.result {
                            ty(id, edge)?;
                        }
                    }
                }
                StmtKind::Effect {
                    generics,
                    operations,
                    members,
                    ..
                } => {
                    for id in generics {
                        edge(NodeId::Generic(*id))?;
                    }
                    for id in operations {
                        edge(NodeId::Stmt(*id))?;
                    }
                    for id in members {
                        ty(*id, edge)?;
                    }
                }
                StmtKind::Use { .. } => {}
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        expr(arm.operation, edge)?;
                        parameters(&arm.parameters, edge)?;
                        expr(arm.body, edge)?;
                    }
                }
                StmtKind::HandlerApplication(id) => expr(*id, edge)?,
                StmtKind::Assignment { target, value, .. } => {
                    expr(*target, edge)?;
                    expr(*value, edge)?;
                }
                StmtKind::Expr { expression, .. } => expr(*expression, edge)?,
            },
            NodeId::Pattern(id) => match &self
                .pattern(id)
                .ok_or(WalkError::MissingNode(NodeId::Pattern(id)))?
                .kind
            {
                PatternKind::Name(_)
                | PatternKind::Wildcard
                | PatternKind::Literal(_)
                | PatternKind::Error => {}
                PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
                    for id in items {
                        pattern(*id, edge)?;
                    }
                }
                PatternKind::Record {
                    ty: annotation,
                    fields,
                    ..
                } => {
                    if let Some(id) = annotation {
                        ty(*id, edge)?;
                    }
                    for field in fields {
                        pattern(field.pattern, edge)?;
                    }
                }
                PatternKind::Constructor { arguments, .. } => {
                    for id in arguments {
                        pattern(*id, edge)?;
                    }
                }
                PatternKind::Mode { pattern: id, .. } => pattern(*id, edge)?,
                PatternKind::Type { ty: id, .. } => ty(*id, edge)?,
                PatternKind::Value(id) => expr(*id, edge)?,
            },
            NodeId::Generic(id) => {
                let node = self
                    .generic(id)
                    .ok_or(WalkError::MissingNode(NodeId::Generic(id)))?;
                if let Some(id) = node.bound {
                    ty(id, edge)?;
                }
                if let Some(id) = node.default {
                    ty(id, edge)?;
                }
            }
            NodeId::Type(id) => match &self
                .type_expression(id)
                .ok_or(WalkError::MissingNode(NodeId::Type(id)))?
                .kind
            {
                TypeKind::Name { arguments, .. } => {
                    for id in arguments {
                        ty(*id, edge)?;
                    }
                }
                TypeKind::Optional(id) | TypeKind::KeyOf(id) | TypeKind::Rest(id) => ty(*id, edge)?,
                TypeKind::Array { length, element } => {
                    if let Some(id) = length {
                        expr(*id, edge)?;
                    }
                    ty(*element, edge)?;
                }
                TypeKind::Map { key, value } => {
                    ty(*key, edge)?;
                    ty(*value, edge)?;
                }
                TypeKind::Tuple(items) => {
                    for id in items {
                        ty(*id, edge)?;
                    }
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        ty(field.ty, edge)?;
                    }
                    if let Some(id) = row {
                        ty(*id, edge)?;
                    }
                }
                TypeKind::Callable {
                    parameters: params,
                    result,
                    ..
                } => {
                    parameters(params, edge)?;
                    if let Some(id) = result {
                        ty(*id, edge)?;
                    }
                }
                TypeKind::TypeFunction { parameters, body } => {
                    for id in parameters {
                        edge(NodeId::Generic(*id))?;
                    }
                    expr(*body, edge)?;
                }
                TypeKind::Projection { base, .. } => ty(*base, edge)?,
                TypeKind::ComputedProjection { base, key } => {
                    ty(*base, edge)?;
                    expr(*key, edge)?;
                }
                TypeKind::Computation(id) => expr(*id, edge)?,
                TypeKind::Mapped { keys, value, .. } => {
                    expr(*keys, edge)?;
                    ty(*value, edge)?;
                }
                TypeKind::KindArrow { parameter, result } => {
                    ty(*parameter, edge)?;
                    ty(*result, edge)?;
                }
                TypeKind::Error => {}
            },
        }
        Ok(())
    }
}
