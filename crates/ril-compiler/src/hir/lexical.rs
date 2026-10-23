//! Static value-name resolution from original HIR edges. This index identifies
//! a lexical binder; it proves neither initialization nor a dynamic activation.
use super::nodes::{self as h, HirProgram, LowerError, NodeId};
use ril_compiler_core::ids::{ExprId, GenericParamId, PatternId, StmtId, TypeExprId};
use std::collections::{BTreeMap, BTreeSet};

type Bindings = BTreeMap<String, Option<PatternId>>;

#[derive(Debug, Clone, Copy)]
enum NameBinding {
    Pattern(PatternId),
    Generic(GenericParamId),
    Other,
}

#[derive(Debug, Default)]
pub struct LexicalBindings {
    names: BTreeMap<ExprId, NameBinding>,
    types: BTreeMap<TypeExprId, TypeNameBinding>,
    pattern_names: BTreeMap<PatternId, NameBinding>,
    generated_roots: usize,
    scopes: Vec<Scope>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeNameBinding {
    Declaration(StmtId),
    Generic(GenericParamId),
    Other,
    Unbound,
}

#[derive(Debug)]
struct Scope {
    parent: Option<usize>,
    names: BTreeMap<String, NameBinding>,
    types: BTreeMap<String, StmtId>,
    generics: BTreeMap<String, GenericParamId>,
    longest_name: usize,
    unknown_imports: bool,
}

struct Builder<'a, 'w> {
    hir: &'a HirProgram,
    work: &'w mut usize,
    visited: BTreeSet<NodeId>,
    index: LexicalBindings,
}

fn charge(work: &mut usize, units: usize) -> Result<(), LowerError> {
    *work = work
        .checked_sub(units)
        .ok_or(LowerError::Budget("lexical bindings"))?;
    Ok(())
}

fn lookup_cost(entries: usize) -> usize {
    entries.checked_ilog2().unwrap_or(0) as usize + 1
}

impl LexicalBindings {
    pub fn new(hir: &HirProgram, work: &mut usize) -> Result<Self, LowerError> {
        charge(work, 1)?;
        let mut builder = Builder {
            hir,
            work,
            visited: BTreeSet::new(),
            index: Self::default(),
        };
        let scope = builder.scope(None)?;
        builder.sequence(hir.roots(), &[], scope, 0)?;
        builder.index.refresh_generated(hir, builder.work)?;
        Ok(builder.index)
    }

    /// Extend an index of this same immutable source HIR with newly appended
    /// generated roots. Original lexical scopes are never reinterpreted here.
    pub fn refresh_generated(
        &mut self,
        hir: &HirProgram,
        work: &mut usize,
    ) -> Result<(), LowerError> {
        charge(work, 1)?;
        let appended = hir
            .generated_roots()
            .get(self.generated_roots..)
            .ok_or(LowerError::Correspondence)?;
        charge(work, appended.len())?;
        for root in appended {
            self.append_generated(hir, *root, work)?;
            self.generated_roots += 1;
        }
        Ok(())
    }

    fn append_generated(
        &mut self,
        hir: &HirProgram,
        root: NodeId,
        work: &mut usize,
    ) -> Result<(), LowerError> {
        // Pattern-value Names read the environment before their original
        // pattern binds a name. No later same-spelled binder can replace it.
        charge(work, 1)?;
        if let NodeId::Stmt(id) = root {
            let statement = hir.statement(id).ok_or(LowerError::MissingAnchor)?;
            if matches!(
                statement.info.origin,
                h::NodeOrigin::Generated {
                    kind: h::GeneratedKind::StaticSpecialization,
                    ..
                }
            ) {
                let h::StmtKind::Function(function) = &statement.kind else {
                    return Err(LowerError::Correspondence);
                };
                if statement.info.owner != h::LexicalOwner::Module
                    || !function.generics.is_empty()
                    || self.scopes.is_empty()
                {
                    return Err(LowerError::Correspondence);
                }
                // Closed generated declarations use the declaration unit's
                // original module scope. The creation call's local bindings
                // do not become the declaration environment of its defaults.
                let mut builder = Builder {
                    hir,
                    work,
                    visited: BTreeSet::new(),
                    index: std::mem::take(self),
                };
                let result = builder.statement(id, 0, 0);
                *self = builder.index;
                return result;
            }
        }
        if let NodeId::Expr(id) = root {
            let node = hir.expression(id).ok_or(LowerError::Correspondence)?;
            let h::NodeOrigin::Generated {
                anchor: NodeId::Pattern(pattern),
                kind: h::GeneratedKind::PatternValue,
                ..
            } = node.info.origin
            else {
                return Ok(());
            };
            let original = hir.pattern(pattern).ok_or(LowerError::MissingAnchor)?;
            if node.info.owner != original.info.owner {
                return Err(LowerError::Correspondence);
            }
            if let h::ExprKind::Name(name) = &node.kind {
                let h::PatternKind::Name(expected) = &original.kind else {
                    return Err(LowerError::Correspondence);
                };
                charge(work, 1 + name.len().max(expected.len()).div_ceil(32))?;
                if name != expected {
                    return Err(LowerError::Correspondence);
                }
                charge(work, lookup_cost(self.pattern_names.len()))?;
                let target = *self
                    .pattern_names
                    .get(&pattern)
                    .ok_or(LowerError::MissingAnchor)?;
                self.record_name(id, target, work)?;
            }
        }
        Ok(())
    }

    fn record_name(
        &mut self,
        id: ExprId,
        target: NameBinding,
        work: &mut usize,
    ) -> Result<(), LowerError> {
        charge(work, lookup_cost(self.names.len()))?;
        match self.names.entry(id) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(target);
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(_) => Err(LowerError::Correspondence),
        }
    }

    /// None means the original Name has no local pattern binder. An absent
    /// query entry is missing coverage and cannot authorize a guessed binder.
    pub fn lookup(
        &self,
        source: ExprId,
        work: &mut usize,
    ) -> Result<Option<PatternId>, LowerError> {
        charge(work, lookup_cost(self.names.len()))?;
        self.names
            .get(&source)
            .copied()
            .map(|binding| match binding {
                NameBinding::Pattern(id) => Some(id),
                _ => None,
            })
            .ok_or(LowerError::Correspondence)
    }

    /// The original value Name may read a bound static parameter. A value,
    /// type declaration or unknown import with the same spelling blocks it.
    pub fn lookup_generic(
        &self,
        source: ExprId,
        work: &mut usize,
    ) -> Result<Option<GenericParamId>, LowerError> {
        charge(work, lookup_cost(self.names.len()))?;
        self.names
            .get(&source)
            .map(|binding| match binding {
                NameBinding::Generic(id) => Some(*id),
                _ => None,
            })
            .ok_or(LowerError::Correspondence)
    }

    pub fn lookup_type(
        &self,
        source: TypeExprId,
        work: &mut usize,
    ) -> Result<TypeNameBinding, LowerError> {
        charge(work, lookup_cost(self.types.len()))?;
        self.types
            .get(&source)
            .copied()
            .ok_or(LowerError::Correspondence)
    }
}

impl Builder<'_, '_> {
    fn enter(&mut self, node: NodeId, depth: usize) -> Result<(), LowerError> {
        charge(self.work, 1 + lookup_cost(self.visited.len()))?;
        if depth >= 128 {
            return Err(LowerError::Budget("lexical binding depth"));
        }
        if !self.visited.insert(node) {
            return Err(LowerError::Correspondence);
        }
        Ok(())
    }

    fn scope(&mut self, parent: Option<usize>) -> Result<usize, LowerError> {
        charge(self.work, 1)?;
        let id = self.index.scopes.len();
        self.index.scopes.push(Scope {
            parent,
            names: BTreeMap::new(),
            types: BTreeMap::new(),
            generics: BTreeMap::new(),
            longest_name: 0,
            unknown_imports: false,
        });
        Ok(id)
    }

    fn name(&mut self, mut scope: usize, name: &str) -> Result<NameBinding, LowerError> {
        loop {
            let frame = &self.index.scopes[scope];
            charge(
                self.work,
                lookup_cost(frame.names.len())
                    * (1 + name.len().max(frame.longest_name).div_ceil(32)),
            )?;
            if let Some(target) = frame.names.get(name) {
                return Ok(*target);
            }
            if frame.unknown_imports {
                return Ok(NameBinding::Other);
            }
            let Some(parent) = frame.parent else {
                return Ok(NameBinding::Other);
            };
            scope = parent;
        }
    }

    fn type_name(&mut self, mut scope: usize, name: &str) -> Result<TypeNameBinding, LowerError> {
        loop {
            let frame = &self.index.scopes[scope];
            charge(
                self.work,
                3 * lookup_cost(frame.names.len())
                    * (1 + name.len().max(frame.longest_name).div_ceil(32)),
            )?;
            if let Some(binding) = frame.names.get(name) {
                charge(
                    self.work,
                    lookup_cost(frame.types.len()) + lookup_cost(frame.generics.len()),
                )?;
                return Ok(match binding {
                    NameBinding::Generic(id) => TypeNameBinding::Generic(*id),
                    NameBinding::Pattern(_) => TypeNameBinding::Other,
                    NameBinding::Other => frame
                        .types
                        .get(name)
                        .copied()
                        .map_or(TypeNameBinding::Other, TypeNameBinding::Declaration),
                });
            }
            if frame.unknown_imports {
                return Ok(TypeNameBinding::Other);
            }
            let Some(parent) = frame.parent else {
                return Ok(TypeNameBinding::Unbound);
            };
            scope = parent;
        }
    }

    fn generics(
        &mut self,
        parameters: &[GenericParamId],
        scope: usize,
        depth: usize,
    ) -> Result<(), LowerError> {
        charge(self.work, parameters.len())?;
        for id in parameters {
            let parameter = self.hir.generic(*id).ok_or(LowerError::Correspondence)?;
            charge(self.work, 1 + parameter.name.len().div_ceil(32))?;
            self.bind(scope, parameter.name.clone(), None)?;
            charge(
                self.work,
                1 + parameter.name.len().div_ceil(32)
                    + lookup_cost(self.index.scopes[scope].generics.len()),
            )?;
            if self.index.scopes[scope]
                .generics
                .insert(parameter.name.clone(), *id)
                .is_some()
            {
                return Err(LowerError::Correspondence);
            }
            charge(
                self.work,
                lookup_cost(self.index.scopes[scope].names.len())
                    + 1
                    + parameter.name.len().div_ceil(32),
            )?;
            self.index.scopes[scope]
                .names
                .insert(parameter.name.clone(), NameBinding::Generic(*id));
        }
        for id in parameters {
            self.enter(NodeId::Generic(*id), depth)?;
            let parameter = self.hir.generic(*id).ok_or(LowerError::Correspondence)?;
            if let Some(ty) = parameter.bound {
                self.ty(ty, scope, depth + 1)?;
            }
            if let Some(ty) = parameter.default {
                self.ty(ty, scope, depth + 1)?;
            }
        }
        Ok(())
    }

    fn bind(
        &mut self,
        scope: usize,
        name: String,
        target: Option<PatternId>,
    ) -> Result<(), LowerError> {
        let frame = &mut self.index.scopes[scope];
        charge(
            self.work,
            lookup_cost(frame.names.len()) * (1 + name.len().max(frame.longest_name).div_ceil(32)),
        )?;
        if let Some(previous) = frame.names.get(&name) {
            if matches!(previous, NameBinding::Generic(_) | NameBinding::Other) && target.is_none()
            {
                frame.names.insert(name, NameBinding::Other);
                return Ok(());
            }
            return Err(LowerError::Correspondence);
        }
        frame.longest_name = frame.longest_name.max(name.len());
        frame.names.insert(
            name,
            target.map_or(NameBinding::Other, NameBinding::Pattern),
        );
        Ok(())
    }

    fn record_name(&mut self, id: ExprId, target: NameBinding) -> Result<(), LowerError> {
        self.index.record_name(id, target, self.work)
    }

    fn bind_pattern(&mut self, pattern: PatternId, scope: usize) -> Result<(), LowerError> {
        for binding in self.hir.pattern_bindings(pattern, self.work)? {
            self.bind(scope, binding.name, Some(binding.pattern))?;
        }
        Ok(())
    }

    fn declarations(&mut self, items: &[StmtId], scope: usize) -> Result<(), LowerError> {
        charge(self.work, items.len())?;
        for id in items {
            let node = self.hir.statement(*id).ok_or(LowerError::Correspondence)?;
            if matches!(node.kind, h::StmtKind::Use { glob: true, .. }) {
                self.index.scopes[scope].unknown_imports = true;
            }
            let name = match &node.kind {
                h::StmtKind::Function(function) => &function.name,
                h::StmtKind::Type { name, .. } | h::StmtKind::Effect { name, .. } => name,
                _ => continue,
            };
            charge(self.work, 1 + name.len().div_ceil(32))?;
            self.bind(scope, name.clone(), None)?;
            if let h::StmtKind::Type { variants, .. } = &node.kind {
                charge(self.work, 1 + name.len().div_ceil(32))?;
                if self.index.scopes[scope].generics.contains_key(name)
                    || self.index.scopes[scope]
                        .types
                        .insert(name.clone(), *id)
                        .is_some()
                {
                    return Err(LowerError::Correspondence);
                }
                charge(self.work, variants.len())?;
                for variant in variants {
                    charge(self.work, 1 + variant.name.len().div_ceil(32))?;
                    self.bind(scope, variant.name.clone(), None)?;
                }
            }
        }
        Ok(())
    }

    fn sequence(
        &mut self,
        items: &[StmtId],
        helpers: &[StmtId],
        scope: usize,
        depth: usize,
    ) -> Result<(), LowerError> {
        self.declarations(items, scope)?;
        self.declarations(helpers, scope)?;
        charge(self.work, items.len() + helpers.len())?;
        for id in items {
            if !matches!(
                self.hir
                    .statement(*id)
                    .ok_or(LowerError::Correspondence)?
                    .kind,
                h::StmtKind::Function(_) | h::StmtKind::Type { .. } | h::StmtKind::Effect { .. }
            ) {
                self.statement(*id, scope, depth + 1)?;
            }
        }
        // Hoisted helpers resolve against every binding in their block. The
        // dynamic receiver must separately prove that captures are initialized.
        for id in items {
            if matches!(
                self.hir
                    .statement(*id)
                    .ok_or(LowerError::Correspondence)?
                    .kind,
                h::StmtKind::Function(_) | h::StmtKind::Type { .. } | h::StmtKind::Effect { .. }
            ) {
                self.statement(*id, scope, depth + 1)?;
            }
        }
        for id in helpers {
            self.statement(*id, scope, depth + 1)?;
        }
        Ok(())
    }

    fn block(&mut self, block: &h::Block, parent: usize, depth: usize) -> Result<(), LowerError> {
        let scope = self.scope(Some(parent))?;
        self.sequence(&block.statements, &block.where_items, scope, depth + 1)
    }

    fn parameters(
        &mut self,
        parameters: &[h::Parameter],
        scope: usize,
        depth: usize,
    ) -> Result<(), LowerError> {
        charge(self.work, parameters.len())?;
        for parameter in parameters {
            if let Some(ty) = parameter.ty {
                self.ty(ty, scope, depth + 1)?;
            }
            if let Some(default) = parameter.default {
                self.expression(default, scope, depth + 1)?;
            }
            self.pattern(parameter.pattern, scope, depth + 1)?;
            self.bind_pattern(parameter.pattern, scope)?;
        }
        Ok(())
    }

    fn statement(&mut self, id: StmtId, scope: usize, depth: usize) -> Result<(), LowerError> {
        self.enter(NodeId::Stmt(id), depth)?;
        let node = self.hir.statement(id).ok_or(LowerError::Correspondence)?;
        match &node.kind {
            h::StmtKind::Binding {
                pattern,
                ty,
                value,
                fallback,
                ..
            } => {
                if let Some(ty) = ty {
                    self.ty(*ty, scope, depth + 1)?;
                }
                self.expression(*value, scope, depth + 1)?;
                self.pattern(*pattern, scope, depth + 1)?;
                if let Some(fallback) = fallback {
                    self.expression(*fallback, scope, depth + 1)?;
                }
                self.bind_pattern(*pattern, scope)?;
            }
            h::StmtKind::Function(function) => {
                let local = self.scope(Some(scope))?;
                self.generics(&function.generics, local, depth + 1)?;
                self.declarations(&function.signature_where, local)?;
                self.parameters(&function.parameters, local, depth + 1)?;
                if let Some(ty) = function.return_type {
                    self.ty(ty, local, depth + 1)?;
                }
                for helper in &function.signature_where {
                    self.statement(*helper, local, depth + 1)?;
                }
                if let Some(body) = &function.body {
                    self.block(body, local, depth + 1)?;
                }
            }
            h::StmtKind::Type {
                generics,
                value,
                variants,
                ..
            } => {
                let local = self.scope(Some(scope))?;
                self.generics(generics, local, depth + 1)?;
                if let Some(ty) = value {
                    self.ty(*ty, local, depth + 1)?;
                }
                for variant in variants {
                    charge(self.work, 1)?;
                    let variant_scope = self.scope(Some(local))?;
                    self.generics(&variant.generics, variant_scope, depth + 1)?;
                    if let Some(ty) = variant.payload {
                        self.ty(ty, variant_scope, depth + 1)?;
                    }
                    if let Some(ty) = variant.result {
                        self.ty(ty, variant_scope, depth + 1)?;
                    }
                }
            }
            h::StmtKind::Effect {
                generics,
                operations,
                members,
                ..
            } => {
                let local = self.scope(Some(scope))?;
                self.generics(generics, local, depth + 1)?;
                for operation in operations {
                    self.statement(*operation, local, depth + 1)?;
                }
                for member in members {
                    self.ty(*member, local, depth + 1)?;
                }
            }
            h::StmtKind::Handler(arms) => {
                charge(self.work, arms.len())?;
                for arm in arms {
                    self.expression(arm.operation, scope, depth + 1)?;
                    let local = self.scope(Some(scope))?;
                    self.parameters(&arm.parameters, local, depth + 1)?;
                    self.expression(arm.body, local, depth + 1)?;
                }
            }
            h::StmtKind::Assignment { target, value, .. } => {
                self.expression(*target, scope, depth + 1)?;
                self.expression(*value, scope, depth + 1)?;
            }
            h::StmtKind::HandlerApplication(expression) | h::StmtKind::Expr { expression, .. } => {
                self.expression(*expression, scope, depth + 1)?
            }
            h::StmtKind::Use {
                alias,
                members,
                path,
                glob,
                ..
            } => {
                charge(self.work, members.len() + path.len())?;
                if *glob {
                    self.index.scopes[scope].unknown_imports = true;
                    return Ok(());
                }
                if members.is_empty() {
                    if let Some(name) = alias.as_ref().or_else(|| path.last()) {
                        charge(self.work, 1 + name.len().div_ceil(32))?;
                        self.bind(scope, name.clone(), None)?;
                    }
                } else {
                    for member in members {
                        let name = member.alias.as_ref().unwrap_or(&member.name);
                        charge(self.work, 1 + name.len().div_ceil(32))?;
                        self.bind(scope, name.clone(), None)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn pattern(&mut self, id: PatternId, scope: usize, depth: usize) -> Result<(), LowerError> {
        self.enter(NodeId::Pattern(id), depth)?;
        let node = self.hir.pattern(id).ok_or(LowerError::Correspondence)?;
        match &node.kind {
            h::PatternKind::Name(name) => {
                let binding = self.name(scope, name)?;
                charge(self.work, lookup_cost(self.index.pattern_names.len()))?;
                if self.index.pattern_names.insert(id, binding).is_some() {
                    return Err(LowerError::Correspondence);
                }
            }
            h::PatternKind::Mode { pattern, .. } => self.pattern(*pattern, scope, depth + 1)?,
            h::PatternKind::Tuple(items) | h::PatternKind::Alternative(items) => {
                for item in items {
                    self.pattern(*item, scope, depth + 1)?;
                }
            }
            h::PatternKind::Record { fields, ty, .. } => {
                if let Some(ty) = ty {
                    self.ty(*ty, scope, depth + 1)?;
                }
                for field in fields {
                    self.pattern(field.pattern, scope, depth + 1)?;
                }
            }
            h::PatternKind::Constructor { arguments, .. } => {
                for argument in arguments {
                    self.pattern(*argument, scope, depth + 1)?;
                }
            }
            h::PatternKind::Value(expression) => self.expression(*expression, scope, depth + 1)?,
            h::PatternKind::Type { ty, .. } => self.ty(*ty, scope, depth + 1)?,
            _ => {}
        }
        Ok(())
    }

    fn expression(&mut self, id: ExprId, scope: usize, depth: usize) -> Result<(), LowerError> {
        self.enter(NodeId::Expr(id), depth)?;
        let node = self.hir.expression(id).ok_or(LowerError::Correspondence)?;
        match &node.kind {
            h::ExprKind::Name(name) => {
                let binding = self.name(scope, name)?;
                self.record_name(id, binding)?;
            }
            h::ExprKind::Block(block) | h::ExprKind::Loop(block) => {
                self.block(block, scope, depth + 1)?
            }
            h::ExprKind::Lambda {
                parameters,
                return_type,
                body,
                ..
            } => {
                let local = self.scope(Some(scope))?;
                self.parameters(parameters, local, depth + 1)?;
                if let Some(ty) = return_type {
                    self.ty(*ty, local, depth + 1)?;
                }
                self.expression(*body, local, depth + 1)?;
            }
            h::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression(*condition, scope, depth + 1)?;
                let yes = self.condition_scope(*condition, true, scope, depth + 1)?;
                self.expression(*then_branch, yes, depth + 1)?;
                if let Some(other) = else_branch {
                    let no = self.condition_scope(*condition, false, scope, depth + 1)?;
                    self.expression(*other, no, depth + 1)?;
                }
            }
            h::ExprKind::Match { value, arms, .. } => {
                self.expression(*value, scope, depth + 1)?;
                charge(self.work, arms.len())?;
                for arm in arms {
                    self.pattern(arm.pattern, scope, depth + 1)?;
                    let local = self.scope(Some(scope))?;
                    self.bind_pattern(arm.pattern, local)?;
                    if let Some(guard) = arm.guard {
                        self.expression(guard, local, depth + 1)?;
                    }
                    self.expression(arm.body, local, depth + 1)?;
                }
            }
            h::ExprKind::Is { value, pattern } => {
                self.expression(*value, scope, depth + 1)?;
                self.pattern(*pattern, scope, depth + 1)?;
            }
            h::ExprKind::While { condition, body } => {
                self.expression(*condition, scope, depth + 1)?;
                let local = self.condition_scope(*condition, true, scope, depth + 1)?;
                self.block(body, local, depth + 1)?;
            }
            h::ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expression(*iterable, scope, depth + 1)?;
                self.pattern(*pattern, scope, depth + 1)?;
                let local = self.scope(Some(scope))?;
                self.bind_pattern(*pattern, local)?;
                self.block(body, local, depth + 1)?;
            }
            h::ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                self.expression(*left, scope, depth + 1)?;
                let right_scope = match operator.as_str() {
                    "&&" => self.condition_scope(*left, true, scope, depth + 1)?,
                    "||" => self.condition_scope(*left, false, scope, depth + 1)?,
                    _ => scope,
                };
                self.expression(*right, right_scope, depth + 1)?;
            }
            _ => {
                for child in self.children(NodeId::Expr(id))? {
                    charge(self.work, 1)?;
                    match child {
                        NodeId::Expr(child) => self.expression(child, scope, depth + 1)?,
                        NodeId::Type(ty) => self.ty(ty, scope, depth + 1)?,
                        _ => return Err(LowerError::Correspondence),
                    }
                }
            }
        }
        Ok(())
    }

    fn condition_scope(
        &mut self,
        expression: ExprId,
        truth: bool,
        parent: usize,
        depth: usize,
    ) -> Result<usize, LowerError> {
        let bindings = self.condition_bindings(expression, truth, depth + 1)?;
        if bindings.is_empty() {
            return Ok(parent);
        }
        let scope = self.scope(Some(parent))?;
        for (name, binding) in bindings {
            self.bind(scope, name, binding)?;
        }
        Ok(scope)
    }

    fn condition_bindings(
        &mut self,
        expression: ExprId,
        truth: bool,
        depth: usize,
    ) -> Result<Bindings, LowerError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(LowerError::Budget("lexical condition depth"));
        }
        let node = self
            .hir
            .expression(expression)
            .ok_or(LowerError::Correspondence)?;
        match &node.kind {
            h::ExprKind::Is { pattern, .. } if truth => {
                let mut bindings = BTreeMap::new();
                for binding in self.hir.pattern_bindings(*pattern, self.work)? {
                    charge(self.work, 1)?;
                    bindings.insert(binding.name, Some(binding.pattern));
                }
                Ok(bindings)
            }
            h::ExprKind::Unary { operator, operand } if operator == "!" => {
                self.condition_bindings(*operand, !truth, depth + 1)
            }
            // A conjunction's true path introduces both sets. Ambiguous names
            // remain a shadowing barrier rather than selecting either binder.
            h::ExprKind::Binary {
                operator,
                left,
                right,
            } if (operator == "&&" && truth) || (operator == "||" && !truth) => {
                let mut bindings = self.condition_bindings(*left, truth, depth + 1)?;
                for (name, binding) in self.condition_bindings(*right, truth, depth + 1)? {
                    charge(
                        self.work,
                        lookup_cost(bindings.len()) * (1 + name.len().div_ceil(32)),
                    )?;
                    bindings
                        .entry(name)
                        .and_modify(|previous| {
                            if *previous != binding {
                                *previous = None;
                            }
                        })
                        .or_insert(binding);
                }
                Ok(bindings)
            }
            h::ExprKind::Binary { operator, .. } if operator == "&&" || operator == "||" => {
                // Different paths may introduce different lexical binders. A
                // single PatternId cannot certify such a name; retain a barrier
                // for every possible introduced name instead of choosing outer.
                let mut bindings = BTreeMap::new();
                self.ambiguous_condition_bindings(expression, &mut bindings, depth + 1)?;
                Ok(bindings)
            }
            _ => Ok(BTreeMap::new()),
        }
    }

    fn ambiguous_condition_bindings(
        &mut self,
        expression: ExprId,
        bindings: &mut Bindings,
        depth: usize,
    ) -> Result<(), LowerError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(LowerError::Budget("lexical condition depth"));
        }
        match &self
            .hir
            .expression(expression)
            .ok_or(LowerError::Correspondence)?
            .kind
        {
            h::ExprKind::Is { pattern, .. } => {
                for binding in self.hir.pattern_bindings(*pattern, self.work)? {
                    charge(
                        self.work,
                        lookup_cost(bindings.len()) * (1 + binding.name.len().div_ceil(32)),
                    )?;
                    bindings.insert(binding.name, None);
                }
            }
            h::ExprKind::Unary { operator, operand } if operator == "!" => {
                self.ambiguous_condition_bindings(*operand, bindings, depth + 1)?
            }
            h::ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "&&" || operator == "||" => {
                self.ambiguous_condition_bindings(*left, bindings, depth + 1)?;
                self.ambiguous_condition_bindings(*right, bindings, depth + 1)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn ty(&mut self, id: TypeExprId, scope: usize, depth: usize) -> Result<(), LowerError> {
        self.enter(NodeId::Type(id), depth)?;
        let node = self
            .hir
            .type_expression(id)
            .ok_or(LowerError::Correspondence)?;
        if let h::TypeKind::Name { path, .. } = &node.kind {
            charge(self.work, path.len() + 1)?;
            for segment in path {
                charge(self.work, 1 + segment.len().div_ceil(32))?;
            }
            let name = path.join("::");
            let binding = self.type_name(scope, &name)?;
            charge(self.work, lookup_cost(self.index.types.len()))?;
            if self.index.types.insert(id, binding).is_some() {
                return Err(LowerError::Correspondence);
            }
        }
        if let h::TypeKind::Callable {
            parameters, result, ..
        } = &node.kind
        {
            let local = self.scope(Some(scope))?;
            self.parameters(parameters, local, depth + 1)?;
            if let Some(ty) = result {
                self.ty(*ty, local, depth + 1)?;
            }
        } else if let h::TypeKind::TypeFunction { parameters, body } = &node.kind {
            let local = self.scope(Some(scope))?;
            self.generics(parameters, local, depth + 1)?;
            self.expression(*body, local, depth + 1)?;
        } else if let h::TypeKind::Mapped {
            binder,
            keys,
            value,
            ..
        } = &node.kind
        {
            self.expression(*keys, scope, depth + 1)?;
            let local = self.scope(Some(scope))?;
            charge(self.work, 1 + binder.len().div_ceil(32))?;
            self.bind(local, binder.clone(), None)?;
            self.ty(*value, local, depth + 1)?;
        } else {
            for child in self.children(NodeId::Type(id))? {
                charge(self.work, 1)?;
                match child {
                    NodeId::Expr(expression) => self.expression(expression, scope, depth + 1)?,
                    NodeId::Type(ty) => self.ty(ty, scope, depth + 1)?,
                    NodeId::Generic(_) => {}
                    _ => return Err(LowerError::Correspondence),
                }
            }
        }
        Ok(())
    }

    fn children(&mut self, node: NodeId) -> Result<Vec<NodeId>, LowerError> {
        self.hir
            .children_with_work(node, self.work)
            .map_err(|error| match error {
                h::WalkError::Budget => LowerError::Budget("lexical child frontier"),
                h::WalkError::MissingNode(_) => LowerError::Correspondence,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(case: &str) -> HirProgram {
        let mut parsed = ril_syntax::parse(ril_test::case_source(case));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        HirProgram::lower_identified(&mut parsed.program, h::InputOrigin::Source).unwrap()
    }

    fn function(hir: &HirProgram, statement: StmtId) -> &h::Function {
        let h::StmtKind::Function(function) = &hir.statement(statement).unwrap().kind else {
            panic!("original function declaration")
        };
        function
    }

    fn binding(hir: &HirProgram, statement: StmtId) -> (PatternId, ExprId) {
        let h::StmtKind::Binding { pattern, value, .. } = hir.statement(statement).unwrap().kind
        else {
            panic!("original binding declaration")
        };
        (pattern, value)
    }

    fn tail(hir: &HirProgram, block: &h::Block) -> ExprId {
        let h::StmtKind::Expr { expression, .. } = hir
            .statement(*block.statements.last().unwrap())
            .unwrap()
            .kind
        else {
            panic!("original expression statement")
        };
        expression
    }

    #[test]
    fn nested_shadowing_uses_the_outer_initializer_and_the_inner_block_tail() {
        let hir = fixture("tests/conformance/numeric.ril::lexical-numeric-shadow");
        let block = function(&hir, hir.roots()[0]).body.as_ref().unwrap();
        let (outer, _) = binding(&hir, block.statements[0]);
        let (_, before) = binding(&hir, block.statements[1]);
        let (_, nested) = binding(&hir, block.statements[2]);
        let h::ExprKind::Block(inner_block) = &hir.expression(nested).unwrap().kind else {
            unreachable!()
        };
        let (inner, initializer) = binding(&hir, inner_block.statements[0]);
        let h::ExprKind::Binary { left, .. } = hir.expression(initializer).unwrap().kind else {
            unreachable!()
        };
        let index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        assert_ne!(outer, inner);
        assert_eq!(index.lookup(before, &mut 4096).unwrap(), Some(outer));
        assert_eq!(index.lookup(left, &mut 4096).unwrap(), Some(outer));
        assert_eq!(
            index.lookup(tail(&hir, inner_block), &mut 4096).unwrap(),
            Some(inner)
        );
        let h::ExprKind::Call { arguments, .. } = &hir.expression(tail(&hir, block)).unwrap().kind
        else {
            unreachable!()
        };
        let h::ExprKind::Binary { left, .. } = hir.expression(arguments[0].value).unwrap().kind
        else {
            unreachable!()
        };
        assert_eq!(index.lookup(left, &mut 4096).unwrap(), Some(outer));
    }

    #[test]
    fn a_hoisted_helper_resolves_the_later_binding_in_its_enclosing_block() {
        let hir = fixture("tests/conformance/numeric.ril::hoisted-numeric-capture");
        let block = function(&hir, hir.roots()[0]).body.as_ref().unwrap();
        let (outer, _) = binding(&hir, block.statements[0]);
        let helper = function(&hir, block.where_items[0]);
        let reading = tail(&hir, helper.body.as_ref().unwrap());
        let index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        assert_eq!(index.lookup(reading, &mut 4096).unwrap(), Some(outer));
    }

    #[test]
    fn a_signature_type_alias_shadows_the_outer_type_declaration() {
        let hir = fixture("tests/conformance/numeric.ril::shadowed-alias-pattern-safe");
        let outer = hir.roots()[0];
        let function = function(&hir, hir.roots()[1]);
        let inner = function.signature_where[0];
        let index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let reference = function.parameters[0].ty.unwrap();
        assert_ne!(outer, inner);
        assert_eq!(
            index.lookup_type(reference, &mut 4096).unwrap(),
            TypeNameBinding::Declaration(inner)
        );
        let h::StmtKind::Type {
            value: Some(primitive),
            ..
        } = hir.statement(inner).unwrap().kind
        else {
            unreachable!()
        };
        assert_eq!(
            index.lookup_type(primitive, &mut 4096).unwrap(),
            TypeNameBinding::Unbound
        );
        assert!(matches!(
            index.lookup_type(reference, &mut 0),
            Err(LowerError::Budget(_))
        ));
        assert!(index.lookup_type(TypeExprId(u32::MAX), &mut 4096).is_err());
    }

    #[test]
    fn same_spelled_type_parameters_keep_their_original_generic_ids() {
        let hir = fixture("tests/conformance/numeric.ril::deferred-arithmetic-safe");
        let index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let identity = function(&hir, hir.roots()[0]);
        let choose = function(&hir, hir.roots()[1]);
        assert_ne!(identity.generics[0], choose.generics[0]);
        for function in [identity, choose] {
            let expected = TypeNameBinding::Generic(function.generics[0]);
            assert_eq!(
                index
                    .lookup_type(function.parameters[0].ty.unwrap(), &mut 4096)
                    .unwrap(),
                expected
            );
            assert_eq!(
                index
                    .lookup_type(function.return_type.unwrap(), &mut 4096)
                    .unwrap(),
                expected
            );
        }
    }

    fn generated_value(
        hir: &mut HirProgram,
        pattern: PatternId,
        kind: ril_syntax::ast::ExprKind,
        owner: h::LexicalOwner,
    ) -> ExprId {
        let expression = ril_syntax::ast::Expr {
            hir_id: None,
            span: hir.pattern(pattern).unwrap().info.span,
            kind,
        };
        hir.mint_generated_expr(
            &expression,
            NodeId::Pattern(pattern),
            h::GeneratedKind::PatternValue,
            owner,
            h::HirLimits::default(),
        )
        .unwrap()
    }

    #[test]
    fn appended_pattern_values_keep_the_environment_before_the_original_binding() {
        let mut hir = fixture("tests/conformance/numeric.ril::lexical-numeric-shadow");
        let block = function(&hir, hir.roots()[0]).body.as_ref().unwrap();
        let (outer, _) = binding(&hir, block.statements[0]);
        let (_, nested) = binding(&hir, block.statements[2]);
        let h::ExprKind::Block(inner) = &hir.expression(nested).unwrap().kind else {
            unreachable!()
        };
        let (pattern, _) = binding(&hir, inner.statements[0]);
        let owner = hir.pattern(pattern).unwrap().info.owner;
        let original = hir.clone();
        let mut index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let generated = generated_value(
            &mut hir,
            pattern,
            ril_syntax::ast::ExprKind::Name("number".into()),
            owner,
        );
        assert!(index.lookup(generated, &mut 4096).is_err());
        assert!(matches!(
            index.refresh_generated(&hir, &mut 0),
            Err(LowerError::Budget(_))
        ));
        assert!(index.lookup(generated, &mut 4096).is_err());
        let mut work = 4096;
        index.refresh_generated(&hir, &mut work).unwrap();
        let cost = 4096 - work;
        assert_eq!(index.lookup(generated, &mut 4096).unwrap(), Some(outer));
        // A successful prefix is not rescanned or rebound on later queries.
        index.refresh_generated(&hir, &mut 1).unwrap();
        let mut exact = LexicalBindings::new(&original, &mut 4_000_000).unwrap();
        exact.refresh_generated(&hir, &mut { cost }).unwrap();
        let mut short = LexicalBindings::new(&original, &mut 4_000_000).unwrap();
        assert!(matches!(
            short.refresh_generated(&hir, &mut { cost - 1 }),
            Err(LowerError::Budget(_))
        ));
        assert!(short.lookup(generated, &mut 4096).is_err());
        assert!(index.refresh_generated(&original, &mut 4096).is_err());
        let wrong = generated_value(
            &mut hir,
            pattern,
            ril_syntax::ast::ExprKind::Name("another".into()),
            owner,
        );
        assert!(index.refresh_generated(&hir, &mut 4096).is_err());
        assert!(index.lookup(wrong, &mut 4096).is_err());
        assert_eq!(index.lookup(generated, &mut 4096).unwrap(), Some(outer));
    }

    #[test]
    fn appended_scalar_roots_need_only_constant_work_and_names_cannot_change_owner() {
        let mut hir = fixture("tests/conformance/numeric.ril::pattern-literal-occurrences");
        let classify = function(&hir, hir.roots()[0]);
        let root = tail(&hir, classify.body.as_ref().unwrap());
        let h::ExprKind::Match { arms, .. } = &hir.expression(root).unwrap().kind else {
            unreachable!()
        };
        let pattern = arms[0].pattern;
        let original = hir.pattern(pattern).unwrap();
        let h::PatternKind::Literal(literal) = &original.kind else {
            unreachable!()
        };
        let literal = literal.clone();
        let owner = original.info.owner;
        let mut index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        for _ in 0..256 {
            generated_value(
                &mut hir,
                pattern,
                ril_syntax::ast::ExprKind::Literal(literal.clone()),
                owner,
            );
            index.refresh_generated(&hir, &mut 3).unwrap();
        }
        let wrong_owner = generated_value(
            &mut hir,
            pattern,
            ril_syntax::ast::ExprKind::Literal(literal),
            h::LexicalOwner::Module,
        );
        assert!(index.refresh_generated(&hir, &mut 4096).is_err());
        assert!(index.lookup(wrong_owner, &mut 4096).is_err());
    }

    #[test]
    fn generated_closed_function_headers_and_defaults_have_their_own_lexical_ids() {
        let mut hir = fixture("tests/conformance/numeric.ril::external-const-floating-defaults");
        let mut index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let root = function(&hir, hir.roots()[1]).body.as_ref().unwrap();
        let (_, call) = binding(&hir, root.statements[0]);
        let h::ExprKind::Call { callee, .. } = hir.expression(call).unwrap().kind else {
            unreachable!()
        };
        let case =
            ril_test::case_by_id("tests/conformance/numeric.ril::external-const-floating-defaults");
        let declarations = case
            .files
            .iter()
            .find(|file| file.name == "api.d.ril")
            .unwrap();
        let mut parsed = ril_syntax::parse(std::str::from_utf8(&declarations.bytes).unwrap());
        let mut statement = parsed.program.statements.remove(0);
        let ril_syntax::ast::StmtKind::Function(concrete) = &mut statement.kind else {
            unreachable!()
        };
        concrete.name = "specialized".into();
        concrete.generics.clear();
        concrete.parameters[0].default = None;
        let mut second = concrete.parameters[0].clone();
        second.pattern.kind = ril_syntax::ast::PatternKind::Name("second".into());
        second.default = Some(ril_syntax::ast::Expr {
            hir_id: None,
            span: second.span,
            kind: ril_syntax::ast::ExprKind::Name("number".into()),
        });
        concrete.parameters.push(second);
        let id = hir
            .mint_generated_identified_statement(
                &mut statement,
                NodeId::Expr(callee),
                h::GeneratedKind::StaticSpecialization,
                h::LexicalOwner::Module,
                h::HirLimits::default(),
            )
            .unwrap();
        index.refresh_generated(&hir, &mut 4_000_000).unwrap();
        let generated = function(&hir, id);
        assert_eq!(
            index
                .lookup(generated.parameters[1].default.unwrap(), &mut 4096,)
                .unwrap(),
            Some(generated.parameters[0].pattern)
        );
        assert_eq!(
            index
                .lookup_type(generated.parameters[0].ty.unwrap(), &mut 4096,)
                .unwrap(),
            TypeNameBinding::Unbound
        );
        assert_eq!(
            index
                .lookup_type(generated.return_type.unwrap(), &mut 4096,)
                .unwrap(),
            TypeNameBinding::Unbound
        );
        assert_eq!(
            hir.type_expression(generated.return_type.unwrap())
                .unwrap()
                .info
                .owner,
            h::LexicalOwner::Declaration(id)
        );
    }

    #[test]
    fn lexical_index_and_queries_cannot_publish_unpaid_or_missing_bindings() {
        let hir = fixture("tests/conformance/numeric.ril::lexical-numeric-shadow");
        assert!(matches!(
            LexicalBindings::new(&hir, &mut 0),
            Err(LowerError::Budget(_))
        ));
        let mut work = 4_000_000;
        let index = LexicalBindings::new(&hir, &mut work).unwrap();
        let cost = 4_000_000 - work;
        assert!(LexicalBindings::new(&hir, &mut { cost }).is_ok());
        assert!(matches!(
            LexicalBindings::new(&hir, &mut { cost - 1 }),
            Err(LowerError::Budget(_))
        ));
        let (_, reading) = binding(
            &hir,
            function(&hir, hir.roots()[0])
                .body
                .as_ref()
                .unwrap()
                .statements[1],
        );
        assert!(matches!(
            index.lookup(reading, &mut 0),
            Err(LowerError::Budget(_))
        ));
        assert!(index.lookup(ExprId(u32::MAX), &mut 4096).is_err());
    }

    #[test]
    fn value_names_keep_their_actual_generic_parameter_id_without_changing_pattern_lookup() {
        let source = ril_test::case_source("tests/conformance/static.ril::accept-key-membership")
            .replace("record.(key)", "record.(K)");
        let mut parsed = ril_syntax::parse(&source);
        assert!(parsed.is_ok());
        let mut sibling = parsed.program.statements[0].clone();
        let ril_syntax::ast::StmtKind::Function(function) = &mut sibling.kind else {
            unreachable!()
        };
        function.name = "other_get_field".into();
        parsed.program.statements.push(sibling);
        let hir =
            HirProgram::lower_identified(&mut parsed.program, h::InputOrigin::Source).unwrap();
        let index = LexicalBindings::new(&hir, &mut 4_000_000).unwrap();
        let mut selected = BTreeSet::new();
        for statement in hir.roots() {
            let h::StmtKind::Function(function) = &hir.statement(*statement).unwrap().kind else {
                continue;
            };
            if function.generics.len() != 2 {
                continue;
            }
            let h::StmtKind::Expr { expression, .. } = hir
                .statement(function.body.as_ref().unwrap().statements[0])
                .unwrap()
                .kind
            else {
                unreachable!()
            };
            let h::ExprKind::ComputedField { key, .. } = hir.expression(expression).unwrap().kind
            else {
                unreachable!()
            };
            let generic = index.lookup_generic(key, &mut 4096).unwrap().unwrap();
            assert_eq!(generic, function.generics[1]);
            assert_eq!(index.lookup(key, &mut 4096).unwrap(), None);
            assert!(index.lookup_generic(key, &mut 0).is_err());
            selected.insert(generic);
        }
        assert_eq!(
            selected.len(),
            2,
            "same-spelled K parameters retain distinct HIR identities"
        );
        assert!(index.lookup_generic(ExprId(u32::MAX), &mut 4096).is_err());
    }
}
