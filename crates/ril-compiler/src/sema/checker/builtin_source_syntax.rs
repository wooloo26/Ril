//! One frozen lexical source walk. Only syntax is indexed; caller facts and
//! builtin summary obligations are checked separately for every observation.
use super::*;
use crate::hir::nodes::{self as hir, NodeId as SyntaxId};
use ril_compiler_core::ids::{DefinitionId, ExprId, StmtId};

struct Candidate {
    source: Option<SyntaxId>,
    owner: CallableOwner,
    name: String,
    shadowed: bool,
}

pub(crate) struct NameIndex<'a> {
    facts: &'a SemanticFacts,
    candidates: BTreeMap<SyntaxId, Vec<Candidate>>,
}

fn name_work(work: &mut usize, units: usize) -> Result<(), String> {
    *work = work
        .checked_sub(units)
        .ok_or("builtin lexical Source exceeds its shared work bound")?;
    Ok(())
}

type DeclarationOwners = BTreeMap<(CallableOwner, StmtId), DefinitionId>;

fn declaration_owners(
    facts: &SemanticFacts,
    work: &mut usize,
) -> Result<DeclarationOwners, String> {
    let mut owners = BTreeMap::new();
    let mut definitions = BTreeMap::new();
    name_work(work, 1 + facts.functions.len())?;
    for info in &facts.functions {
        let (Some(parent), Some(source)) = (info.lexical_owner, info.hir_id) else {
            continue;
        };
        name_work(
            work,
            2 + owners.len().checked_ilog2().unwrap_or(0) as usize
                + definitions.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let original = facts
            .semantic_hir
            .as_deref()
            .and_then(|hir| hir.statement(source))
            .ok_or("builtin function owner has no canonical declaration")?;
        let hir::StmtKind::Function(function) = &original.kind else {
            return Err("builtin function owner names a non-function declaration".into());
        };
        name_work(work, 2 + info.syntax.name.len() + function.name.len())?;
        if info.syntax.name != function.name {
            return Err("builtin function owner changed its canonical name".into());
        }
        if owners
            .insert((parent, source), info.definition)
            .is_some_and(|previous| previous != info.definition)
            || definitions
                .insert((parent, info.definition), source)
                .is_some_and(|previous| previous != source)
        {
            return Err("builtin function owner has ambiguous declaration identities".into());
        }
    }
    Ok(owners)
}

impl<'a> NameIndex<'a> {
    pub(crate) fn new_with_work(
        facts: &'a SemanticFacts,
        work: &mut usize,
    ) -> Result<Self, String> {
        name_work(work, 1)?;
        let program = facts
            .source_program
            .as_deref()
            .ok_or("builtin source has no frozen actual Program")?;
        let owners = declaration_owners(facts, work)?;
        let mut walker = Walk {
            facts,
            owners,
            work,
            found: Vec::new(),
        };
        walker.statements(&program.statements, CallableOwner::Global, 0, 0)?;
        let mut candidates = BTreeMap::<_, Vec<_>>::new();
        for candidate in walker.found {
            if let Some(source) = candidate.source {
                name_work(
                    walker.work,
                    2 + candidates.len().checked_ilog2().unwrap_or(0) as usize,
                )?;
                candidates.entry(source).or_default().push(candidate);
            }
        }
        Ok(Self { facts, candidates })
    }

    pub(crate) fn needs_preparation(
        facts: &SemanticFacts,
        work: &mut usize,
    ) -> Result<bool, String> {
        name_work(work, 1)?;
        if !facts.builtin_source_observations.is_empty() {
            return Ok(true);
        }
        name_work(work, facts.expressions.len())?;
        for fact in &facts.expressions {
            name_work(work, fact.value.callables.len())?;
            for callable in &fact.value.callables {
                let name = match callable {
                    Callable::Builtin(name) | Callable::Constructor(name) => name,
                    _ => continue,
                };
                name_work(work, 1 + name.len())?;
                if matches!(
                    name.strip_prefix("Prelude::").unwrap_or(name),
                    "Some" | "Ok" | "Err" | "None" | "clone" | "clone_immut"
                ) || builtin_bit(name) != 0
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// Cheap applicability only. It does not authenticate lexical resolution,
    /// a physical observation, or any previously checked declaration.
    pub(crate) fn is_candidate(actual: &Expr, work: &mut usize) -> Result<bool, String> {
        name_work(work, 1)?;
        Ok(match &actual.kind {
            ExprKind::Name(name) => {
                name_work(work, 1 + name.len())?;
                builtin_bit(name) != 0
            }
            ExprKind::Path(path) if path.len() <= 3 && path.iter().all(|part| part.len() <= 64) => {
                name_work(work, 1 + path.len() * 2)?;
                for part in path {
                    name_work(work, 1 + part.len())?;
                }
                builtin_bit(&path.join("::")) != 0
            }
            _ => false,
        })
    }

    pub(crate) fn matches_facts(&self, facts: &SemanticFacts) -> bool {
        std::ptr::eq(self.facts, facts)
    }

    fn candidate(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
        work: &mut usize,
    ) -> Result<&Candidate, String> {
        name_work(
            work,
            2 + self.candidates.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("builtin source has no HIR")?;
        let node = hir
            .expression(source)
            .ok_or("builtin source HIR is absent")?;
        if let hir::ExprKind::Name(name) = &node.kind {
            name_work(work, 1 + name.len())?;
        }
        if let hir::ExprKind::Path(path) = &node.kind {
            name_work(work, path.len())?;
            for part in path {
                name_work(work, 1 + part.len())?;
            }
        }
        let source = match node.info.origin {
            hir::NodeOrigin::Generated {
                anchor: SyntaxId::Pattern(id),
                kind: hir::GeneratedKind::PatternValue,
                ..
            } => {
                let pattern = hir
                    .pattern(id)
                    .ok_or("builtin value-test anchor is absent")?;
                let original = match (&pattern.kind, &node.kind) {
                    (hir::PatternKind::Name(actual), hir::ExprKind::Name(name)) => actual == name,
                    (
                        hir::PatternKind::Constructor {
                            path,
                            arguments,
                            parenthesized,
                        },
                        hir::ExprKind::Path(actual),
                    ) => path == actual && arguments.is_empty() && !parenthesized,
                    _ => false,
                };
                if !original || pattern.info.owner != node.info.owner {
                    return Err("builtin value-test name changed its original HIR pattern".into());
                }
                SyntaxId::Pattern(id)
            }
            _ => SyntaxId::Expr(source),
        };
        let values = self
            .candidates
            .get(&source)
            .ok_or("builtin source has no actual HIR name")?;
        let [candidate] = values.as_slice() else {
            return Err("builtin source repeats a static HIR identity".into());
        };
        if Some(candidate.owner) != owner {
            return Err("builtin source borrowed another lexical owner".into());
        }
        Ok(candidate)
    }

    pub(crate) fn direct_identity(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
        work: &mut usize,
    ) -> Result<Option<String>, String> {
        name_work(work, 1)?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("builtin source has no HIR")?;
        let node = hir
            .expression(source)
            .ok_or("builtin source HIR is absent")?;
        match &node.kind {
            hir::ExprKind::Name(name) => name_work(work, 1 + name.len())?,
            hir::ExprKind::Path(path) => {
                name_work(
                    work,
                    path.len()
                        .checked_mul(2)
                        .ok_or("builtin path work overflow")?,
                )?;
                for part in path {
                    name_work(work, 1 + part.len())?;
                }
            }
            _ => {}
        }
        let name = match &node.kind {
            crate::hir::nodes::ExprKind::Name(name) if builtin_bit(name) != 0 => name.clone(),
            crate::hir::nodes::ExprKind::Path(path)
                if path.len() <= 3 && path.iter().all(|part| part.len() <= 64) =>
            {
                path.join("::")
            }
            _ => return Ok(None),
        };
        if builtin_bit(&name) == 0 {
            return Ok(None);
        }
        let candidate = self.candidate(owner, source, work)?;
        if candidate.name != name {
            return Err("builtin reference differs from its original HIR name".into());
        }
        name_work(work, 1 + candidate.name.len())?;
        Ok((!candidate.shadowed && builtin_bit(&candidate.name) != 0)
            .then(|| candidate.name.clone()))
    }

    pub(crate) fn actual_name(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
        name: &str,
        work: &mut usize,
    ) -> Result<(), String> {
        name_work(work, 1 + name.len())?;
        if self.direct_identity(owner, source, work)?.as_deref() == Some(name) {
            return Ok(());
        }
        Err(
            "builtin source has no unique unshadowed canonical Name in its real lexical owner"
                .into(),
        )
    }
}

impl NameIndex<'_> {
    /// Lexical resolution only. Physical callee/operand, caller activation and
    /// value transport are authenticated by the enclosing Source query.
    pub(crate) fn actual_prelude_name(
        &self,
        context: InvocationContext,
        actual: &Expr,
        identity: &str,
        work: &mut usize,
    ) -> Result<(), String> {
        name_work(work, 1 + identity.len())?;
        let identity = identity.strip_prefix("Prelude::").unwrap_or(identity);
        if !matches!(identity, "Some" | "Ok" | "Err" | "clone" | "clone_immut") {
            return Err("Prelude source lookup does not implement this primitive".into());
        }
        let name = match &actual.kind {
            ExprKind::Name(name) => {
                name_work(work, 1 + name.len())?;
                name.clone()
            }
            ExprKind::Path(path) => {
                name_work(
                    work,
                    1 + path
                        .len()
                        .checked_mul(2)
                        .ok_or("Prelude path work overflow")?,
                )?;
                for piece in path {
                    name_work(work, 1 + piece.len())?;
                }
                path.join("::")
            }
            _ => return Err("Prelude constructor source is not an actual Name or Path".into()),
        };
        name_work(work, 10 + identity.len())?;
        if name != identity && name != format!("Prelude::{identity}") {
            return Err("Prelude constructor source names a different declaration".into());
        }
        let source = actual
            .hir_id
            .ok_or("Prelude primitive has no original HIR identity")?;
        let candidate = self.candidate(context.owner, source, work)?;
        name_work(work, 1 + candidate.name.len())?;
        if candidate.name != name || candidate.shadowed {
            return Err(
                "Prelude constructor is shadowed or absent in its actual lexical owner".into(),
            );
        }
        Ok(())
    }
}

fn builtin_bit(name: &str) -> u128 {
    match name {
        "None" => 1 << 14,
        "Prelude::None" => 1 << 15,
        "File::read_chunk" => 1,
        "File::write" => 2,
        "Process::wait" => 4,
        "Process::terminate" => 8,
        "Array::push" => 1 << 112,
        "Array::insert" => 1 << 113,
        "Array::truncate" => 1 << 114,
        "Map::set" => 1 << 115,
        "Io::read_all" => 1 << 116,
        "Io::write_all" => 1 << 117,
        "Io::read_buffered" => 1 << 118,
        "Io::write_buffered" => 1 << 119,
        "Io::flush" => 1 << 120,
        "Io::close_write_buffer" => 1 << 121,
        other => ril_compiler_core::numeric_builtins::NumericBuiltin::lookup(other)
            .map(|id| id.lexical_bit())
            .or_else(|| {
                crate::sema::source_types::builtins::BuiltinId::lookup(other).map(|id| id.bit())
            })
            .or_else(|| {
                crate::sema::source_types::builtins::ConstantId::lookup(other).map(|id| id.bit())
            })
            .unwrap_or(0),
    }
}

fn bit(name: &str) -> u128 {
    match name {
        "Some" => 1 << 4,
        "Ok" => 1 << 5,
        "Err" => 1 << 6,
        "Prelude::Some" => 1 << 7,
        "Prelude::Ok" => 1 << 8,
        "Prelude::Err" => 1 << 9,
        "clone" => 1 << 10,
        "clone_immut" => 1 << 11,
        "Prelude::clone" => 1 << 12,
        "Prelude::clone_immut" => 1 << 13,
        // A genuinely unresolved local Prelude namespace cannot certify a
        // qualified standard export. A short Some binding does not hide it.
        "Prelude" => (1 << 7) | (1 << 8) | (1 << 9) | (1 << 12) | (1 << 13) | (1 << 15),
        "Io" => ((1 << 6) - 1) << 116,
        _ => builtin_bit(name),
    }
}

struct Walk<'a, 'w> {
    facts: &'a SemanticFacts,
    owners: DeclarationOwners,
    work: &'w mut usize,
    found: Vec<Candidate>,
}

impl Walk<'_, '_> {
    fn charge(&mut self, depth: usize) -> Result<(), String> {
        if depth >= 128 {
            return Err("builtin lexical Source exceeds its nesting bound".into());
        }
        name_work(self.work, 1)?;
        Ok(())
    }

    fn pattern_names(&mut self, pattern: &Pattern, depth: usize) -> Result<u128, String> {
        self.charge(depth)?;
        let mut mask = 0;
        match &pattern.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name)) => mask |= bit(name),
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    mask |= self.pattern_names(item, depth + 1)?;
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    mask |= self.pattern_names(&field.pattern, depth + 1)?;
                }
                mask |= rest_binding.as_deref().map_or(0, bit);
            }
            PatternKind::Mode { pattern, .. } => mask |= self.pattern_names(pattern, depth + 1)?,
            PatternKind::Type { binder, .. } => mask |= binder.as_deref().map_or(0, bit),
            _ => {}
        }
        Ok(mask)
    }

    fn declaration_names(&mut self, statement: &Stmt, depth: usize) -> Result<u128, String> {
        self.charge(depth)?;
        let mut mask = 0;
        match &statement.kind {
            StmtKind::Function(function) => mask |= bit(&function.name),
            StmtKind::Binding(binding) => {
                mask |= self.pattern_names(&binding.pattern, depth + 1)?;
            }
            StmtKind::Type(declaration) => {
                mask |= bit(&declaration.name);
                for variant in &declaration.variants {
                    self.charge(depth)?;
                    name_work(self.work, 3 + declaration.name.len() + variant.name.len())?;
                    mask |= bit(&format!("{}::{}", declaration.name, variant.name));
                }
            }
            StmtKind::Effect(effect) => {
                for operation in &effect.operations {
                    self.charge(depth)?;
                    name_work(self.work, 3 + effect.name.len() + operation.name.len())?;
                    mask |= bit(&format!("{}::{}", effect.name, operation.name));
                }
            }
            StmtKind::Use(import) => {
                if import.glob {
                    // Unresolved wildcard imports do not establish which
                    // declaration supplies a constructor spelling.
                    mask = u128::MAX;
                } else {
                    if let Some(alias) = &import.alias {
                        mask |= bit(alias);
                    } else if import.members.is_empty()
                        && let Some(name) = import.path.last()
                    {
                        mask |= bit(name);
                    }
                    for member in &import.members {
                        self.charge(depth)?;
                        mask |= bit(member.alias.as_ref().unwrap_or(&member.name));
                    }
                }
            }
            _ => {}
        }
        Ok(mask)
    }

    fn statements(
        &mut self,
        statements: &[Stmt],
        owner: CallableOwner,
        mut shadow: u128,
        depth: usize,
    ) -> Result<(), String> {
        for statement in statements {
            shadow |= self.declaration_names(statement, depth)?;
        }
        for statement in statements {
            self.charge(depth)?;
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.expr(&binding.value, owner, shadow, depth + 1)?;
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback, owner, shadow, depth + 1)?;
                    }
                    self.pattern(&binding.pattern, owner, shadow, depth + 1)?;
                }
                StmtKind::Function(function) => {
                    let source = statement
                        .hir_id
                        .ok_or("builtin function scope lost its original declaration identity")?;
                    name_work(
                        self.work,
                        1 + self.owners.len().checked_ilog2().unwrap_or(0) as usize,
                    )?;
                    let Some(&definition) = self.owners.get(&(owner, source)) else {
                        continue;
                    };
                    let hir = self
                        .facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("builtin function scope has no canonical HIR")?;
                    // The original body is authenticated once, independently
                    // of the number of dynamic FunctionInfo instances.
                    for _ in 0..2 {
                        crate::static_eval::charge_statement_syntax_clone(statement, self.work)
                            .ok_or(
                                "builtin canonical scope syntax exceeds its shared work bound",
                            )?;
                    }
                    let mut original = statement.clone();
                    hir.validate_statement_syntax(&mut original, source, hir::HirLimits::default())
                        .map_err(|error| {
                            format!("builtin canonical scope differs from HIR: {error}")
                        })?;
                    let child_owner = CallableOwner::Function(definition);
                    let mut child_shadow = shadow;
                    for parameter in &function.generics {
                        self.charge(depth)?;
                        child_shadow |= bit(&parameter.name);
                    }
                    for statement in &function.signature_where {
                        child_shadow |= self.declaration_names(statement, depth + 1)?;
                    }
                    for parameter in &function.parameters {
                        child_shadow |= self.pattern_names(&parameter.pattern, depth + 1)?;
                        if let Some(default) = &parameter.default {
                            self.expr(default, child_owner, child_shadow, depth + 1)?;
                        }
                    }
                    self.statements(
                        &function.signature_where,
                        child_owner,
                        child_shadow,
                        depth + 1,
                    )?;
                    if let Some(body) = &function.body {
                        self.block(body, child_owner, child_shadow, depth + 1)?;
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target, owner, shadow, depth + 1)?;
                    self.expr(value, owner, shadow, depth + 1)?;
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression, owner, shadow, depth + 1)?
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        let child_owner = owner;
                        let mut child_shadow = shadow;
                        for parameter in &arm.parameters {
                            child_shadow |= self.pattern_names(&parameter.pattern, depth + 1)?;
                        }
                        self.expr(&arm.body, child_owner, child_shadow, depth + 1)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn block(
        &mut self,
        block: &Block,
        owner: CallableOwner,
        shadow: u128,
        depth: usize,
    ) -> Result<(), String> {
        // where declarations share the body's lexical scope.
        let mut scope = shadow;
        for statement in &block.where_items {
            scope |= self.declaration_names(statement, depth + 1)?;
        }
        self.statements(&block.where_items, owner, scope, depth + 1)?;
        self.statements(&block.statements, owner, scope, depth + 1)
    }

    fn lambda_owner(
        &mut self,
        parent: CallableOwner,
        source: Option<ExprId>,
    ) -> Result<Option<CallableOwner>, String> {
        let Some(source) = source else {
            return Ok(None);
        };
        name_work(self.work, 1 + self.facts.closure_sites.len())?;
        let mut matching = self
            .facts
            .closure_sites
            .iter()
            .filter(|site| site.owner == parent && site.source == source);
        let Some(site) = matching.next() else {
            return Ok(None);
        };
        if matching.next().is_some() {
            return Ok(None);
        }
        Ok(Some(CallableOwner::Lambda(site.id)))
    }

    fn pattern(
        &mut self,
        pattern: &Pattern,
        owner: CallableOwner,
        shadow: u128,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &pattern.kind {
            PatternKind::Name(name) if bit(name) != 0 => {
                name_work(self.work, 2 + name.len())?;
                self.found.push(Candidate {
                    source: pattern.hir_id.map(SyntaxId::Pattern),
                    owner,
                    name: name.clone(),
                    shadowed: shadow & bit(name) != 0,
                });
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } if arguments.is_empty()
                && !parenthesized
                && path.len() <= 3
                && path.iter().all(|piece| piece.len() <= 64) =>
            {
                name_work(self.work, 2 + path.len() * 2)?;
                for part in path {
                    name_work(self.work, 1 + part.len())?;
                }
                let name = path.join("::");
                if bit(&name) != 0 {
                    self.found.push(Candidate {
                        source: pattern.hir_id.map(SyntaxId::Pattern),
                        owner,
                        shadowed: shadow & bit(&name) != 0,
                        name,
                    });
                }
            }
            PatternKind::Value(value) => self.expr(value, owner, shadow, depth + 1)?,
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.pattern(item, owner, shadow, depth + 1)?;
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    self.pattern(&field.pattern, owner, shadow, depth + 1)?;
                }
            }
            PatternKind::Mode { pattern, .. } => self.pattern(pattern, owner, shadow, depth + 1)?,
            _ => {}
        }
        Ok(())
    }

    fn expr(
        &mut self,
        expression: &Expr,
        owner: CallableOwner,
        shadow: u128,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &expression.kind {
            ExprKind::Name(name) if bit(name) != 0 => {
                name_work(self.work, 2 + name.len())?;
                self.found.push(Candidate {
                    source: expression.hir_id.map(SyntaxId::Expr),
                    owner,
                    name: name.clone(),
                    shadowed: shadow & bit(name) != 0,
                });
            }
            ExprKind::Path(path) => {
                if path.len() > 3 || path.iter().any(|piece| piece.len() > 64) {
                    return Ok(());
                }
                name_work(self.work, 2 + path.len() * 2)?;
                for part in path {
                    name_work(self.work, 1 + part.len())?;
                }
                let name = path.join("::");
                if bit(&name) == 0 {
                    return Ok(());
                }
                self.found.push(Candidate {
                    source: expression.hir_id.map(SyntaxId::Expr),
                    owner,
                    shadowed: shadow & bit(&name) != 0,
                    name,
                });
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => {
                self.block(block, owner, shadow, depth + 1)?
            }
            ExprKind::Lambda {
                parameters, body, ..
            } => {
                if let Some(child_owner) = self.lambda_owner(owner, expression.hir_id)? {
                    let mut child_shadow = shadow;
                    for parameter in parameters {
                        child_shadow |= self.pattern_names(&parameter.pattern, depth + 1)?;
                    }
                    self.expr(body, child_owner, child_shadow, depth + 1)?;
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::Map(items) => {
                for (key, value) in items {
                    self.expr(key, owner, shadow, depth + 1)?;
                    self.expr(value, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::Record { members, .. } => {
                for member in members {
                    self.expr(
                        match member {
                            RecordMember::Field(field) => &field.value,
                            RecordMember::Spread(value) => value,
                        },
                        owner,
                        shadow,
                        depth + 1,
                    )?;
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Generic { base: operand, .. }
            | ExprKind::Field { base: operand, .. } => {
                self.expr(operand, owner, shadow, depth + 1)?
            }
            ExprKind::Binary { left, right, .. }
            | ExprKind::ComputedField {
                base: left,
                key: right,
            }
            | ExprKind::Index {
                base: left,
                index: right,
                ..
            } => {
                self.expr(left, owner, shadow, depth + 1)?;
                self.expr(right, owner, shadow, depth + 1)?;
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee, owner, shadow, depth + 1)?;
                for argument in arguments {
                    self.expr(&argument.value, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, owner, shadow, depth + 1)?;
                self.expr(then_branch, owner, shadow, depth + 1)?;
                if let Some(value) = else_branch {
                    self.expr(value, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(value, owner, shadow, depth + 1)?;
                for arm in arms {
                    let child_shadow = shadow | self.pattern_names(&arm.pattern, depth + 1)?;
                    self.pattern(&arm.pattern, owner, shadow, depth + 1)?;
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, owner, child_shadow, depth + 1)?;
                    }
                    self.expr(&arm.body, owner, child_shadow, depth + 1)?;
                }
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                self.expr(value, owner, shadow, depth + 1)?;
                self.pattern(pattern, owner, shadow, depth + 1)?;
                let child_shadow = shadow | self.pattern_names(pattern, depth + 1)?;
                self.expr(then_branch, owner, child_shadow, depth + 1)?;
                if let Some(other) = else_branch {
                    self.expr(other, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expr(value, owner, shadow, depth + 1)?;
                self.pattern(pattern, owner, shadow, depth + 1)?;
            }
            ExprKind::While { condition, body } => {
                self.expr(condition, owner, shadow, depth + 1)?;
                self.block(body, owner, shadow, depth + 1)?;
            }
            ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => {
                self.expr(value, owner, shadow, depth + 1)?;
                self.pattern(pattern, owner, shadow, depth + 1)?;
                let child_shadow = shadow | self.pattern_names(pattern, depth + 1)?;
                self.block(body, owner, child_shadow, depth + 1)?;
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable, owner, shadow, depth + 1)?;
                let child_shadow = shadow | self.pattern_names(pattern, depth + 1)?;
                self.block(body, owner, child_shadow, depth + 1)?;
            }
            ExprKind::Control {
                value: Some(value), ..
            } => {
                self.expr(value, owner, shadow, depth + 1)?;
            }
            ExprKind::Control { value: None, .. } => {}
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.expr(base, owner, shadow, depth + 1)?;
                }
                self.expr(recipe, owner, shadow, depth + 1)?;
            }
            ExprKind::Range { start, end, .. } => {
                for value in start.iter().chain(end) {
                    self.expr(value, owner, shadow, depth + 1)?;
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression, owner, shadow, depth + 1)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod prelude_tests {
    use super::*;

    fn function_model() -> (SemanticFacts, StmtId, ExprId) {
        let source = ril_test::case_source("tests/stdlib/num.ril::numeric-callable-views");
        let mut parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let hir = crate::hir::nodes::HirProgram::lower_identified(
            &mut parsed.program,
            crate::hir::nodes::InputOrigin::Source,
        )
        .unwrap();
        let statement = parsed
            .program
            .statements
            .iter()
            .find(|statement| matches!(statement.kind, StmtKind::Function(_)))
            .unwrap();
        let StmtKind::Function(function) = &statement.kind else {
            unreachable!()
        };
        let declaration = statement.hir_id.unwrap();
        let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[0].kind else {
            unreachable!("numeric callable fixture begins with the direct parse declaration")
        };
        let expression = binding.value.hir_id.unwrap();
        assert!(matches!(&hir.expression(expression).unwrap().kind,
            hir::ExprKind::Path(path) if path == &["Num", "parse_int"]));
        let info = FunctionInfo {
            hir_id: Some(declaration),
            definition: DefinitionId(0),
            lexical_owner: Some(CallableOwner::Global),
            typing_environment: Default::default(),
            syntax: function.clone(),
            lexical: Default::default(),
            owner: None,
            handler_context: vec![],
            lexical_scope: 0,
            environment: None,
            captures: Default::default(),
            writes: Default::default(),
            environment_published: false,
        };
        (
            SemanticFacts {
                functions: vec![info],
                source_program: Some(std::sync::Arc::new(parsed.program)),
                semantic_hir: Some(std::sync::Arc::new(hir)),
                ..Default::default()
            },
            declaration,
            expression,
        )
    }

    #[test]
    fn name_preparation_sees_prelude_builtin_and_constructor_forms() {
        for name in [
            "Some",
            "Ok",
            "Err",
            "None",
            "clone",
            "clone_immut",
            "Prelude::Some",
            "Prelude::None",
        ] {
            for constructor in [false, true] {
                let mut value = Value::scalar(Ty::Unknown, None, CauseId(0));
                value.callables.push(if constructor {
                    Callable::Constructor(name.into())
                } else {
                    Callable::Builtin(name.into())
                });
                let mut facts = SemanticFacts::default();
                facts.expressions.push(crate::sema::ExpressionFact {
                    source_id: None,
                    allocation_epoch: 0,
                    span: Span {
                        file: FileId(0),
                        start: 0,
                        end: 0,
                    },
                    value: crate::sema::PhysicalValue::unobserved_fixture(value, 0),
                });
                assert!(NameIndex::needs_preparation(&facts, &mut 4096).unwrap());
                assert!(NameIndex::needs_preparation(&facts, &mut 0).is_err());
            }
        }
        assert!(!NameIndex::needs_preparation(&SemanticFacts::default(), &mut 4096).unwrap());
    }

    #[test]
    fn function_owner_index_reuses_declarations_across_dynamic_instances() {
        let (mut facts, _, expression) = function_model();
        let mut work = 4_000_000;
        let names = NameIndex::new_with_work(&facts, &mut work).unwrap();
        assert_eq!(
            names
                .direct_identity(
                    Some(CallableOwner::Function(DefinitionId(0))),
                    expression,
                    &mut work
                )
                .unwrap()
                .as_deref(),
            Some("Num::parse_int")
        );
        let baseline = 4_000_000 - work;
        drop(names);
        let copies = 128;
        let template = facts.functions[0].clone();
        facts
            .functions
            .extend((0..copies).map(|_| template.clone()));
        let mut work = 4_000_000;
        let names = NameIndex::new_with_work(&facts, &mut work).unwrap();
        assert_eq!(
            names
                .direct_identity(
                    Some(CallableOwner::Function(DefinitionId(0))),
                    expression,
                    &mut work
                )
                .unwrap()
                .as_deref(),
            Some("Num::parse_int")
        );
        assert!(
            4_000_000 - work < baseline + copies * 128,
            "each dynamic instance must cost registry admission, not another complete body traversal"
        );
        for units in [0, 1] {
            assert!(NameIndex::new_with_work(&facts, &mut { units }).is_err());
        }
    }

    #[test]
    fn function_owner_index_rejects_missing_ambiguous_cross_owner_and_forged_bodies() {
        let (facts, declaration, expression) = function_model();
        let owner = Some(CallableOwner::Function(DefinitionId(0)));
        for mutation in 0..4 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.functions[0].hir_id = None,
                1 => {
                    let mut second = changed.functions[0].clone();
                    second.definition = DefinitionId(1);
                    changed.functions.push(second);
                }
                2 => {
                    changed.functions[0].lexical_owner =
                        Some(CallableOwner::Function(DefinitionId(99)))
                }
                _ => {
                    let original =
                        std::sync::Arc::make_mut(changed.source_program.as_mut().unwrap());
                    let statement = original
                        .statements
                        .iter_mut()
                        .find(|statement| statement.hir_id == Some(declaration))
                        .unwrap();
                    let StmtKind::Function(function) = &mut statement.kind else {
                        unreachable!()
                    };
                    let StmtKind::Binding(binding) =
                        &mut function.body.as_mut().unwrap().statements[0].kind
                    else {
                        unreachable!()
                    };
                    let ExprKind::Path(path) = &mut binding.value.kind else {
                        unreachable!()
                    };
                    *path.last_mut().unwrap() = "parse_f32".into();
                }
            }
            match NameIndex::new_with_work(&changed, &mut 4_000_000) {
                Err(_) => {}
                Ok(names) => assert!(
                    names.direct_identity(owner, expression, &mut 4096).is_err(),
                    "mutation {mutation} borrowed another declaration owner"
                ),
            }
        }
        let mut moved = facts.clone();
        let program = std::sync::Arc::make_mut(moved.source_program.as_mut().unwrap());
        let statement = program
            .statements
            .iter_mut()
            .find(|statement| statement.hir_id == Some(declaration))
            .unwrap();
        statement.span.start += 10;
        let StmtKind::Function(function) = &mut statement.kind else {
            unreachable!()
        };
        function.span.start += 10;
        let names = NameIndex::new_with_work(&moved, &mut 4_000_000).unwrap();
        assert_eq!(
            names
                .direct_identity(owner, expression, &mut 4096)
                .unwrap()
                .as_deref(),
            Some("Num::parse_int"),
            "diagnostic spans cannot select an owner"
        );
    }

    #[test]
    fn hoist_declaration_identity_uses_some_statement_ids_and_the_lexical_owner() {
        let (mut facts, declaration, _) = function_model();
        let owner = Some(CallableOwner::Global);
        assert_eq!(
            crate::sema::checker::declaration_definition(
                &facts.functions,
                owner,
                Some(declaration)
            ),
            Some(DefinitionId(0))
        );
        assert_eq!(
            crate::sema::checker::declaration_definition(
                &facts.functions,
                owner,
                Some(StmtId(u32::MAX))
            ),
            None,
            "an equal name/span is not another declaration's identity"
        );
        assert_eq!(
            crate::sema::checker::declaration_definition(&facts.functions, None, Some(declaration)),
            None
        );
        assert_eq!(
            crate::sema::checker::declaration_definition(
                &facts.functions,
                Some(CallableOwner::Function(DefinitionId(99))),
                Some(declaration)
            ),
            None
        );
        facts.functions[0].syntax.span.start += 10;
        assert_eq!(
            crate::sema::checker::declaration_definition(
                &facts.functions,
                owner,
                Some(declaration)
            ),
            Some(DefinitionId(0))
        );
        facts.functions[0].hir_id = None;
        assert_eq!(
            crate::sema::checker::declaration_definition(&facts.functions, owner, None),
            None,
            "two missing identities cannot authorize reuse"
        );
    }

    fn model(large_declaration: bool) -> SemanticFacts {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let mut statements = Vec::new();
        if large_declaration {
            statements.push(Stmt {
                hir_id: None,
                span,
                kind: StmtKind::Type(TypeDeclaration {
                    visibility: Default::default(),
                    is_halt: false,
                    name: "x".repeat(1024 * 1024),
                    generics: vec![],
                    value: None,
                    variants: vec![Variant {
                        name: "Variant".into(),
                        generics: vec![],
                        payload: None,
                        result: None,
                        annotations: vec![],
                        span,
                    }],
                    opaque: false,
                    nominal: true,
                    span,
                }),
            });
        }
        statements.push(Stmt {
            hir_id: None,
            span,
            kind: StmtKind::Expr {
                expression: Expr {
                    hir_id: None,
                    span,
                    kind: ExprKind::Path(vec!["Num".into(), "parse_int".into()]),
                },
                terminated: false,
            },
        });
        let mut program = Program { statements };
        let hir = crate::hir::nodes::HirProgram::lower_identified(
            &mut program,
            crate::hir::nodes::InputOrigin::Source,
        )
        .unwrap();
        SemanticFacts {
            source_program: Some(std::sync::Arc::new(program)),
            semantic_hir: Some(std::sync::Arc::new(hir)),
            ..SemanticFacts::default()
        }
    }

    #[test]
    fn name_index_prepays_owned_names_and_borrows_exact_construction_work() {
        let facts = model(true);
        for units in [0, 1] {
            let mut work = units;
            assert!(NameIndex::new_with_work(&facts, &mut work).is_err());
            assert!(work <= units);
        }
        let initial = 16_000_000;
        let mut work = initial;
        let names = NameIndex::new_with_work(&facts, &mut work).unwrap();
        assert!(names.matches_facts(&facts));
        let other = model(false);
        assert!(!names.matches_facts(&other));
        let used = initial - work;
        assert!(
            used >= 1024 * 1024,
            "formatting a declaration's owned variant name is admitted before allocation"
        );
        let mut exact = used;
        assert!(NameIndex::new_with_work(&facts, &mut exact).is_ok());
        assert_eq!(exact, 0);
        let mut short = used - 1;
        assert!(NameIndex::new_with_work(&facts, &mut short).is_err());
    }

    #[test]
    fn name_index_lookups_cannot_refill_the_shared_allowance() {
        let facts = model(false);
        let names = NameIndex::new_with_work(&facts, &mut 65536).unwrap();
        let StmtKind::Expr { expression, .. } =
            &facts.source_program.as_ref().unwrap().statements[0].kind
        else {
            unreachable!()
        };
        let source = expression.hir_id.unwrap();
        let owner = Some(CallableOwner::Global);
        for units in [0, 1] {
            assert!(
                names
                    .direct_identity(owner, source, &mut { units })
                    .is_err()
            );
        }
        let initial = 65536;
        let mut work = initial;
        assert_eq!(
            names
                .direct_identity(owner, source, &mut work)
                .unwrap()
                .as_deref(),
            Some("Num::parse_int")
        );
        let used = initial - work;
        let mut exact = used;
        assert_eq!(
            names
                .direct_identity(owner, source, &mut exact)
                .unwrap()
                .as_deref(),
            Some("Num::parse_int")
        );
        assert_eq!(exact, 0);
        assert!(names.direct_identity(owner, source, &mut exact).is_err());
        assert!(
            names
                .direct_identity(owner, source, &mut { used - 1 })
                .is_err()
        );
    }

    fn lookup(source: &str, spelling: &str, identity: &str) -> Result<(), String> {
        let mut parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let hir = crate::hir::nodes::HirProgram::lower_identified(
            &mut parsed.program,
            crate::hir::nodes::InputOrigin::Source,
        )
        .unwrap();
        let facts = SemanticFacts {
            source_program: Some(std::sync::Arc::new(parsed.program)),
            semantic_hir: Some(std::sync::Arc::new(hir)),
            ..SemanticFacts::default()
        };
        let mut work = 65536;
        let owners = declaration_owners(&facts, &mut work)?;
        let mut walk = Walk {
            facts: &facts,
            owners,
            work: &mut work,
            found: vec![],
        };
        walk.statements(
            &facts.source_program.as_ref().unwrap().statements,
            CallableOwner::Global,
            0,
            0,
        )?;
        let candidate = walk
            .found
            .iter()
            .find(|candidate| {
                candidate.name == spelling && matches!(candidate.source, Some(SyntaxId::Expr(_)))
            })
            .expect("fixture must contain its real constructor expression");
        let Some(SyntaxId::Expr(source)) = candidate.source else {
            panic!("fixture must select a physical expression")
        };
        let names = NameIndex::new_with_work(&facts, &mut work)?;
        names.actual_prelude_name(
            InvocationContext {
                invocation: None,
                owner: Some(CallableOwner::Global),
                closure: None,
                closure_invocation: None,
                budget_validation: false,
                default_use: None,
            },
            &Expr {
                hir_id: Some(source),
                span: facts
                    .semantic_hir
                    .as_deref()
                    .unwrap()
                    .expression(source)
                    .unwrap()
                    .info
                    .span,
                kind: ExprKind::Name(spelling.into()),
            },
            identity,
            &mut work,
        )
    }

    #[test]
    fn only_real_unshadowed_prelude_spellings_resolve() {
        for name in ["Some", "Ok", "Err"] {
            assert!(lookup(&format!("let VALUE={name}(1)"), name, name).is_ok());
            let qualified = format!("Prelude::{name}");
            assert!(lookup(&format!("let VALUE={qualified}(1)"), &qualified, name).is_ok());
            assert!(
                lookup(
                    &format!("type {name}(int)\nlet VALUE={name}(1)"),
                    name,
                    name
                )
                .is_err()
            );
            assert!(
                lookup(
                    &format!("use external::{{{name}}}\nlet VALUE={name}(1)"),
                    name,
                    name
                )
                .is_err()
            );
            // The explicit canonical namespace remains independent of the
            // short local constructor, matching the resolver's policy.
            assert!(
                lookup(
                    &format!("type {name}(int)\nlet VALUE={qualified}(1)"),
                    &qualified,
                    name
                )
                .is_ok()
            );
            assert!(
                lookup(
                    &format!("type Prelude{{{name}(int)}}\nlet VALUE={qualified}(1)"),
                    &qualified,
                    name
                )
                .is_err()
            );
        }
        assert!(lookup("let VALUE=Some(1)", "Some", "None").is_err());
        assert!(lookup("let VALUE=Some(1)", "Some", "Ok").is_err());
        for name in ["clone", "clone_immut"] {
            let qualified = format!("Prelude::{name}");
            assert!(lookup(&format!("let VALUE={name}(1)"), name, name).is_ok());
            assert!(lookup(&format!("let VALUE={{let {name}=1;{name}(1)}}"), name, name).is_err());
            assert!(
                lookup(
                    &format!("let VALUE={{let {name}=1;{qualified}(1)}}"),
                    &qualified,
                    name
                )
                .is_ok()
            );
        }
    }

    #[test]
    fn local_imports_where_declarations_and_match_blocks_keep_their_scope() {
        for source in [
            "let VALUE={use external::{Some};Some(2)}",
            "let VALUE={Some(2)\nwhere type Some(int)}",
            "let VALUE=match 1{_->{Some(2)\nwhere type Some(int)}}",
        ] {
            assert!(lookup(source, "Some", "Some").is_err(), "{source}");
        }
    }
}
