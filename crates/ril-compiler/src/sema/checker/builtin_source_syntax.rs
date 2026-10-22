//! One frozen lexical source walk. Only syntax is indexed; caller facts and
//! builtin summary obligations are checked separately for every observation.
use super::*;
use crate::hir::nodes::{self as hir, NodeId as SyntaxId};
use ril_compiler_core::ids::ExprId;

#[derive(Clone)]
struct Candidate {
    source: Option<SyntaxId>,
    owner: CallableOwner,
    name: String,
    shadowed: bool,
}

pub(super) struct NameIndex<'a> {
    facts: &'a SemanticFacts,
    candidates: BTreeMap<SyntaxId, Vec<Candidate>>,
}

impl<'a> NameIndex<'a> {
    pub(super) fn new(facts: &'a SemanticFacts) -> Result<Self, String> {
        let program = facts
            .source_program
            .as_deref()
            .ok_or("builtin source has no frozen actual Program")?;
        let mut walker = Walk {
            facts,
            work: 65536,
            found: Vec::new(),
        };
        walker.statements(&program.statements, CallableOwner::Global, 0, 0)?;
        if walker.work < walker.found.len() {
            return Err("builtin lexical index exceeds its work bound".into());
        }
        let mut candidates = BTreeMap::<_, Vec<_>>::new();
        for candidate in walker.found {
            if let Some(source) = candidate.source {
                candidates.entry(source).or_default().push(candidate);
            }
        }
        Ok(Self { facts, candidates })
    }

    fn candidate(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
    ) -> Result<&Candidate, String> {
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("builtin source has no HIR")?;
        let node = hir
            .expression(source)
            .ok_or("builtin source HIR is absent")?;
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

    pub(super) fn direct_identity(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
    ) -> Result<Option<String>, String> {
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("builtin source has no HIR")?;
        let node = hir
            .expression(source)
            .ok_or("builtin source HIR is absent")?;
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
        let candidate = self.candidate(owner, source)?;
        if candidate.name != name {
            return Err("builtin reference differs from its original HIR name".into());
        }
        Ok((!candidate.shadowed && builtin_bit(&candidate.name) != 0)
            .then(|| candidate.name.clone()))
    }

    pub(super) fn actual_name(
        &self,
        owner: Option<CallableOwner>,
        source: ExprId,
        name: &str,
    ) -> Result<(), String> {
        if self.direct_identity(owner, source)?.as_deref() == Some(name) {
            return Ok(());
        }
        Err(
            "builtin source has no unique unshadowed canonical Name in its real lexical owner"
                .into(),
        )
    }
}

/// A lexical lookup only. Call-site, caller activation, complete argument
/// receipts and original constructor value must be checked independently.
pub(super) fn actual_prelude_name(
    facts: &SemanticFacts,
    context: InvocationContext,
    actual: &Expr,
    identity: &str,
) -> Result<(), String> {
    let identity = identity.strip_prefix("Prelude::").unwrap_or(identity);
    if !matches!(identity, "Some" | "Ok" | "Err" | "clone" | "clone_immut") {
        return Err("Prelude source lookup does not implement this primitive".into());
    }
    let name = match &actual.kind {
        ExprKind::Name(name) => name.clone(),
        ExprKind::Path(path) => path.join("::"),
        _ => return Err("Prelude constructor source is not an actual Name or Path".into()),
    };
    if name != identity && name != format!("Prelude::{identity}") {
        return Err("Prelude constructor source names a different declaration".into());
    }
    let source = actual
        .hir_id
        .ok_or_else(|| "Prelude primitive has no original HIR identity".to_owned())?;
    let candidate = actual_candidate(facts, context.owner, source)?;
    if candidate.name != name || candidate.shadowed {
        return Err("Prelude constructor is shadowed or absent in its actual lexical owner".into());
    }
    Ok(())
}

fn actual_candidate(
    facts: &SemanticFacts,
    owner: Option<CallableOwner>,
    source: ExprId,
) -> Result<Candidate, String> {
    Ok(NameIndex::new(facts)?.candidate(owner, source)?.clone())
}

fn builtin_bit(name: &str) -> u64 {
    match name {
        "File::read_chunk" => 1,
        "File::write" => 2,
        "Process::wait" => 4,
        "Process::terminate" => 8,
        "Array::push" => 1 << 52,
        "Array::insert" => 1 << 53,
        "Array::truncate" => 1 << 54,
        "Map::set" => 1 << 55,
        other => crate::sema::source_types::builtins::BuiltinId::lookup(other)
            .map(|id| id.bit())
            .or_else(|| {
                crate::sema::source_types::builtins::ConstantId::lookup(other).map(|id| id.bit())
            })
            .unwrap_or(0),
    }
}

fn bit(name: &str) -> u64 {
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
        "Prelude" => (1 << 7) | (1 << 8) | (1 << 9) | (1 << 12) | (1 << 13),
        _ => builtin_bit(name),
    }
}

struct Walk<'a> {
    facts: &'a SemanticFacts,
    work: usize,
    found: Vec<Candidate>,
}

impl Walk<'_> {
    fn charge(&mut self, depth: usize) -> Result<(), String> {
        if depth >= 128 {
            return Err("builtin lexical Source exceeds its nesting bound".into());
        }
        self.work = self
            .work
            .checked_sub(1)
            .ok_or("builtin lexical Source exceeds its work bound")?;
        Ok(())
    }

    fn pattern_names(&mut self, pattern: &Pattern, depth: usize) -> Result<u64, String> {
        self.charge(depth)?;
        let mut mask = 0;
        match &pattern.kind {
            PatternKind::Name(name) => mask |= bit(name),
            PatternKind::Tuple(items)
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

    fn declaration_names(&mut self, statement: &Stmt, depth: usize) -> Result<u64, String> {
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
                    mask |= bit(&format!("{}::{}", declaration.name, variant.name));
                }
            }
            StmtKind::Effect(effect) => {
                for operation in &effect.operations {
                    self.charge(depth)?;
                    mask |= bit(&format!("{}::{}", effect.name, operation.name));
                }
            }
            StmtKind::Use(import) => {
                if import.glob {
                    // Unresolved wildcard imports do not establish which
                    // declaration supplies a constructor spelling.
                    mask = u64::MAX;
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
        mut shadow: u64,
        depth: usize,
    ) -> Result<(), String> {
        for statement in statements {
            shadow |= self.declaration_names(statement, depth)?;
        }
        for statement in statements {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.expr(&binding.value, owner, shadow, depth + 1)?;
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback, owner, shadow, depth + 1)?;
                    }
                    self.pattern(&binding.pattern, owner, shadow, depth + 1)?;
                }
                StmtKind::Function(function) => {
                    let mut definitions = BTreeSet::new();
                    let facts = self.facts;
                    for info in &facts.functions {
                        self.charge(depth)?;
                        if info.syntax == *function {
                            definitions.insert(info.definition);
                        }
                    }
                    if definitions.len() != 1 {
                        continue;
                    }
                    let child_owner = CallableOwner::Function(*definitions.first().unwrap());
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
        shadow: u64,
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

    fn lambda_owner(&self, parent: CallableOwner, source: Option<ExprId>) -> Option<CallableOwner> {
        let source = source?;
        let matching: Vec<_> = self
            .facts
            .closure_sites
            .iter()
            .filter(|site| site.owner == parent && site.source == source)
            .collect();
        let [site] = matching.as_slice() else {
            return None;
        };
        Some(CallableOwner::Lambda(site.id))
    }

    fn pattern(
        &mut self,
        pattern: &Pattern,
        owner: CallableOwner,
        shadow: u64,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &pattern.kind {
            PatternKind::Name(name) if bit(name) != 0 => self.found.push(Candidate {
                source: pattern.hir_id.map(SyntaxId::Pattern),
                owner,
                name: name.clone(),
                shadowed: shadow & bit(name) != 0,
            }),
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } if arguments.is_empty()
                && !parenthesized
                && path.len() <= 3
                && path.iter().all(|piece| piece.len() <= 64) =>
            {
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
        shadow: u64,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &expression.kind {
            ExprKind::Name(name) if bit(name) != 0 => self.found.push(Candidate {
                source: expression.hir_id.map(SyntaxId::Expr),
                owner,
                name: name.clone(),
                shadowed: shadow & bit(name) != 0,
            }),
            ExprKind::Path(path) => {
                if path.len() > 3 || path.iter().any(|piece| piece.len() > 64) {
                    return Ok(());
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
                if let Some(child_owner) = self.lambda_owner(owner, expression.hir_id) {
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
            ExprKind::Is { value, pattern } => {
                self.expr(value, owner, shadow, depth + 1)?;
                self.pattern(pattern, owner, shadow, depth + 1)?;
            }
            ExprKind::While { condition, body } => {
                self.expr(condition, owner, shadow, depth + 1)?;
                self.block(body, owner, shadow, depth + 1)?;
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
        let mut walk = Walk {
            facts: &facts,
            work: 65536,
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
        actual_prelude_name(
            &facts,
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
