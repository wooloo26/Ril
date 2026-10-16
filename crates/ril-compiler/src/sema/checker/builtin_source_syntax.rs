//! One frozen lexical source walk. Only syntax is indexed; caller facts and
//! builtin summary obligations are checked separately for every observation.
use super::*;

#[derive(Clone)]
struct Candidate {
    owner: CallableOwner,
    span: Span,
    name: String,
    shadowed: bool,
}

pub(super) fn actual_name(
    facts: &SemanticFacts,
    owner: Option<CallableOwner>,
    span: Span,
    name: &str,
) -> Result<(), String> {
    if direct_identity(facts, owner, span)?.as_deref() == Some(name) {
        return Ok(());
    }
    Err("builtin source has no unique unshadowed canonical Name in its real lexical owner".into())
}

pub(super) fn direct_identity(
    facts: &SemanticFacts,
    owner: Option<CallableOwner>,
    span: Span,
) -> Result<Option<String>, String> {
    let candidate = actual_candidate(facts, owner, span)?;
    Ok((!candidate.shadowed && builtin_bit(&candidate.name) != 0).then_some(candidate.name))
}

/// A lexical lookup only. Call-site, caller activation, complete argument
/// receipts and original constructor value must be checked independently.
pub(super) fn actual_prelude_name(
    facts: &SemanticFacts,
    context: InvocationContext,
    actual: &Expr,
    identity: &str,
) -> Result<(), String> {
    if !matches!(identity, "Some" | "Ok" | "Err") {
        return Err("Prelude source lookup does not implement this constructor".into());
    }
    let name = match &actual.kind {
        ExprKind::Name(name) => name.clone(),
        ExprKind::Path(path) => path.join("::"),
        _ => return Err("Prelude constructor source is not an actual Name or Path".into()),
    };
    if name != identity && name != format!("Prelude::{identity}") {
        return Err("Prelude constructor source names a different declaration".into());
    }
    let candidate = actual_candidate(facts, context.owner, actual.span)?;
    if candidate.name != name || candidate.shadowed {
        return Err("Prelude constructor is shadowed or absent in its actual lexical owner".into());
    }
    Ok(())
}

fn actual_candidate(
    facts: &SemanticFacts,
    owner: Option<CallableOwner>,
    span: Span,
) -> Result<Candidate, String> {
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
    let candidates: Vec<_> = walker
        .found
        .iter()
        .filter(|candidate| Some(candidate.owner) == owner && candidate.span == span)
        .collect();
    let [candidate] = candidates.as_slice() else {
        return Err("builtin source has no unique real Name in its lexical owner".into());
    };
    Ok((**candidate).clone())
}

fn builtin_bit(name: &str) -> u16 {
    match name {
        "File::read_chunk" => 1,
        "File::write" => 2,
        "Process::wait" => 4,
        "Process::terminate" => 8,
        _ => 0,
    }
}

fn bit(name: &str) -> u16 {
    match name {
        "Some" => 1 << 4,
        "Ok" => 1 << 5,
        "Err" => 1 << 6,
        "Prelude::Some" => 1 << 7,
        "Prelude::Ok" => 1 << 8,
        "Prelude::Err" => 1 << 9,
        // A genuinely unresolved local Prelude namespace cannot certify a
        // qualified standard export. A short Some binding does not hide it.
        "Prelude" => (1 << 7) | (1 << 8) | (1 << 9),
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

    fn pattern_names(&mut self, pattern: &Pattern, depth: usize) -> Result<u16, String> {
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

    fn declaration_names(&mut self, statement: &Stmt, depth: usize) -> Result<u16, String> {
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
                    mask = u16::MAX;
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
        mut shadow: u16,
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
                        let child_owner = self.lambda_owner(owner, arm.span).unwrap_or(owner);
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
        shadow: u16,
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

    fn lambda_owner(&self, parent: CallableOwner, span: Span) -> Option<CallableOwner> {
        let matching: Vec<_> = self
            .facts
            .closure_sites
            .iter()
            .filter(|site| site.owner == parent && site.span == span)
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
        shadow: u16,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &pattern.kind {
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
        shadow: u16,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(depth)?;
        match &expression.kind {
            ExprKind::Name(name) => self.found.push(Candidate {
                owner,
                span: expression.span,
                name: name.clone(),
                shadowed: shadow & bit(name) != 0,
            }),
            ExprKind::Path(path) => {
                let name = path.join("::");
                self.found.push(Candidate {
                    owner,
                    span: expression.span,
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
                if let Some(child_owner) = self.lambda_owner(owner, expression.span) {
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
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let facts = SemanticFacts {
            source_program: Some(std::sync::Arc::new(parsed.program)),
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
            .find(|candidate| candidate.name == spelling)
            .expect("fixture must contain its real constructor expression");
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
                span: candidate.span,
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
