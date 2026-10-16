//! File discovery and lexical module resolution. I/O stays outside queries;
//! imported names are resolved to one declaration identity before verification.
use crate::sema::UnsupportedFeature;
use ril_compiler_core::{
    diagnostic::{Diagnostic, Label, Severity},
    source::{FileId, Span},
};
use ril_syntax::ast::*;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    io,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone)]
pub struct ModuleUnit {
    pub path: PathBuf,
    pub file: FileId,
    pub program: Program,
    pub is_declaration: bool,
}

#[derive(Debug, Clone)]
pub struct ResolvedProject {
    pub root: FileId,
    pub units: Vec<ModuleUnit>,
    pub program: Program,
    pub diagnostics: Vec<Diagnostic>,
    pub unsupported: Vec<UnsupportedFeature>,
    pub syntax_incomplete: bool,
    pub external_declarations: Vec<ExternalDeclaration>,
    pub type_declarations: BTreeMap<String, String>,
}
/// Host binding names follow source module declarations, independently of file
/// discovery order and the hygienic internal names chosen for this compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalDeclaration {
    pub declaration: String,
    pub internal_name: String,
    pub span: Span,
    pub kind: ExternalDeclarationKind,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalDeclarationKind {
    Function,
    Constant,
}

/// Resolve imports relative to the executable/library root's directory. An
/// implementation unit is selected before a declaration unit at the same path.
pub fn load_project(path: &Path) -> io::Result<ResolvedProject> {
    let root_path = std::fs::canonicalize(path)?;
    let directory = root_path.parent().unwrap_or(Path::new(".")).to_owned();
    let mut queue = VecDeque::from([root_path]);
    let mut seen = BTreeSet::new();
    let mut units = vec![];
    let mut diagnostics = vec![];
    let mut unsupported = vec![];
    let mut syntax_incomplete = false;
    while let Some(path) = queue.pop_front() {
        if !seen.insert(path.clone()) {
            continue;
        }
        let file = FileId(units.len() as u32);
        let bytes = std::fs::read(&path)?;
        let program = match std::str::from_utf8(&bytes) {
            Ok(text) => {
                let parsed = ril_syntax::parse_file(text, file);
                diagnostics.extend(parsed.diagnostics);
                if parsed.incomplete {
                    syntax_incomplete = true;
                    unsupported.push(UnsupportedFeature {
                        span: Span {
                            file,
                            start: 0,
                            end: bytes.len().min(u32::MAX as usize) as u32,
                        },
                        description: "unsupported module syntax".into(),
                    });
                }
                parsed.program
            }
            Err(error) => {
                let start = error.valid_up_to() as u32;
                diagnostics.push(error_diagnostic(
                    "E0104",
                    Span {
                        file,
                        start,
                        end: start.saturating_add(1),
                    },
                    "source is not valid UTF-8",
                ));
                Program::default()
            }
        };
        let mut imports = vec![];
        collect_imports(&program.statements, &mut imports);
        for import in imports {
            if import.path.first().is_some_and(|part| part == "ril") {
                continue;
            }
            let stem = import
                .path
                .iter()
                .fold(directory.clone(), |path, part| path.join(part));
            let ordinary = stem.with_extension("ril");
            let declaration = stem.with_extension("d.ril");
            let selected = if ordinary.is_file() {
                Some(ordinary)
            } else if declaration.is_file() {
                Some(declaration)
            } else {
                None
            };
            if let Some(selected) = selected {
                queue.push_back(std::fs::canonicalize(selected)?);
            } else {
                diagnostics.push(error_diagnostic(
                    "E0208",
                    import.span,
                    format!("module {} does not exist", import.path.join("/")),
                ));
            }
        }
        let is_declaration = path.to_string_lossy().ends_with(".d.ril");
        units.push(ModuleUnit {
            path,
            file,
            program,
            is_declaration,
        });
    }
    let mut resolved = resolve(units, FileId(0));
    diagnostics.append(&mut resolved.diagnostics);
    unsupported.append(&mut resolved.unsupported);
    resolved.diagnostics = diagnostics;
    resolved.unsupported = unsupported;
    resolved.syntax_incomplete = syntax_incomplete;
    Ok(resolved)
}

pub fn resolve(mut units: Vec<ModuleUnit>, root: FileId) -> ResolvedProject {
    for unit in &mut units {
        crate::normalize::program(&mut unit.program);
    }
    Resolver::new(units, root).run()
}

pub fn validate_unit(unit: &ModuleUnit) -> Vec<Diagnostic> {
    let mut diagnostics = vec![];
    for statement in &unit.program.statements {
        match &statement.kind {
            StmtKind::Function(function) => {
                if unit.is_declaration && function.body.is_some() {
                    diagnostics.push(error_diagnostic(
                        "E0901",
                        function.span,
                        "external declaration cannot contain an implementation body",
                    ));
                }
                if !unit.is_declaration && function.body.is_none() {
                    diagnostics.push(error_diagnostic(
                        "E0902",
                        function.span,
                        "ordinary module function requires an implementation body",
                    ));
                }
                if unit.is_declaration {
                    let hidden_result = function.return_type.as_ref().is_some_and(|ty| {
                        contains_callable(ty, &unit.program, &mut BTreeSet::new())
                    });
                    let invalid_parameter = function.parameters.iter().any(|parameter| {
                        parameter.mode == ParameterMode::SharedMut
                            || (parameter.mode == ParameterMode::Mut
                                && !parameter.ty.as_ref().is_some_and(|ty| {
                                    direct_callable(ty, &unit.program, &mut BTreeSet::new())
                                }))
                            || parameter.ty.as_ref().is_some_and(|ty| {
                                invalid_callback_exchange(ty, &unit.program, &mut BTreeSet::new())
                                    || contains_callable(ty, &unit.program, &mut BTreeSet::new())
                                        && !direct_callable(ty, &unit.program, &mut BTreeSet::new())
                            })
                    });
                    if hidden_result
                        || invalid_parameter
                        || function.annotations.iter().any(|annotation| {
                            annotation.text == "&^mut" || annotation.text == "&capture"
                        })
                    {
                        diagnostics.push(error_diagnostic("E0908",function.span,"external contract requests unsupported mutable exchange or callable retention"));
                    }
                }
            }
            StmtKind::Binding(binding) => {
                if unit.is_declaration
                    && (!matches!(binding.value.kind, ExprKind::Ambient)
                        || binding.mode != BindingMode::Let
                        || binding.is_meta)
                {
                    diagnostics.push(error_diagnostic(
                        "E0901",
                        statement.span,
                        "external module admits only uninitialized immutable constants",
                    ));
                }
                if !unit.is_declaration && matches!(binding.value.kind, ExprKind::Ambient) {
                    diagnostics.push(error_diagnostic(
                        "E0902",
                        statement.span,
                        "ordinary module constant requires an initializer",
                    ));
                }
                if unit.is_declaration
                    && binding.ty.as_ref().is_some_and(|ty| {
                        contains_callable(ty, &unit.program, &mut BTreeSet::new())
                    })
                {
                    diagnostics.push(error_diagnostic(
                        "E0908",
                        statement.span,
                        "external constants cannot contain callable values",
                    ));
                }
            }
            StmtKind::Type(_) | StmtKind::Use(_) => {}
            _ if unit.is_declaration => diagnostics.push(error_diagnostic(
                "E0901",
                statement.span,
                "executable statement is prohibited in an external declaration module",
            )),
            _ => {}
        }
    }
    diagnostics
}

fn error_diagnostic(code: &str, span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic {
        code: code.into(),
        severity: Severity::Error,
        message: message.clone(),
        labels: vec![Label { span, message }],
        causes: vec![],
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Symbol {
    Declaration(String),
    Namespace(usize),
    Standard(String),
    Ambiguous,
}
#[derive(Clone, Default)]
struct Scope {
    names: BTreeMap<String, Symbol>,
    locals: BTreeSet<String>,
    local_variants: BTreeMap<String, Vec<String>>,
    local_operations: BTreeMap<String, Vec<String>>,
    local_effect_sets: BTreeSet<String>,
    derived_variants: BTreeSet<String>,
}
impl Scope {
    fn shadow(&mut self, names: impl IntoIterator<Item = String>) {
        for name in names {
            self.local_variants.remove(&name);
            self.local_operations.remove(&name);
            self.local_effect_sets.remove(&name);
            self.locals.insert(name);
        }
    }
    fn clear_derived_variants(&mut self) {
        for name in std::mem::take(&mut self.derived_variants) {
            self.names.remove(&name);
        }
    }
}
#[derive(Clone, Default)]
struct Symbols {
    own: BTreeMap<String, Symbol>,
    exports: BTreeMap<String, Symbol>,
    private: BTreeSet<String>,
}

struct Resolver {
    units: Vec<ModuleUnit>,
    root: FileId,
    symbols: Vec<Symbols>,
    targets: BTreeMap<String, usize>,
    diagnostics: Vec<Diagnostic>,
    unsupported: Vec<UnsupportedFeature>,
    variants: BTreeMap<String, Vec<String>>,
    operations: BTreeMap<String, Vec<String>>,
    effect_sets: BTreeSet<String>,
    canonical_names: BTreeMap<(usize, String), String>,
    value_declarations: BTreeSet<String>,
}
impl Resolver {
    fn new(units: Vec<ModuleUnit>, root: FileId) -> Self {
        let directory = units
            .iter()
            .find(|unit| unit.file == root)
            .and_then(|unit| unit.path.parent())
            .unwrap_or(Path::new("."))
            .to_owned();
        let targets = units
            .iter()
            .enumerate()
            .map(|(index, unit)| {
                let relative = unit.path.strip_prefix(&directory).unwrap_or(&unit.path);
                let spelling = relative.to_string_lossy().replace('\\', "/");
                let name = spelling
                    .strip_suffix(".d.ril")
                    .or_else(|| spelling.strip_suffix(".ril"))
                    .unwrap_or(&spelling)
                    .to_owned();
                (name, index)
            })
            .collect();
        let symbols = vec![Symbols::default(); units.len()];
        let declarations: Vec<_> = units.iter().map(unit_declarations).collect();
        let mut used: BTreeSet<_> = declarations
            .iter()
            .flatten()
            .map(|(name, _)| name.clone())
            .collect();
        let mut canonical_names = BTreeMap::new();
        for (index, names) in declarations.iter().enumerate() {
            for (name, type_name) in names {
                if canonical_names.contains_key(&(index, name.clone())) {
                    continue;
                }
                let base = if units[index].file == root && !type_name {
                    name.clone()
                } else if *type_name {
                    format!("Ril__Module{}{}", units[index].file.0, name)
                } else if name.bytes().any(|c| c.is_ascii_uppercase()) {
                    format!("RIL__MODULE_{}_{}", units[index].file.0, name)
                } else {
                    format!(
                        "ril__module_{}_{}",
                        units[index].file.0,
                        name.trim_start_matches('_')
                    )
                };
                let mut canonical = base.clone();
                let mut suffix = 2;
                if units[index].file != root {
                    while used.contains(&canonical) {
                        canonical = if *type_name {
                            format!("{base}{suffix}")
                        } else {
                            format!("{base}_{suffix}")
                        };
                        suffix += 1;
                    }
                }
                used.insert(canonical.clone());
                canonical_names.insert((index, name.clone()), canonical);
            }
        }
        Self {
            units,
            root,
            symbols,
            targets,
            diagnostics: vec![],
            unsupported: vec![],
            variants: BTreeMap::new(),
            operations: BTreeMap::new(),
            effect_sets: BTreeSet::new(),
            canonical_names,
            value_declarations: BTreeSet::new(),
        }
    }
    fn run(mut self) -> ResolvedProject {
        for index in 0..self.units.len() {
            self.diagnostics.extend(validate_unit(&self.units[index]));
            let statements = self.units[index].program.statements.clone();
            for statement in &statements {
                let (name, visibility) = match &statement.kind {
                    StmtKind::Function(function) => {
                        (Some(function.name.clone()), function.visibility)
                    }
                    StmtKind::Type(declaration) => {
                        (Some(declaration.name.clone()), declaration.visibility)
                    }
                    StmtKind::Effect(declaration) => {
                        (Some(declaration.name.clone()), declaration.visibility)
                    }
                    StmtKind::Binding(binding) => {
                        let mut names = vec![];
                        pattern_bindings(&binding.pattern, &mut names);
                        for name in names {
                            self.declare(index, &name, binding.visibility, statement.span);
                            self.value_declarations.insert(self.canonical(index, &name));
                        }
                        continue;
                    }
                    _ => (None, Visibility::Private),
                };
                if let Some(name) = name {
                    self.declare(index, &name, visibility, statement.span);
                    if let StmtKind::Type(declaration) = &statement.kind {
                        let canonical = self.canonical(index, &name);
                        self.variants.insert(
                            canonical,
                            declaration
                                .variants
                                .iter()
                                .map(|variant| variant.name.clone())
                                .collect(),
                        );
                    }
                    if let StmtKind::Effect(declaration) = &statement.kind {
                        if !declaration.members.is_empty() {
                            self.effect_sets.insert(self.canonical(index, &name));
                        }
                        self.operations.insert(
                            self.canonical(index, &name),
                            declaration
                                .operations
                                .iter()
                                .map(|operation| operation.name.clone())
                                .collect(),
                        );
                    }
                }
            }
        }
        // Re-export equations are monotone and finite. Cyclic import graphs do
        // not manufacture definitions; only actual declarations seed exports.
        for _ in 0..=self.units.len() {
            let mut changed = false;
            for index in 0..self.units.len() {
                let statements = self.units[index].program.statements.clone();
                for statement in &statements {
                    if let StmtKind::Use(import) = &statement.kind
                        && import.visibility == Visibility::Public
                    {
                        for (name, symbol) in self.import_symbols(index, import, false) {
                            if self.symbols[index].exports.get(&name) != Some(&symbol) {
                                self.symbols[index].exports.insert(name, symbol);
                                changed = true;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut program = Program::default();
        // Dependencies initialize before the root. Each real declaration occurs
        // once even when reached through aliases or re-export chains.
        let order = self.initialization_order();
        for index in order {
            let mut statements = self.units[index].program.statements.clone();
            let mut scope = Scope {
                local_effect_sets: BTreeSet::new(),
                names: prelude_symbols(),
                locals: BTreeSet::new(),
                local_variants: BTreeMap::new(),
                local_operations: BTreeMap::new(),
                derived_variants: BTreeSet::new(),
            };
            scope.names.extend(self.symbols[index].own.clone());
            self.import_scope(index, &statements, &mut scope);
            self.add_variants(&mut scope);
            self.rewrite_statements(index, &mut statements, &mut scope, true);
            program.statements.extend(
                statements
                    .into_iter()
                    .filter(|statement| !matches!(statement.kind, StmtKind::Use(_))),
            );
        }
        let external_declarations = self.external_declarations();
        let mut type_declarations = BTreeMap::new();
        for (module, &index) in &self.targets {
            for statement in &self.units[index].program.statements {
                if let StmtKind::Type(declaration) = &statement.kind {
                    type_declarations.insert(
                        self.canonical(index, &declaration.name),
                        format!("{module}::{}", declaration.name),
                    );
                }
            }
        }
        ResolvedProject {
            root: self.root,
            units: self.units,
            program,
            diagnostics: self.diagnostics,
            unsupported: self.unsupported,
            syntax_incomplete: false,
            external_declarations,
            type_declarations,
        }
    }
    fn external_declarations(&self) -> Vec<ExternalDeclaration> {
        let mut declarations = Vec::new();
        for (module, &index) in &self.targets {
            let unit = &self.units[index];
            if !unit.is_declaration {
                continue;
            }
            for statement in &unit.program.statements {
                let (names, kind) = match &statement.kind {
                    StmtKind::Function(function) if function.body.is_none() => (
                        vec![function.name.clone()],
                        ExternalDeclarationKind::Function,
                    ),
                    StmtKind::Binding(binding)
                        if matches!(binding.value.kind, ExprKind::Ambient) =>
                    {
                        let mut names = Vec::new();
                        pattern_bindings(&binding.pattern, &mut names);
                        (names, ExternalDeclarationKind::Constant)
                    }
                    _ => continue,
                };
                declarations.extend(names.into_iter().map(|name| ExternalDeclaration {
                    declaration: format!("{module}::{name}"),
                    internal_name: self.canonical(index, &name),
                    span: statement.span,
                    kind,
                }));
            }
        }
        declarations
    }
    fn canonical(&self, index: usize, name: &str) -> String {
        self.canonical_names
            .get(&(index, name.into()))
            .cloned()
            .unwrap_or_else(|| name.into())
    }
    fn initialization_order(&self) -> Vec<usize> {
        fn visit(
            index: usize,
            resolver: &Resolver,
            seen: &mut BTreeSet<usize>,
            order: &mut Vec<usize>,
        ) {
            if !seen.insert(index) {
                return;
            }
            let mut imports = vec![];
            collect_imports(&resolver.units[index].program.statements, &mut imports);
            for import in imports {
                if let Some(&target) = resolver.targets.get(&import.path.join("/")) {
                    visit(target, resolver, seen, order);
                }
            }
            order.push(index);
        }
        let mut order = vec![];
        let mut seen = BTreeSet::new();
        if let Some(index) = self.units.iter().position(|unit| unit.file == self.root) {
            visit(index, self, &mut seen, &mut order);
        }
        for index in 0..self.units.len() {
            visit(index, self, &mut seen, &mut order);
        }
        order
    }
    fn declare(&mut self, index: usize, name: &str, visibility: Visibility, span: Span) {
        let symbol = Symbol::Declaration(self.canonical(index, name));
        if self.symbols[index]
            .own
            .insert(name.into(), symbol.clone())
            .is_some()
        {
            self.diagnostics.push(error_diagnostic(
                "E0203",
                span,
                format!("duplicate declaration {name}"),
            ));
        }
        if visibility == Visibility::Public {
            self.symbols[index].exports.insert(name.into(), symbol);
        } else {
            self.symbols[index].private.insert(name.into());
        }
    }
    fn import_symbols(
        &mut self,
        index: usize,
        import: &UseDeclaration,
        report: bool,
    ) -> Vec<(String, Symbol)> {
        let path = import.path.join("/");
        let target = if import.path.first().is_some_and(|p| p == "ril") {
            let Some(namespace) = standard_namespace(&path) else {
                if report {
                    self.diagnostics.push(error_diagnostic(
                        "E0208",
                        import.span,
                        format!("standard module {path} does not exist"),
                    ));
                }
                return vec![];
            };
            Symbol::Standard(namespace.into())
        } else if let Some(&target) = self.targets.get(&path) {
            Symbol::Namespace(target)
        } else {
            if report {
                self.diagnostics.push(error_diagnostic(
                    "E0208",
                    import.span,
                    format!("module {path} does not exist"),
                ));
            }
            return vec![];
        };
        if import.members.is_empty() && !import.glob {
            let name = import.alias.clone().unwrap_or_else(|| {
                pascal(import.path.last().map(String::as_str).unwrap_or_default())
            });
            if report && !name.chars().next().is_some_and(char::is_uppercase) {
                self.diagnostics.push(error_diagnostic(
                    "E0101",
                    import.span,
                    "module namespace alias must be PascalCase",
                ));
            }
            return vec![(name, target)];
        }
        if import.glob {
            return match target {
                Symbol::Namespace(target) => self.symbols[target]
                    .exports
                    .iter()
                    .map(|(name, symbol)| (name.clone(), symbol.clone()))
                    .collect(),
                Symbol::Standard(namespace) => standard_exports(&path)
                    .iter()
                    .map(|name| {
                        (
                            name.to_string(),
                            Symbol::Declaration(standard_identity(&namespace, name)),
                        )
                    })
                    .collect(),
                _ => vec![],
            };
        }
        let mut result = vec![];
        for member in &import.members {
            let symbol = match &target {
                Symbol::Namespace(target) => {
                    self.member(*target, &member.name, member.span, report)
                }
                Symbol::Standard(namespace) => {
                    if report && !standard_exports(&path).contains(&member.name.as_str()) {
                        self.diagnostics.push(error_diagnostic(
                            "E0209",
                            member.span,
                            format!("module {path} has no member {}", member.name),
                        ));
                    }
                    Some(Symbol::Declaration(standard_identity(
                        namespace,
                        &member.name,
                    )))
                }
                _ => None,
            };
            if let Some(symbol) = symbol {
                result.push((
                    member.alias.clone().unwrap_or_else(|| member.name.clone()),
                    symbol,
                ));
            }
        }
        let _ = index;
        result
    }
    fn member(&mut self, target: usize, name: &str, span: Span, report: bool) -> Option<Symbol> {
        if let Some(symbol) = self.symbols[target].exports.get(name) {
            return Some(symbol.clone());
        }
        if report {
            let code = if self.symbols[target].own.contains_key(name) {
                "E0201"
            } else {
                "E0209"
            };
            self.diagnostics.push(error_diagnostic(
                code,
                span,
                format!(
                    "module member {name} is {}",
                    if code == "E0201" {
                        "private"
                    } else {
                        "missing"
                    }
                ),
            ));
        }
        None
    }
    fn import_scope(&mut self, index: usize, statements: &[Stmt], scope: &mut Scope) {
        for statement in statements {
            if let StmtKind::Use(import) = &statement.kind {
                for (name, symbol) in self.import_symbols(index, import, true) {
                    if (scope.names.contains_key(&name) && !is_implicit_prelude(&name, scope))
                        || scope.locals.contains(&name)
                    {
                        self.diagnostics.push(error_diagnostic(
                            "E0203",
                            import.span,
                            format!("import collides with {name}"),
                        ));
                    } else {
                        scope.names.insert(name, symbol);
                    }
                }
            }
        }
    }
    fn add_variants(&self, scope: &mut Scope) {
        scope.clear_derived_variants();
        let mut candidates: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (binding, symbol) in &scope.names {
            if let Symbol::Declaration(name) = symbol
                && !scope.locals.contains(binding)
                && let Some(variants) = self.variants.get(name)
            {
                for variant in variants {
                    candidates
                        .entry(variant.clone())
                        .or_default()
                        .push(format!("{name}::{variant}"));
                }
            }
        }
        for (name, variants) in &scope.local_variants {
            for variant in variants {
                candidates
                    .entry(variant.clone())
                    .or_default()
                    .push(format!("{name}::{variant}"));
            }
        }
        for (name, mut candidates) in candidates {
            candidates.sort();
            candidates.dedup();
            if let std::collections::btree_map::Entry::Vacant(entry) =
                scope.names.entry(name.clone())
            {
                scope.derived_variants.insert(name);
                entry.insert(if candidates.len() == 1 {
                    Symbol::Declaration(candidates.remove(0))
                } else {
                    Symbol::Ambiguous
                });
            }
        }
    }
    fn path(&mut self, path: &[String], scope: &Scope, span: Span) -> Vec<String> {
        let Some(first) = path.first() else {
            return vec![];
        };
        if scope.locals.contains(first) {
            if path.len() > 1
                && !(path.len() == 2
                    && (scope
                        .local_variants
                        .get(first)
                        .is_some_and(|members| members.contains(&path[1]))
                        || scope
                            .local_operations
                            .get(first)
                            .is_some_and(|members| members.contains(&path[1]))
                        || scope.local_effect_sets.contains(first)))
            {
                self.diagnostics.push(error_diagnostic(
                    "E0204",
                    span,
                    "lexical binding does not declare this namespace member",
                ));
                return vec![format!("ril__unresolved_{}_{}", span.file.0, span.start)];
            }
            return path.to_vec();
        }
        let Some(mut symbol) = scope.names.get(first).cloned() else {
            if self
                .canonical_names
                .values()
                .any(|name| name == &path.join("::"))
            {
                self.diagnostics.push(error_diagnostic(
                    "E0204",
                    span,
                    "internal declaration identity is not an imported source name",
                ));
                return vec![format!("ril_missing_{}", span.start)];
            }
            if self.units.iter().enumerate().any(|(index, unit)| {
                unit.file == self.root && self.symbols[index].own.contains_key(first)
            }) {
                self.diagnostics.push(error_diagnostic(
                    "E0204",
                    span,
                    format!("{first} is not declared or imported in this module"),
                ));
                return vec![format!("ril_unresolved_{}_{}", span.file.0, span.start)];
            }
            return path.to_vec();
        };
        let mut cursor = 1;
        while let Symbol::Namespace(target) = symbol {
            let Some(name) = path.get(cursor) else {
                return path.to_vec();
            };
            cursor += 1;
            let Some(member) = self.member(target, name, span, true) else {
                return vec![format!("ril_missing_{}", span.start)];
            };
            symbol = member;
        }
        let mut resolved = match symbol {
            Symbol::Declaration(name) => {
                if cursor < path.len()
                    && !((path.len() == cursor + 1
                        && (self
                            .variants
                            .get(&name)
                            .is_some_and(|members| members.contains(&path[cursor]))
                            || self
                                .operations
                                .get(&name)
                                .is_some_and(|members| members.contains(&path[cursor]))
                            || self.effect_sets.contains(&name)))
                        || name.starts_with("Prelude::")
                        || known_standard_identity(&name))
                {
                    self.diagnostics.push(error_diagnostic(
                        "E0204",
                        span,
                        "declaration does not own this namespace member",
                    ));
                    return vec![format!("ril__unresolved_{}_{}", span.file.0, span.start)];
                }
                name.split("::").map(str::to_owned).collect::<Vec<_>>()
            }
            Symbol::Standard(namespace) => vec![namespace],
            Symbol::Ambiguous => {
                self.diagnostics.push(error_diagnostic(
                    "E0206",
                    span,
                    "constructor abbreviation has multiple visible declarations",
                ));
                return path.to_vec();
            }
            Symbol::Namespace(_) => unreachable!(),
        };
        resolved.extend_from_slice(&path[cursor..]);
        resolved
    }

    fn rewrite_statements(
        &mut self,
        index: usize,
        statements: &mut [Stmt],
        scope: &mut Scope,
        top: bool,
    ) {
        for statement in statements {
            match &mut statement.kind {
                StmtKind::Function(function) => {
                    let mut child = scope.clone();
                    for parameter in &function.parameters {
                        let mut names = vec![];
                        pattern_bindings(&parameter.pattern, &mut names);
                        child.shadow(names);
                    }
                    for generic in &function.generics {
                        child.shadow([generic.name.clone()]);
                    }
                    if top {
                        function.name = self.canonical(index, &function.name);
                    } else {
                        child.locals.insert(function.name.clone());
                    }
                    self.rewrite_function(index, function, &mut child);
                }
                StmtKind::Type(declaration) => {
                    let mut child = scope.clone();
                    child.shadow(declaration.generics.iter().map(|g| g.name.clone()));
                    if top {
                        declaration.name = self.canonical(index, &declaration.name);
                    }
                    self.rewrite_generics(index, &mut declaration.generics, &child);
                    if let Some(value) = &mut declaration.value {
                        self.rewrite_type(index, value, &child);
                    }
                    for variant in &mut declaration.variants {
                        let mut variant_scope = child.clone();
                        variant_scope.shadow(variant.generics.iter().map(|g| g.name.clone()));
                        self.rewrite_generics(index, &mut variant.generics, &variant_scope);
                        if let Some(payload) = &mut variant.payload {
                            self.rewrite_type(index, payload, &variant_scope);
                        }
                        if let Some(result) = &mut variant.result {
                            self.rewrite_type(index, result, &variant_scope);
                        }
                        self.rewrite_annotations(&mut variant.annotations, &variant_scope);
                    }
                }
                StmtKind::Effect(declaration) => {
                    if top {
                        declaration.name = self.canonical(index, &declaration.name);
                    }
                    let mut child = scope.clone();
                    child.shadow(declaration.generics.iter().map(|g| g.name.clone()));
                    self.rewrite_generics(index, &mut declaration.generics, &child);
                    for operation in &mut declaration.operations {
                        self.rewrite_function(index, operation, &mut child.clone());
                    }
                    for member in &mut declaration.members {
                        self.rewrite_type(index, member, &child);
                    }
                }
                StmtKind::Binding(binding) => {
                    self.rewrite_expr(index, &mut binding.value, scope);
                    if let Some(ty) = &mut binding.ty {
                        self.rewrite_type(index, ty, scope);
                    }
                    if let Some(fallback) = &mut binding.fallback {
                        self.rewrite_expr(index, fallback, scope);
                    }
                    self.rewrite_pattern(index, &mut binding.pattern, scope, true, top);
                    if !top {
                        let mut names = vec![];
                        pattern_bindings(&binding.pattern, &mut names);
                        scope.shadow(names);
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.rewrite_expr(index, target, scope);
                    self.rewrite_expr(index, value, scope);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.rewrite_expr(index, expression, scope)
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        self.rewrite_expr(index, &mut arm.operation, scope);
                        let mut child = scope.clone();
                        for parameter in &arm.parameters {
                            let mut names = vec![];
                            pattern_bindings(&parameter.pattern, &mut names);
                            child.shadow(names);
                        }
                        for parameter in &mut arm.parameters {
                            self.rewrite_parameter(index, parameter, &child);
                        }
                        self.rewrite_expr(index, &mut arm.body, &child);
                    }
                }
                StmtKind::Use(_) => {}
            }
        }
    }
    fn rewrite_function(&mut self, index: usize, function: &mut Function, scope: &mut Scope) {
        // Signature declarations are hoisted into the signature and body. Their
        // lexical names must win before any module-qualified name is selected.
        for statement in &function.signature_where {
            if let StmtKind::Type(declaration) = &statement.kind {
                scope.locals.insert(declaration.name.clone());
                scope.local_variants.insert(
                    declaration.name.clone(),
                    declaration
                        .variants
                        .iter()
                        .map(|variant| variant.name.clone())
                        .collect(),
                );
            }
        }
        self.add_variants(scope);
        self.rewrite_generics(index, &mut function.generics, scope);
        for parameter in &mut function.parameters {
            self.rewrite_parameter(index, parameter, scope);
        }
        if let Some(result) = &mut function.return_type {
            self.rewrite_type(index, result, scope);
        }
        // A body-local declaration is hoisted within its block, but its effect
        // identity cannot become part of the enclosing function's signature.
        if let Some(body) = &function.body {
            let local: BTreeSet<_> = body
                .statements
                .iter()
                .chain(&body.where_items)
                .filter_map(|statement| match &statement.kind {
                    StmtKind::Effect(effect) => Some(effect.name.as_str()),
                    _ => None,
                })
                .collect();
            for annotation in &function.annotations {
                if annotation.kind == AnnotationKind::Effect
                    && annotation
                        .text
                        .split(|character: char| {
                            !character.is_ascii_alphanumeric() && character != '_'
                        })
                        .any(|name| local.contains(name))
                {
                    self.diagnostics.push(error_diagnostic(
                        "E0618",
                        annotation.span,
                        "a body-local effect cannot escape into the enclosing callable signature",
                    ));
                }
            }
        }
        self.rewrite_annotations(&mut function.annotations, scope);
        self.rewrite_statements(index, &mut function.signature_where, scope, false);
        if let Some(body) = &mut function.body {
            self.rewrite_block(index, body, scope);
        }
    }
    fn rewrite_generics(&mut self, index: usize, generics: &mut [GenericParameter], scope: &Scope) {
        for generic in generics {
            if let Some(bound) = &mut generic.bound {
                self.rewrite_type(index, bound, scope);
            }
            if let Some(default) = &mut generic.default {
                self.rewrite_type(index, default, scope);
            }
        }
    }
    fn rewrite_parameter(&mut self, index: usize, parameter: &mut Parameter, scope: &Scope) {
        if let Some(ty) = &mut parameter.ty {
            self.rewrite_type(index, ty, scope);
        }
        if let Some(default) = &mut parameter.default {
            self.rewrite_expr(index, default, scope);
        }
    }
    fn rewrite_block(&mut self, index: usize, block: &mut Block, parent: &Scope) {
        let mut scope = parent.clone();
        scope.clear_derived_variants();
        for statement in block.statements.iter().chain(&block.where_items) {
            match &statement.kind {
                StmtKind::Function(f) => {
                    scope.locals.insert(f.name.clone());
                }
                StmtKind::Type(t) => {
                    scope.locals.insert(t.name.clone());
                    scope.local_variants.insert(
                        t.name.clone(),
                        t.variants
                            .iter()
                            .map(|variant| variant.name.clone())
                            .collect(),
                    );
                }
                StmtKind::Effect(e) => {
                    scope.locals.insert(e.name.clone());
                    if !e.members.is_empty() {
                        scope.local_effect_sets.insert(e.name.clone());
                    }
                    scope.local_operations.insert(
                        e.name.clone(),
                        e.operations
                            .iter()
                            .map(|operation| operation.name.clone())
                            .collect(),
                    );
                }
                StmtKind::Binding(binding) => {
                    let mut names = vec![];
                    pattern_bindings(&binding.pattern, &mut names);
                    scope.shadow(names);
                }
                _ => {}
            }
        }
        self.import_scope(index, &block.statements, &mut scope);
        self.add_variants(&mut scope);
        self.rewrite_statements(index, &mut block.where_items, &mut scope, false);
        self.rewrite_statements(index, &mut block.statements, &mut scope, false);
        block
            .statements
            .retain(|statement| !matches!(statement.kind, StmtKind::Use(_)));
    }
    fn rewrite_expr(&mut self, index: usize, expr: &mut Expr, scope: &Scope) {
        match &mut expr.kind {
            ExprKind::Name(name) => {
                let resolved = self.path(std::slice::from_ref(name), scope, expr.span);
                if resolved.len() == 1 {
                    *name = resolved[0].clone();
                } else {
                    expr.kind = ExprKind::Path(resolved);
                }
            }
            ExprKind::Path(path) => *path = self.path(path, scope, expr.span),
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.rewrite_expr(index, expression, scope);
                    }
                }
            }
            ExprKind::Generic { base, arguments } => {
                self.rewrite_expr(index, base, scope);
                for argument in arguments {
                    self.rewrite_type(index, argument, scope);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.rewrite_expr(index, item, scope);
                }
            }
            ExprKind::Map(pairs) => {
                for (key, value) in pairs {
                    self.rewrite_expr(index, key, scope);
                    self.rewrite_expr(index, value, scope);
                }
            }
            ExprKind::Record {
                ty,
                fields,
                spread,
                members,
            } => {
                if let Some(ty) = ty {
                    self.rewrite_type(index, ty, scope);
                }
                for field in fields {
                    self.rewrite_expr(index, &mut field.value, scope);
                }
                if let Some(spread) = spread {
                    self.rewrite_expr(index, spread, scope);
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            self.rewrite_expr(index, &mut field.value, scope)
                        }
                        RecordMember::Spread(value) => self.rewrite_expr(index, value, scope),
                    }
                }
            }
            ExprKind::Unary { operand, .. } => self.rewrite_expr(index, operand, scope),
            ExprKind::Binary { left, right, .. } => {
                self.rewrite_expr(index, left, scope);
                self.rewrite_expr(index, right, scope);
            }
            ExprKind::Call { callee, arguments } => {
                self.rewrite_expr(index, callee, scope);
                for argument in arguments {
                    self.rewrite_expr(index, &mut argument.value, scope);
                }
            }
            ExprKind::Field { base, .. } => self.rewrite_expr(index, base, scope),
            ExprKind::ComputedField { base, key } => {
                self.rewrite_expr(index, base, scope);
                self.rewrite_expr(index, key, scope);
            }
            ExprKind::Index {
                base,
                index: subscript,
                ..
            } => {
                self.rewrite_expr(index, base, scope);
                self.rewrite_expr(index, subscript, scope);
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } => {
                let mut child = scope.clone();
                for parameter in parameters.iter() {
                    let mut names = vec![];
                    pattern_bindings(&parameter.pattern, &mut names);
                    child.shadow(names);
                }
                for parameter in parameters {
                    self.rewrite_parameter(index, parameter, &child);
                }
                if let Some(result) = return_type {
                    self.rewrite_type(index, result, &child);
                }
                self.rewrite_annotations(annotations, &child);
                self.rewrite_expr(index, body, &child);
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => {
                self.rewrite_block(index, block, scope)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.rewrite_expr(index, condition, scope);
                self.rewrite_expr(index, then_branch, scope);
                if let Some(branch) = else_branch {
                    self.rewrite_expr(index, branch, scope);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.rewrite_expr(index, value, scope);
                for arm in arms {
                    let mut child = scope.clone();
                    let mut names = vec![];
                    pattern_bindings(&arm.pattern, &mut names);
                    child.shadow(names);
                    self.rewrite_pattern(index, &mut arm.pattern, scope, true, false);
                    if let Some(guard) = &mut arm.guard {
                        self.rewrite_expr(index, guard, &child);
                    }
                    self.rewrite_expr(index, &mut arm.body, &child);
                }
            }
            ExprKind::Is { value, pattern } => {
                self.rewrite_expr(index, value, scope);
                self.rewrite_pattern(index, pattern, scope, false, false);
            }
            ExprKind::While { condition, body } => {
                self.rewrite_expr(index, condition, scope);
                self.rewrite_block(index, body, scope);
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.rewrite_expr(index, iterable, scope);
                let mut child = scope.clone();
                let mut names = vec![];
                pattern_bindings(pattern, &mut names);
                child.shadow(names);
                self.rewrite_pattern(index, pattern, scope, true, false);
                self.rewrite_block(index, body, &child);
            }
            ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    self.rewrite_expr(index, value, scope);
                }
            }
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.rewrite_type(index, ty, scope),
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.rewrite_expr(index, base, scope);
                }
                self.rewrite_expr(index, recipe, scope);
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.rewrite_expr(index, start, scope);
                }
                if let Some(end) = end {
                    self.rewrite_expr(index, end, scope);
                }
            }
            ExprKind::Literal(_) | ExprKind::Accessor(_) | ExprKind::Ambient | ExprKind::Error => {}
        }
    }
    fn rewrite_type(&mut self, index: usize, ty: &mut TypeExpr, scope: &Scope) {
        match &mut ty.kind {
            TypeKind::Name { path, arguments } => {
                *path = self.path(path, scope, ty.span);
                for argument in arguments {
                    self.rewrite_type(index, argument, scope);
                }
            }
            TypeKind::Optional(inner) | TypeKind::KeyOf(inner) | TypeKind::Rest(inner) => {
                self.rewrite_type(index, inner, scope)
            }
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    self.rewrite_expr(index, length, scope);
                }
                self.rewrite_type(index, element, scope);
            }
            TypeKind::Map { key, value } => {
                self.rewrite_type(index, key, scope);
                self.rewrite_type(index, value, scope);
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.rewrite_type(index, item, scope);
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.rewrite_type(index, &mut field.ty, scope);
                }
                if let Some(row) = row {
                    self.rewrite_type(index, row, scope);
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                for parameter in parameters {
                    self.rewrite_parameter(index, parameter, scope);
                }
                if let Some(result) = result {
                    self.rewrite_type(index, result, scope);
                }
                self.rewrite_annotations(annotations, scope);
            }
            TypeKind::TypeFunction { parameters, body } => {
                let mut child = scope.clone();
                child.shadow(parameters.iter().map(|p| p.name.clone()));
                self.rewrite_generics(index, parameters, &child);
                self.rewrite_expr(index, body, &child);
            }
            TypeKind::Projection { base, .. } => self.rewrite_type(index, base, scope),
            TypeKind::ComputedProjection { base, key } => {
                self.rewrite_type(index, base, scope);
                self.rewrite_expr(index, key, scope);
            }
            TypeKind::Computation(value) => self.rewrite_expr(index, value, scope),
            TypeKind::Mapped {
                binder,
                keys,
                value,
                ..
            } => {
                self.rewrite_expr(index, keys, scope);
                let mut child = scope.clone();
                child.shadow([binder.clone()]);
                self.rewrite_type(index, value, &child);
            }
            TypeKind::KindArrow { parameter, result } => {
                self.rewrite_type(index, parameter, scope);
                self.rewrite_type(index, result, scope);
            }
            TypeKind::Error => {}
        }
    }
    fn rewrite_pattern(
        &mut self,
        index: usize,
        pattern: &mut Pattern,
        scope: &Scope,
        binding: bool,
        top: bool,
    ) {
        match &mut pattern.kind {
            PatternKind::Name(name) => {
                if top {
                    *name = self.canonical(index, name);
                } else if !binding {
                    let path = self.path(std::slice::from_ref(name), scope, pattern.span);
                    *name = path.join("::");
                }
            }
            PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
                for item in items {
                    self.rewrite_pattern(index, item, scope, binding, top);
                }
            }
            PatternKind::Record {
                ty,
                fields,
                rest_binding,
                ..
            } => {
                if let Some(ty) = ty {
                    self.rewrite_type(index, ty, scope);
                }
                for field in fields {
                    self.rewrite_pattern(index, &mut field.pattern, scope, binding, top);
                }
                if top && let Some(name) = rest_binding {
                    *name = self.canonical(index, name);
                }
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => {
                let local_value = path.len() == 1
                    && scope.locals.contains(&path[0])
                    && !scope.local_variants.contains_key(&path[0])
                    && !scope.local_operations.contains_key(&path[0]);
                *path = self.path(path, scope, pattern.span);
                let value = local_value || self.value_declarations.contains(&path.join("::"));
                if !binding && value && arguments.is_empty() && !*parenthesized {
                    pattern.kind = PatternKind::Value(Box::new(Expr {
                        kind: if path.len() == 1 {
                            ExprKind::Name(path[0].clone())
                        } else {
                            ExprKind::Path(path.clone())
                        },
                        span: pattern.span,
                    }));
                    return;
                }
                for argument in arguments {
                    self.rewrite_pattern(index, argument, scope, binding, top);
                }
            }
            PatternKind::Mode { pattern, .. } => {
                self.rewrite_pattern(index, pattern, scope, binding, top)
            }
            PatternKind::Type { ty, .. } => self.rewrite_type(index, ty, scope),
            PatternKind::Value(value) => self.rewrite_expr(index, value, scope),
            PatternKind::Literal(_) | PatternKind::Wildcard | PatternKind::Error => {}
        }
    }
    fn rewrite_annotations(&mut self, annotations: &mut [Annotation], scope: &Scope) {
        for annotation in annotations {
            let mut result = String::new();
            let text = annotation.text.clone();
            let mut pos = 0;
            while pos < text.len() {
                let c = text[pos..].chars().next().unwrap();
                if c.is_ascii_alphabetic() || c == '_' {
                    let start = pos;
                    pos += c.len_utf8();
                    while pos < text.len() {
                        let c = text[pos..].chars().next().unwrap();
                        if c.is_ascii_alphanumeric() || c == '_' || text[pos..].starts_with("::") {
                            pos += if text[pos..].starts_with("::") { 2 } else { 1 };
                        } else {
                            break;
                        }
                    }
                    let word = &text[start..pos];
                    if matches!(word, "closure" | "capture" | "mut") {
                        result.push_str(word);
                    } else {
                        let path: Vec<_> = word.split("::").map(str::to_owned).collect();
                        result.push_str(&self.path(&path, scope, annotation.span).join("::"));
                    }
                } else {
                    result.push(c);
                    pos += c.len_utf8();
                }
            }
            annotation.text = result;
        }
    }
}

fn pattern_bindings(pattern: &Pattern, names: &mut Vec<String>) {
    match &pattern.kind {
        PatternKind::Name(name) => names.push(name.clone()),
        PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
            for item in items {
                pattern_bindings(item, names);
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                pattern_bindings(&field.pattern, names);
            }
            if let Some(name) = rest_binding {
                names.push(name.clone());
            }
        }
        PatternKind::Constructor { arguments, .. } => {
            for argument in arguments {
                pattern_bindings(argument, names);
            }
        }
        PatternKind::Mode { pattern, .. } => pattern_bindings(pattern, names),
        PatternKind::Type { ty, .. } => type_pattern_bindings(ty, names),
        _ => {}
    }
}
fn type_pattern_bindings(ty: &TypeExpr, names: &mut Vec<String>) {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            if let Some(name) = path
                .first()
                .and_then(|name| name.strip_prefix("let "))
                .filter(|name| *name != "_")
            {
                names.push(name.into());
            }
            for argument in arguments {
                type_pattern_bindings(argument, names);
            }
        }
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Array { element: inner, .. } => type_pattern_bindings(inner, names),
        TypeKind::Map { key, value } => {
            type_pattern_bindings(key, names);
            type_pattern_bindings(value, names);
        }
        TypeKind::Tuple(items) => {
            for item in items {
                type_pattern_bindings(item, names);
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                type_pattern_bindings(&field.ty, names);
            }
            if let Some(row) = row {
                type_pattern_bindings(row, names);
            }
        }
        _ => {}
    }
}
fn unit_declarations(unit: &ModuleUnit) -> Vec<(String, bool)> {
    let mut result = vec![];
    for statement in &unit.program.statements {
        match &statement.kind {
            StmtKind::Function(f) => result.push((f.name.clone(), false)),
            StmtKind::Type(t) => result.push((t.name.clone(), true)),
            StmtKind::Effect(e) => result.push((e.name.clone(), true)),
            StmtKind::Binding(b) => {
                let mut names = vec![];
                pattern_bindings(&b.pattern, &mut names);
                result.extend(names.into_iter().map(|name| (name, false)));
            }
            _ => {}
        }
    }
    result
}
fn pascal(value: &str) -> String {
    value
        .split('_')
        .map(|part| {
            let mut chars = part.chars();
            chars
                .next()
                .map(|c| c.to_ascii_uppercase().to_string() + chars.as_str())
                .unwrap_or_default()
        })
        .collect()
}
fn standard_identity(namespace: &str, name: &str) -> String {
    if namespace == "Prelude" || matches!(name, "Option" | "Result" | "Immut" | "Set") {
        format!("Prelude::{name}")
    } else {
        format!("{namespace}::{name}")
    }
}
fn prelude_symbols() -> BTreeMap<String, Symbol> {
    let mut symbols: BTreeMap<_, _> = [
        "inner",
        "clone",
        "clone_immut",
        "len",
        "byte_size",
        "panic",
        "assert",
        "print",
        "println",
        "Some",
        "None",
        "Ok",
        "Err",
        "Option",
        "Result",
        "Immut",
    ]
    .into_iter()
    .map(|name| (name.into(), Symbol::Declaration(format!("Prelude::{name}"))))
    .collect();
    for name in ["Array", "Map", "String", "Set", "Options", "Results"] {
        symbols.insert(name.into(), Symbol::Standard(name.into()));
    }
    symbols
}
fn is_implicit_prelude(name: &str, scope: &Scope) -> bool {
    prelude_symbols().get(name) == scope.names.get(name)
}
fn standard_namespace(path: &str) -> Option<&'static str> {
    Some(match path {
        "ril/prelude" => "Prelude",
        "ril/option" => "Options",
        "ril/result" => "Results",
        "ril/array" => "Array",
        "ril/map" => "Map",
        "ril/set" => "Set",
        "ril/string" => "String",
        "ril/order" => "Order",
        "ril/deque" => "Deque",
        "ril/heap" => "Heap",
        "ril/iter" => "Iter",
        "ril/unicode" => "Unicode",
        "ril/string_builder" => "StringBuilder",
        "ril/num" => "Num",
        "ril/math" => "Math",
        "ril/bytes" => "Bytes",
        "ril/encoding/binary" => "Binary",
        "ril/encoding/hex" => "Hex",
        "ril/crypto" => "Crypto",
        "ril/os" => "Os",
        "ril/path" => "Path",
        "ril/io" => "Io",
        "ril/file" => "File",
        "ril/env" => "Env",
        "ril/process" => "Process",
        "ril/time" => "Time",
        "ril/clock" => "Clock",
        "ril/random" => "Random",
        "ril/concurrent" => "Concurrent",
        "ril/concurrent/channel" => "Channel",
        "ril/parallel" => "Parallel",
        "ril/test" => "Test",
        _ => return None,
    })
}

/// Distinguish a declared standard export with an unfinished contract from a
/// misspelled source name. This registry never admits arbitrary namespace tails.
pub(crate) fn known_standard_identity(name: &str) -> bool {
    let Some((namespace, member)) = name.split_once("::") else {
        return false;
    };
    let path = match namespace {
        "Prelude" => "ril/prelude",
        "Options" => "ril/option",
        "Results" => "ril/result",
        "Array" => "ril/array",
        "Map" => "ril/map",
        "Set" => "ril/set",
        "String" => "ril/string",
        "Order" => "ril/order",
        "Deque" => "ril/deque",
        "Heap" => "ril/heap",
        "Iter" => "ril/iter",
        "Unicode" => "ril/unicode",
        "StringBuilder" => "ril/string_builder",
        "Num" => "ril/num",
        "Math" => "ril/math",
        "Bytes" => "ril/bytes",
        "Binary" => "ril/encoding/binary",
        "Hex" => "ril/encoding/hex",
        "Crypto" => "ril/crypto",
        "Os" => "ril/os",
        "Path" => "ril/path",
        "Io" => "ril/io",
        "File" => "ril/file",
        "Env" => "ril/env",
        "Process" => "ril/process",
        "Time" => "ril/time",
        "Clock" => "ril/clock",
        "Random" => "ril/random",
        "Concurrent" => "ril/concurrent",
        "Channel" => "ril/concurrent/channel",
        "Parallel" => "ril/parallel",
        "Test" => "ril/test",
        _ => return false,
    };
    standard_exports(path)
        .iter()
        .any(|export| standard_identity(namespace, export) == name)
        || (namespace == "Prelude" && matches!(member, "Some" | "None" | "Ok" | "Err"))
        || matches!(
            name,
            "Order::Ordering::Less"
                | "Order::Ordering::Equal"
                | "Order::Ordering::Greater"
                | "Num::NumError::InvalidSyntax"
                | "Num::NumError::OutOfRange"
                | "Num::NumError::InvalidRadix"
                | "Binary::ByteOrder::Little"
                | "Binary::ByteOrder::Big"
                | "Binary::BinaryError::UnexpectedEnd"
                | "Binary::BinaryError::Overflow"
                | "Binary::BinaryError::NonCanonical"
                | "Time::TimeError::OutOfRange"
                | "Time::TimeError::DifferentClock"
                | "Iter::Step::Done"
                | "Iter::Step::Yielded"
        )
}

fn standard_exports(path: &str) -> &'static [&'static str] {
    match path {
        "ril/prelude" => &[
            "Option",
            "Result",
            "Immut",
            "Options",
            "Results",
            "Array",
            "Map",
            "String",
            "Set",
            "inner",
            "clone",
            "clone_immut",
            "derive",
            "len",
            "byte_size",
            "panic",
            "assert",
            "print",
            "println",
        ],
        "ril/option" => &[
            "Option",
            "map",
            "and_then",
            "unwrap_or",
            "unwrap_or_else",
            "expect",
        ],
        "ril/result" => &["Result", "map", "map_err", "and_then", "recover", "expect"],
        "ril/array" => &[
            "Elem", "push", "pop", "insert", "remove", "truncate", "get", "first", "contains",
            "reverse", "concat", "map", "filter", "fold", "find", "any", "all", "for_each",
        ],
        "ril/map" => &[
            "Key", "Value", "from", "get", "set", "remove", "contains", "keys", "values", "entries",
        ],
        "ril/set" => &[
            "Set",
            "Elem",
            "from",
            "of",
            "insert",
            "remove",
            "contains",
            "values",
            "union",
            "intersect",
            "diff",
        ],
        "ril/string" => &[
            "split",
            "trim",
            "contains",
            "starts_with",
            "ends_with",
            "replace",
            "find",
            "slice",
            "concat",
            "join",
            "lines",
            "scalar_at",
            "scalars",
            "utf8",
            "byte_len",
            "byte_offset",
            "scalar_offset",
        ],
        "ril/order" => &[
            "Ordering",
            "Ops",
            "sorted",
            "binary_search",
            "compare_int",
            "compare_str",
            "compare_bytes",
            "total_f64",
        ],
        "ril/deque" => &[
            "Deque",
            "new",
            "len",
            "push_front",
            "push_back",
            "pop_front",
            "pop_back",
            "values",
        ],
        "ril/heap" => &["Heap", "new", "len", "push", "pop", "peek"],
        "ril/iter" => &[
            "Step", "Source", "Cursor", "cursor", "pull", "collect", "fold", "take", "map",
            "filter", "indexed",
        ],
        "ril/unicode" => &[
            "DecodeError",
            "ScalarError",
            "decode_utf8",
            "from_scalar",
            "is_white_space",
            "is_alphabetic",
            "is_decimal_digit",
            "is_xid_start",
            "is_xid_continue",
            "lowercase",
            "uppercase",
        ],
        "ril/string_builder" => &[
            "Builder",
            "new",
            "append",
            "append_scalar",
            "clear",
            "to_string",
        ],
        "ril/num" => &[
            "NumError",
            "parse_int",
            "parse_bigint",
            "parse_f64",
            "parse_i8",
            "parse_i16",
            "parse_i32",
            "parse_i64",
            "parse_u8",
            "parse_u16",
            "parse_u32",
            "parse_u64",
            "parse_f32",
            "format_int",
            "format_bigint",
            "format_f64",
            "format_i8",
            "format_i16",
            "format_i32",
            "format_i64",
            "format_u8",
            "format_u16",
            "format_u32",
            "format_u64",
            "format_f32",
            "convert",
        ],
        "ril/math" => &[
            "PI",
            "TAU",
            "PI_F32",
            "TAU_F32",
            "sqrt",
            "floor",
            "ceil",
            "round",
            "abs",
            "is_nan",
            "is_finite",
            "min",
            "max",
            "sqrt_f32",
            "floor_f32",
            "ceil_f32",
            "round_f32",
            "abs_f32",
            "is_nan_f32",
            "is_finite_f32",
            "min_f32",
            "max_f32",
        ],
        "ril/bytes" => &["from_array", "to_array", "slice", "concat", "find", "at"],
        "ril/encoding/binary" => &[
            "ByteOrder",
            "BinaryError",
            "Cursor",
            "cursor",
            "remaining",
            "read_u8",
            "read_i8",
            "read_u16",
            "read_i16",
            "read_u32",
            "read_i32",
            "read_u64",
            "read_i64",
            "read_f32",
            "read_f64",
            "read_bytes",
            "read_uleb128",
            "write_u8",
            "write_i8",
            "write_u16",
            "write_i16",
            "write_u32",
            "write_i32",
            "write_u64",
            "write_i64",
            "write_f32",
            "write_f64",
            "write_bytes",
            "write_uleb128",
        ],
        "ril/encoding/hex" => &["HexError", "encode", "decode"],
        "ril/crypto" => &["sha256", "sha256_bytes"],
        "ril/os" => &[
            "NativeString",
            "NativeError",
            "Platform",
            "platform",
            "from_string",
            "to_string",
            "from_posix_bytes",
            "posix_bytes",
            "from_windows_units",
            "windows_units",
            "compare",
        ],
        "ril/path" => &[
            "Path",
            "from_string",
            "from_native",
            "native",
            "to_string",
            "join",
            "parent",
            "file_name",
            "extension",
            "is_absolute",
            "normalize_lexical",
            "compare",
        ],
        "ril/io" => &[
            "ErrorKind",
            "IoError",
            "ReadChunk",
            "WriteProgress",
            "ReadOps",
            "WriteOps",
            "read_all",
            "write_all",
            "stdin_read",
            "stdout_write",
            "stderr_write",
            "write_stdout",
            "write_stderr",
            "error_text",
            "ReadBuffer",
            "WriteBuffer",
            "read_buffer",
            "write_buffer",
            "read_buffered",
            "write_buffered",
            "flush",
        ],
        "ril/file" => &[
            "Handle",
            "OpenMode",
            "SeekFrom",
            "Metadata",
            "FileKind",
            "Entry",
            "open",
            "open_path",
            "read",
            "read_chunk",
            "write",
            "seek",
            "sync",
            "close",
            "read_bytes",
            "read_text",
            "write_bytes",
            "write_text",
            "metadata",
            "read_dir",
            "create_dir",
            "create_dir_all",
            "remove_file",
            "remove_dir",
            "rename",
            "canonicalize",
            "temp_file",
            "with_file",
        ],
        "ril/env" => &["args", "get", "all", "current_dir", "temp_dir"],
        "ril/process" => &[
            "Input",
            "OutputMode",
            "Command",
            "ExitStatus",
            "Output",
            "ProcessError",
            "Child",
            "command",
            "run",
            "spawn",
            "wait",
            "terminate",
            "with_child",
            "success",
        ],
        "ril/time" => &[
            "Duration",
            "Timestamp",
            "Instant",
            "TimeError",
            "duration_nanos",
            "timestamp",
            "add",
            "elapsed",
            "monotonic",
            "sleep",
        ],
        "ril/clock" => &["now"],
        "ril/random" => &["Rng", "seeded", "next_u64", "below", "entropy"],
        "ril/concurrent" => &[
            "Scope",
            "Task",
            "scope",
            "PanicInfo",
            "UnwindCause",
            "DoubleFaultInfo",
            "TaskFault",
        ],
        "ril/concurrent/channel" => &[
            "Sender",
            "Receiver",
            "Detached",
            "ChannelError",
            "bounded",
            "send",
            "recv",
            "close",
            "detach",
            "attach",
        ],
        "ril/parallel" => &[
            "map",
            "map_bounded",
            "find",
            "first",
            "any",
            "fold",
            "join",
            "join3",
            "for_each",
        ],
        "ril/test" => &["assert_eq", "assert_ne", "assert_some", "assert_ok"],
        _ => &[],
    }
}

fn direct_callable(ty: &TypeExpr, program: &Program, seen: &mut BTreeSet<String>) -> bool {
    match &ty.kind {
        TypeKind::Callable { .. } => true,
        TypeKind::Name { path, .. } if path.len() == 1 && seen.insert(path[0].clone()) => program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) if declaration.name == path[0] => {
                    declaration.value.as_ref()
                }
                _ => None,
            })
            .is_some_and(|value| direct_callable(value, program, seen)),
        _ => false,
    }
}
fn invalid_callback_exchange(
    ty: &TypeExpr,
    program: &Program,
    seen: &mut BTreeSet<String>,
) -> bool {
    match &ty.kind {
        TypeKind::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(|parameter| {
                parameter.mode != ParameterMode::Read
                    || parameter
                        .ty
                        .as_ref()
                        .is_some_and(|ty| contains_callable(ty, program, &mut BTreeSet::new()))
            }) || result
                .as_ref()
                .is_some_and(|ty| contains_callable(ty, program, &mut BTreeSet::new()))
        }
        TypeKind::Name { path, .. } if path.len() == 1 && seen.insert(path[0].clone()) => program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) if declaration.name == path[0] => {
                    declaration.value.as_ref()
                }
                _ => None,
            })
            .is_some_and(|value| invalid_callback_exchange(value, program, seen)),
        _ => false,
    }
}
fn contains_callable(ty: &TypeExpr, program: &Program, seen: &mut BTreeSet<String>) -> bool {
    match &ty.kind {
        TypeKind::Callable { .. } => true,
        TypeKind::Name { path, arguments } => {
            arguments
                .iter()
                .any(|arg| contains_callable(arg, program, &mut seen.clone()))
                || (path.len() == 1
                    && seen.insert(path[0].clone())
                    && program
                        .statements
                        .iter()
                        .any(|statement| match &statement.kind {
                            StmtKind::Type(declaration) if declaration.name == path[0] => {
                                declaration
                                    .value
                                    .as_ref()
                                    .is_some_and(|value| contains_callable(value, program, seen))
                                    || declaration.variants.iter().any(|variant| {
                                        variant.payload.as_ref().is_some_and(|payload| {
                                            contains_callable(payload, program, &mut seen.clone())
                                        })
                                    })
                            }
                            _ => false,
                        }))
        }
        TypeKind::Optional(inner)
        | TypeKind::Array { element: inner, .. }
        | TypeKind::Rest(inner) => contains_callable(inner, program, seen),
        TypeKind::Map { key, value } => {
            contains_callable(key, program, &mut seen.clone())
                || contains_callable(value, program, seen)
        }
        TypeKind::Tuple(items) => items
            .iter()
            .any(|item| contains_callable(item, program, &mut seen.clone())),
        TypeKind::Record { fields, row } => {
            fields
                .iter()
                .any(|field| contains_callable(&field.ty, program, &mut seen.clone()))
                || row
                    .as_ref()
                    .is_some_and(|row| contains_callable(row, program, seen))
        }
        _ => false,
    }
}

fn collect_imports<'a>(statements: &'a [Stmt], imports: &mut Vec<&'a UseDeclaration>) {
    for statement in statements {
        match &statement.kind {
            StmtKind::Use(import) => imports.push(import),
            StmtKind::Function(function) => {
                if let Some(body) = &function.body {
                    collect_imports(&body.statements, imports);
                    collect_imports(&body.where_items, imports);
                }
            }
            StmtKind::Binding(binding) => collect_expr_imports(&binding.value, imports),
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                collect_expr_imports(expression, imports)
            }
            StmtKind::Assignment { target, value, .. } => {
                collect_expr_imports(target, imports);
                collect_expr_imports(value, imports);
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    collect_expr_imports(&arm.body, imports);
                }
            }
            _ => {}
        }
    }
}
fn collect_expr_imports<'a>(expr: &'a Expr, imports: &mut Vec<&'a UseDeclaration>) {
    match &expr.kind {
        ExprKind::Block(block) | ExprKind::Loop(block) => {
            collect_imports(&block.statements, imports);
            collect_imports(&block.where_items, imports);
        }
        ExprKind::Lambda { body, .. } => collect_expr_imports(body, imports),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_expr_imports(condition, imports);
            collect_expr_imports(then_branch, imports);
            if let Some(branch) = else_branch {
                collect_expr_imports(branch, imports);
            }
        }
        ExprKind::Match { value, arms, .. } => {
            collect_expr_imports(value, imports);
            for arm in arms {
                collect_expr_imports(&arm.body, imports);
            }
        }
        ExprKind::While { condition, body } => {
            collect_expr_imports(condition, imports);
            collect_imports(&body.statements, imports);
        }
        ExprKind::For { iterable, body, .. } => {
            collect_expr_imports(iterable, imports);
            collect_imports(&body.statements, imports);
        }
        ExprKind::Call { callee, arguments } => {
            collect_expr_imports(callee, imports);
            for argument in arguments {
                collect_expr_imports(&argument.value, imports);
            }
        }
        ExprKind::Unary { operand, .. } => collect_expr_imports(operand, imports),
        ExprKind::Binary { left, right, .. } => {
            collect_expr_imports(left, imports);
            collect_expr_imports(right, imports);
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                collect_expr_imports(item, imports);
            }
        }
        ExprKind::Record { fields, spread, .. } => {
            for field in fields {
                collect_expr_imports(&field.value, imports);
            }
            if let Some(spread) = spread {
                collect_expr_imports(spread, imports);
            }
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation { expression, .. } = part {
                    collect_expr_imports(expression, imports);
                }
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn root_constructor_owners_cannot_impersonate_prelude_identities() {
        let analyze = |source: &str| {
            let project = resolve(vec![unit("root.ril", 0, source)], FileId(0));
            assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
            let evaluated = crate::static_eval::evaluate(
                &project.program,
                ril_compiler_core::target::TargetLayout::POINTER64,
            );
            assert!(
                evaluated.diagnostics.is_empty() && evaluated.unsupported.is_empty(),
                "{:?} {:?}",
                evaluated.diagnostics,
                evaluated.unsupported
            );
            crate::sema::analyze_project(&evaluated.program, FileId(0), &[])
        };
        let outcome = analyze(
            "type Prelude{Some(int),None}\nfn example(){let value=Prelude::Some(7);match value{Prelude::Some(n)->assert(n==7),Prelude::None->()};let optional:?int=Some(8);assert(optional is Some(8))}",
        );
        assert!(
            outcome.program.is_some(),
            "{:?} {:?}",
            outcome.diagnostics,
            outcome.unsupported
        );
        let facts = outcome.program.unwrap();
        assert!(
            facts
                .facts()
                .constructors
                .values()
                .any(|constructor| constructor.tag == "Ril__Module0Prelude::Some")
        );
        assert!(
            facts
                .facts()
                .constructors
                .values()
                .any(|constructor| constructor.tag == "Ril__Module0Prelude::None")
        );
        assert!(
            !facts
                .facts()
                .constructors
                .values()
                .any(|constructor| constructor.tag == "Prelude::Some")
        );
        let wrong =
            analyze("type Prelude{Some(int)}\nfn example(value:Prelude){assert(value is Some(_))}");
        assert!(
            wrong
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            wrong.diagnostics,
            wrong.unsupported
        );
        let raw = ril_syntax::parse(
            "type Prelude{Some(int)}\nfn example(value:Prelude){assert(value is Some(_))}",
        );
        let raw_outcome = crate::sema::analyze(&raw.program, FileId(0));
        assert!(
            raw_outcome
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "raw public verification bypass: {:?} {:?}",
            raw_outcome.diagnostics,
            raw_outcome.unsupported
        );
        for name in ["Some", "None", "Ok", "Err"] {
            let source = format!(
                "type {name}(int)\nfn example(){{let value={name}(7);assert(inner(value)==7);let optional:?int=Prelude::Some(8);assert(optional is Prelude::Some(8))}}"
            );
            let result = analyze(&source);
            assert!(
                result.program.is_some(),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
            assert!(
                result
                    .program
                    .unwrap()
                    .facts()
                    .constructors
                    .values()
                    .any(|constructor| constructor.tag == format!("Ril__Module0{name}"))
            );
        }
    }
    #[test]
    fn local_sum_candidates_and_type_pattern_binders_have_lexical_identity() {
        let project = resolve(
            vec![unit(
                "root.ril",
                0,
                "type Outer { Item(int) }\nfn example() { let value = Item(1)\nwhere\ntype Inner { Item(str) }\n}",
            )],
            FileId(0),
        );
        assert!(
            project
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0206"),
            "{:?}",
            project.diagnostics
        );
        let project = resolve(
            vec![unit(
                "root.ril",
                0,
                "fn example() { let value = Local(1)\nwhere\ntype Inner { Local(int) }\n}",
            )],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        assert!(format!("{:?}", project.program).contains("\"Inner\", \"Local\""));
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper::{Inspect}\ntype Value = Inspect<Option<int>>\nmeta let _ = assert(type<Value> == type<int>)",
                ),
                unit(
                    "helper.ril",
                    1,
                    "pub type U = str\npub type Inspect = \\T -> match type<T> { type<Option<let U>> -> type<U>, _ -> type<never> }",
                ),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let evaluated = crate::static_eval::evaluate(
            &project.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        assert!(
            evaluated.diagnostics.is_empty(),
            "{:?}",
            evaluated.diagnostics
        );
        assert!(
            evaluated.unsupported.is_empty(),
            "{:?}",
            evaluated.unsupported
        );
    }
    fn unit(name: &str, file: u32, text: &str) -> ModuleUnit {
        let parsed = ril_syntax::parse_file(text, FileId(file));
        assert!(parsed.is_ok(), "{name}: {:?}", parsed.diagnostics);
        ModuleUnit {
            path: PathBuf::from("/ril-module-tests").join(name),
            file: FileId(file),
            program: parsed.program,
            is_declaration: name.ends_with(".d.ril"),
        }
    }
    fn functions(project: &ResolvedProject) -> Vec<&Function> {
        project
            .program
            .statements
            .iter()
            .filter_map(|statement| {
                if let StmtKind::Function(function) = &statement.kind {
                    Some(function)
                } else {
                    None
                }
            })
            .collect()
    }
    #[test]
    fn aliases_and_reexports_preserve_one_real_definition() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use public\nuse public::{answer as renamed}\npub fn main() { assert(Public::answer() == renamed()) }",
                ),
                unit("helper.ril", 1, "pub fn answer() -> int { 7 }"),
                unit("public.ril", 2, "pub use helper::{answer}"),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let funcs = functions(&project);
        assert_eq!(funcs.len(), 2);
        let main = funcs
            .iter()
            .find(|function| function.name == "main")
            .unwrap();
        let debug = format!("{:?}", main.body);
        assert_eq!(debug.matches("ril__module_1_answer").count(), 2);
    }
    #[test]
    fn private_and_missing_members_have_distinct_diagnostics() {
        for (member, code) in [("secret", "E0201"), ("missing", "E0209")] {
            let root = format!("use helper::{{{member}}}");
            let project = resolve(
                vec![
                    unit("root.ril", 0, &root),
                    unit("helper.ril", 1, "fn secret() {}"),
                ],
                FileId(0),
            );
            assert!(
                project.diagnostics.iter().any(|d| d.code == code),
                "{:?}",
                project.diagnostics
            );
        }
    }
    #[test]
    fn module_state_annotations_follow_canonical_identity() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use counter\nfn advance() &Counter::advance { Counter::advance() }",
                ),
                unit(
                    "counter.ril",
                    1,
                    "var count = 0\npub fn advance() &{mut count} { count += 1 }",
                ),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty());
        let funcs = functions(&project);
        assert_eq!(funcs[0].annotations[0].text, "&{mut ril__module_1_count}");
        assert_eq!(funcs[1].annotations[0].text, "&ril__module_1_advance");
    }
    #[test]
    fn local_import_and_shadowing_stay_lexical() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "fn local_scope(answer: int) -> int { { use helper::{answer as call}; call() }; answer }\nfn outside() { call() }",
                ),
                unit("helper.ril", 1, "pub fn answer() -> int { 7 }"),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let funcs = functions(&project);
        let scoped = funcs
            .iter()
            .find(|function| function.name == "local_scope")
            .unwrap();
        assert!(format!("{:?}", scoped.body).contains("ril__module_1_answer"));
        let outside = funcs
            .iter()
            .find(|function| function.name == "outside")
            .unwrap();
        assert!(format!("{:?}", outside.body).contains("Name(\"call\")"));
    }
    #[test]
    fn signature_type_declarations_shadow_imports_before_the_signature_is_resolved() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper::{Token}\nfn example(value: Token) -> Token\nwhere\n    type Token = int\n{ value }",
                ),
                unit("helper.ril", 1, "pub type Token(str)"),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let example = functions(&project)
            .into_iter()
            .find(|function| function.name == "example")
            .unwrap();
        assert!(
            matches!(&example.parameters[0].ty.as_ref().unwrap().kind,TypeKind::Name{path,..} if path == &["Token"])
        );
        assert!(
            matches!(&example.return_type.as_ref().unwrap().kind,TypeKind::Name{path,..} if path == &["Token"])
        );
    }
    #[test]
    fn foreign_module_shapes_and_exchange_contracts_are_checked() {
        for (text, code) in [
            ("pub fn answer() -> int { 1 }", "E0901"),
            ("pub let VALUE: int = 1", "E0901"),
            ("pub var value: int", "E0901"),
            ("pub fn edit(mut data: []int) &mut", "E0908"),
            ("pub fn get() -> { callback: fn() -> () }", "E0908"),
        ] {
            let project = resolve(
                vec![
                    unit("root.ril", 0, "use foreign"),
                    unit("foreign.d.ril", 1, text),
                ],
                FileId(0),
            );
            assert!(
                project.diagnostics.iter().any(|d| d.code == code),
                "{text}: {:?}",
                project.diagnostics
            );
        }
        let project = resolve(vec![unit("root.ril", 0, "fn missing()")], FileId(0));
        assert!(project.diagnostics.iter().any(|d| d.code == "E0902"));
    }
    #[test]
    fn interpolation_references_keep_module_identity_and_source_spans() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper\nfn read() -> str { Helper::text() }",
                ),
                unit(
                    "helper.ril",
                    1,
                    "let VALUE = 7\npub fn text() -> str { \"value={VALUE}\" }",
                ),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty());
        let function = functions(&project)[0];
        let debug = format!("{:?}", function.body);
        assert!(debug.contains("RIL__MODULE_1_VALUE"));
        assert!(debug.contains("FileId(1)"));
    }

    #[test]
    fn root_definitions_cannot_shadow_another_modules_prelude_or_private_scope() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper\nfn clone(value: int) -> int { value }\nfn secret() {}",
                ),
                unit(
                    "helper.ril",
                    1,
                    "pub fn copy(value: int) -> int { clone(value) }\nfn bad() { secret() }",
                ),
            ],
            FileId(0),
        );
        assert!(
            project
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0204")
        );
        let function = functions(&project)
            .into_iter()
            .find(|function| function.name == "ril__module_1_copy")
            .unwrap();
        assert!(format!("{:?}", function.body).contains("Prelude"));
    }
    #[test]
    fn source_names_cannot_capture_generated_module_identities() {
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper\nfn ril_module_1_answer()->int {99}\nfn example()->int { let ril_module_1_answer=\\->88; Helper::answer() }",
                ),
                unit("helper.ril", 1, "pub fn answer()->int {7}"),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let imported = functions(&project)
            .into_iter()
            .find(|function| function.name == "ril__module_1_answer")
            .unwrap();
        assert_ne!(imported.name, "ril_module_1_answer");
        let evaluated = crate::static_eval::evaluate(
            &project.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        assert!(
            evaluated.diagnostics.is_empty(),
            "{:?}",
            evaluated.diagnostics
        );
        assert!(
            evaluated.unsupported.is_empty(),
            "{:?}",
            evaluated.unsupported
        );
        let example = evaluated
            .program
            .statements
            .iter()
            .find_map(|statement| {
                if let StmtKind::Function(function) = &statement.kind
                    && function.name == "example"
                {
                    Some(function)
                } else {
                    None
                }
            })
            .unwrap();
        let StmtKind::Expr { expression, .. } = &example.body.as_ref().unwrap().statements[1].kind
        else {
            panic!()
        };
        assert!(
            matches!(&expression.kind,ExprKind::Call {callee,..} if matches!(&callee.kind,ExprKind::Name(name) if name=="ril__module_1_answer") || matches!(&callee.kind,ExprKind::Path(path) if path==&["ril__module_1_answer"]))
        );
        let verified = crate::sema::analyze_project(&evaluated.program, FileId(0), &[]);
        assert!(
            verified.program.is_some(),
            "{:?} {:?}",
            verified.diagnostics,
            verified.unsupported
        );
    }
    #[test]
    fn user_effects_and_lexical_type_binders_cannot_impersonate_standard_namespaces() {
        for source in [
            "fn example<Heap>() {let mut value=Heap::new<int>();Heap::push(mut value,1)}",
            "type Heap(int)\nfn example() {let value=Heap::new<int>()}",
        ] {
            let project = resolve(vec![unit("root.ril", 0, source)], FileId(0));
            assert!(
                project
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0204"),
                "{source}: {:?}",
                project.diagnostics
            );
        }
        let project = resolve(
            vec![
                unit(
                    "root.ril",
                    0,
                    "use helper\neff Num {parse_int()->int}\nfn read()->int @Num {Num::parse_int()}",
                ),
                unit(
                    "helper.ril",
                    1,
                    "use ril/num\npub fn read()->bool {Num::parse_int(\"1\") is Ok(1)}",
                ),
            ],
            FileId(0),
        );
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let evaluated = crate::static_eval::evaluate(
            &project.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        assert!(
            evaluated.diagnostics.is_empty(),
            "{:?}",
            evaluated.diagnostics
        );
        assert!(
            evaluated.unsupported.is_empty(),
            "{:?}",
            evaluated.unsupported
        );
        let verified = crate::sema::analyze_project(&evaluated.program, FileId(0), &[]);
        assert!(
            verified.program.is_some(),
            "{:?} {:?}",
            verified.diagnostics,
            verified.unsupported
        );
    }

    #[test]
    fn whole_positive_corpus_resolves_modules_without_erasing_names() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let cases = ril_test::discover_cases(&repository.join("tests")).unwrap();
        let mut failures = vec![];
        for case in cases {
            if case.meta.mode == ril_test::Mode::CheckFail {
                continue;
            }
            let mut units = vec![];
            let mut root = FileId(0);
            for file in case.files.iter().filter(|file| file.name.ends_with(".ril")) {
                let id = units.len() as u32;
                if file.name == case.root {
                    root = FileId(id);
                }
                units.push(unit(
                    &file.name,
                    id,
                    std::str::from_utf8(&file.bytes).unwrap(),
                ));
            }
            let project = resolve(units, root);
            if !project.diagnostics.is_empty() {
                failures.push(format!("{}: {:?}", case.id, project.diagnostics));
            }
        }
        assert!(
            failures.is_empty(),
            "{} cases failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn module_negative_corpus_has_required_boundary_diagnostics() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let cases = ril_test::discover_cases(&repository.join("tests")).unwrap();
        let mut failures = vec![];
        for case in cases {
            let expected: Vec<_> = case
                .errors
                .iter()
                .filter(|code| {
                    matches!(
                        code.as_str(),
                        "E0201" | "E0208" | "E0209" | "E0901" | "E0902" | "E0908"
                    )
                })
                .collect();
            if expected.is_empty() {
                continue;
            }
            let mut units = vec![];
            let mut root = FileId(0);
            for file in case.files.iter().filter(|file| file.name.ends_with(".ril")) {
                let id = FileId(units.len() as u32);
                if file.name == case.root {
                    root = id;
                }
                let parsed = ril_syntax::parse_file(std::str::from_utf8(&file.bytes).unwrap(), id);
                units.push(ModuleUnit {
                    path: PathBuf::from("/ril-module-tests").join(&file.name),
                    file: id,
                    program: parsed.program,
                    is_declaration: file.name.ends_with(".d.ril"),
                });
            }
            let project = resolve(units, root);
            for code in expected {
                if !project
                    .diagnostics
                    .iter()
                    .any(|diagnostic| &diagnostic.code == code)
                {
                    failures.push(format!(
                        "{} expected {code}: {:?}",
                        case.id, project.diagnostics
                    ));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "{} cases failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}
#[test]
fn standard_export_availability_never_guesses_namespace_suffixes() {
    for name in [
        "File::open",
        "Order::sorted",
        "Deque::Deque",
        "Prelude::Some",
        "Binary::ByteOrder::Big",
    ] {
        assert!(known_standard_identity(name), "{name}");
    }
    for name in [
        "File::missing",
        "Other::open",
        "Deque::missing",
        "File::open::invented",
        "Order::Ordering::Invented",
    ] {
        assert!(!known_standard_identity(name), "{name}");
    }
}
