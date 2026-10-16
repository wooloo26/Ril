//! Termination is independent of effect rows. Unresolved call dependencies do
//! not prove finite computation, and ordinary divergent functions remain legal.
use ril_compiler_core::{
    diagnostic::{Diagnostic, Label, Severity},
    source::Span,
};
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
mod budget;
mod callbacks;
pub use budget::BudgetTerminationWitness;
mod descent;
#[cfg(test)]
mod proofs;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Judgment {
    pub may_diverge: bool,
    pub unresolved: bool,
    pub callable_parameters: BTreeSet<usize>,
}
impl Judgment {
    fn include(&mut self, other: Self) {
        self.may_diverge |= other.may_diverge;
        self.unresolved |= other.unresolved;
        self.callable_parameters.extend(other.callable_parameters);
    }
    fn unresolved() -> Self {
        Self {
            unresolved: true,
            ..Default::default()
        }
    }
}
#[derive(Debug, Default)]
pub struct Analysis {
    pub judgments: BTreeMap<String, Judgment>,
    pub diagnostics: Vec<Diagnostic>,
    pub unsupported: Vec<crate::sema::UnsupportedFeature>,
    pub budget_witnesses: Vec<BudgetTerminationWitness>,
}
pub fn analyze(program: &Program) -> Analysis {
    analyze_with_budgets(program, &[])
}
/// Only semantic coverage certificates can replace an unbounded invocation
/// with a finite budget boundary. The public analysis has no certificates.
pub(crate) fn analyze_with_budgets(
    program: &Program,
    budget_proofs: &[crate::sema::BudgetProof],
) -> Analysis {
    let functions: BTreeMap<_, _> = program
        .statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StmtKind::Function(function) => Some((function.name.clone(), function.clone())),
            _ => None,
        })
        .collect();
    let mut analysis = Analysis {
        judgments: functions
            .keys()
            .map(|name| (name.clone(), Judgment::unresolved()))
            .collect(),
        ..Default::default()
    };
    let descending = descent::proved_components(&functions);
    for name in descending {
        analysis.judgments.insert(name, Judgment::default());
    }
    // A proved descending component starts at the finite lattice bottom. Other
    // recursive components retain Unknown; a cycle alone never proves halt.
    for _ in 0..=functions.len() {
        let previous = analysis.judgments.clone();
        for (name, function) in &functions {
            let mut visitor = Visitor {
                functions: &functions,
                summaries: &previous,
                budget_proofs,
                budget_witnesses: vec![],
                parameters: function
                    .parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(i, p)| {
                        if let PatternKind::Name(name) = &p.pattern.kind {
                            Some((name.clone(), i))
                        } else {
                            None
                        }
                    })
                    .collect(),
                aliases: BTreeMap::new(),
                handlers: BTreeMap::new(),
                callback_arguments: Default::default(),
                contextual_calls: BTreeSet::new(),
                depth: 0,
                diagnostics: vec![],
                unsupported: vec![],
            };
            let mut result = function
                .body
                .as_ref()
                .map_or_else(Judgment::unresolved, |body| visitor.block(body));
            for parameter in &function.parameters {
                if let Some(default) = &parameter.default {
                    result.include(visitor.expression(default));
                }
            }
            analysis.judgments.insert(name.clone(), result);
        }
        if previous == analysis.judgments {
            break;
        }
    }
    for (name, function) in &functions {
        let judgment = &analysis.judgments[name];
        if function.is_halt {
            if function.annotations.iter().any(|annotation| {
                !matches!(annotation.text.replace(' ', "").as_str(), "&{}" | "@{}")
            }) {
                analysis.diagnostics.push(diagnostic(
                    "E0821",
                    function.span,
                    "halt function has outward effects or capabilities",
                ));
            }
            if judgment.may_diverge {
                analysis.diagnostics.push(diagnostic(
                    "E0820",
                    function.span,
                    "halt invocation includes a computation without a finite termination proof",
                ));
            }
            if judgment.unresolved {
                analysis.unsupported.push(crate::sema::UnsupportedFeature {
                    span: function.span,
                    description: "termination proof for recursive, handled or indirect computation"
                        .into(),
                });
            }
        }
        let mut visitor = Visitor {
            functions: &functions,
            summaries: &analysis.judgments,
            budget_proofs,
            budget_witnesses: vec![],
            parameters: function
                .parameters
                .iter()
                .enumerate()
                .filter_map(|(i, p)| {
                    if let PatternKind::Name(name) = &p.pattern.kind {
                        Some((name.clone(), i))
                    } else {
                        None
                    }
                })
                .collect(),
            aliases: BTreeMap::new(),
            handlers: BTreeMap::new(),
            callback_arguments: Default::default(),
            contextual_calls: BTreeSet::new(),
            depth: 0,
            diagnostics: vec![],
            unsupported: vec![],
        };
        if let Some(body) = &function.body {
            visitor.block(body);
        }
        analysis.diagnostics.extend(visitor.diagnostics);
        analysis.unsupported.extend(visitor.unsupported);
        analysis.budget_witnesses.extend(visitor.budget_witnesses);
    }
    analysis
}
/// Prove the computation performed by invoking a callable expression. Lambda
/// creation alone is finite; this entry checks its body as required for cleanup.
pub fn analyze_expression(program: &Program, expression: &Expr) -> Judgment {
    analyze_expression_with_context(program, expression, &[], BTreeMap::new())
}
pub(crate) fn analyze_expression_with_context(
    program: &Program,
    expression: &Expr,
    budget_proofs: &[crate::sema::BudgetProof],
    aliases: BTreeMap<String, Expr>,
) -> Judgment {
    analyze_expression_with_handlers(program, expression, budget_proofs, aliases, BTreeMap::new())
}
pub(crate) fn analyze_expression_with_handlers(
    program: &Program,
    expression: &Expr,
    budget_proofs: &[crate::sema::BudgetProof],
    aliases: BTreeMap<String, Expr>,
    handlers: BTreeMap<String, Judgment>,
) -> Judgment {
    let analysis = analyze_with_budgets(program, budget_proofs);
    let functions = program
        .statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StmtKind::Function(function) => Some((function.name.clone(), function.clone())),
            _ => None,
        })
        .collect();
    let mut visitor = Visitor {
        functions: &functions,
        summaries: &analysis.judgments,
        budget_proofs,
        budget_witnesses: vec![],
        parameters: BTreeMap::new(),
        aliases,
        handlers,
        callback_arguments: Default::default(),
        contextual_calls: BTreeSet::new(),
        depth: 0,
        diagnostics: vec![],
        unsupported: vec![],
    };
    visitor.callable(expression, &mut BTreeSet::new())
}
fn diagnostic(code: &str, span: Span, message: &str) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        severity: Severity::Error,
        message: message.into(),
        labels: vec![Label {
            span,
            message: message.into(),
        }],
        causes: vec![],
    }
}

fn standard_termination(name: &str) -> Option<Judgment> {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    let parallel = match name {
        "Parallel::map" | "Parallel::find" | "Parallel::first" | "Parallel::any"
        | "Parallel::for_each" => Some(vec![1]),
        "Parallel::map_bounded" => Some(vec![2]),
        "Parallel::fold" => Some(vec![1, 2, 3]),
        "Parallel::join" => Some(vec![0, 1]),
        "Parallel::join3" => Some(vec![0, 1, 2]),
        _ => None,
    };
    if let Some(callbacks) = parallel {
        return Some(Judgment {
            callable_parameters: callbacks.into_iter().collect(),
            ..Default::default()
        });
    }
    let callback = match name {
        "Array::map"
        | "Array::filter"
        | "Array::find"
        | "Array::any"
        | "Array::all"
        | "Array::for_each"
        | "Options::map"
        | "Options::and_then"
        | "Options::unwrap_or_else"
        | "Results::map"
        | "Results::map_err"
        | "Results::and_then"
        | "Results::recover" => Some(1),
        "Array::fold" => Some(2),
        _ => None,
    };
    if let Some(index) = callback {
        return Some(Judgment {
            callable_parameters: [index].into(),
            ..Default::default()
        });
    }
    let finite = matches!(
        name,
        "assert"
            | "panic"
            | "len"
            | "clone"
            | "clone_immut"
            | "Some"
            | "Ok"
            | "Err"
            | "Array::push"
            | "Array::pop"
            | "Array::truncate"
            | "Array::insert"
            | "Array::remove"
            | "Array::reverse"
            | "Array::concat"
            | "Array::first"
            | "Array::contains"
            | "Array::get"
            | "Map::from"
            | "Map::get"
            | "Map::set"
            | "Map::contains"
            | "Map::remove"
            | "Map::keys"
            | "Map::values"
            | "Map::entries"
            | "Set::from"
            | "Set::contains"
            | "Set::insert"
            | "Set::remove"
            | "Set::values"
            | "Set::union"
            | "Set::intersect"
            | "Set::diff"
            | "Options::unwrap_or"
            | "Options::expect"
            | "Results::expect"
            | "Order::compare_int"
            | "Order::compare_str"
            | "Order::compare_bytes"
            | "Order::total_f64"
            | "Order::sorted"
            | "Order::binary_search"
            | "Deque::new"
            | "Deque::len"
            | "Deque::push_front"
            | "Deque::push_back"
            | "Deque::pop_front"
            | "Deque::pop_back"
            | "Deque::values"
            | "Heap::new"
            | "Heap::len"
            | "Heap::push"
            | "Heap::peek"
            | "Heap::pop"
            | "Time::duration_nanos"
            | "Os::platform"
            | "Os::from_string"
            | "Os::to_string"
            | "Os::from_posix_bytes"
            | "Os::posix_bytes"
            | "Os::from_windows_units"
            | "Os::windows_units"
            | "Os::compare"
            | "Path::from_string"
            | "Path::from_native"
            | "Path::native"
            | "Path::to_string"
            | "Path::join"
            | "Path::parent"
            | "Path::file_name"
            | "Path::extension"
            | "Path::is_absolute"
            | "Path::normalize_lexical"
            | "Path::compare"
            | "File::SeekFrom::Start"
            | "File::SeekFrom::Current"
            | "File::SeekFrom::End"
            | "Io::error_text"
            | "Io::read_buffer"
            | "Io::write_buffer"
            | "Process::command"
            | "Process::success"
            | "Time::timestamp"
            | "Time::add"
            | "Time::elapsed"
            | "Random::seeded"
            | "Random::next_u64"
            | "Random::below"
            | "Test::assert_eq"
            | "Test::assert_ne"
            | "Test::assert_some"
            | "Test::assert_ok"
            | "String::split"
            | "String::trim"
            | "String::contains"
            | "String::starts_with"
            | "String::ends_with"
            | "String::replace"
            | "String::find"
            | "String::slice"
            | "String::concat"
            | "String::join"
            | "String::lines"
            | "String::scalar_at"
            | "String::scalars"
            | "String::utf8"
            | "String::byte_len"
            | "String::byte_offset"
            | "String::scalar_offset"
            | "StringBuilder::new"
            | "StringBuilder::append"
            | "StringBuilder::append_scalar"
            | "StringBuilder::clear"
            | "StringBuilder::to_string"
            | "Unicode::decode_utf8"
            | "Unicode::from_scalar"
            | "Unicode::lowercase"
            | "Unicode::uppercase"
            | "Unicode::is_white_space"
            | "Unicode::is_alphabetic"
            | "Unicode::is_decimal_digit"
            | "Unicode::is_xid_start"
            | "Unicode::is_xid_continue"
            | "Bytes::from_array"
            | "Bytes::to_array"
            | "Bytes::slice"
            | "Bytes::concat"
            | "Bytes::find"
            | "Bytes::at"
            | "Hex::encode"
            | "Hex::decode"
            | "Crypto::sha256"
            | "Crypto::sha256_bytes"
            | "Binary::cursor"
            | "Binary::remaining"
    ) || name.strip_prefix("Math::").is_some_and(|op| {
        matches!(
            op.strip_suffix("_f32").unwrap_or(op),
            "sqrt" | "floor" | "ceil" | "round" | "abs" | "is_nan" | "is_finite" | "min" | "max"
        )
    }) || name.strip_prefix("Num::").is_some_and(|op| {
        op == "convert"
            || ["parse_", "format_"].iter().any(|prefix| {
                op.strip_prefix(prefix).is_some_and(|ty| {
                    matches!(
                        ty,
                        "int"
                            | "bigint"
                            | "i8"
                            | "u8"
                            | "i16"
                            | "u16"
                            | "i32"
                            | "u32"
                            | "i64"
                            | "u64"
                            | "f32"
                            | "f64"
                    )
                })
            })
    }) || name.strip_prefix("Binary::").is_some_and(|op| {
        ["read_", "write_"].iter().any(|prefix| {
            op.strip_prefix(prefix).is_some_and(|ty| {
                matches!(
                    ty,
                    "u8" | "i8"
                        | "u16"
                        | "i16"
                        | "u32"
                        | "i32"
                        | "u64"
                        | "i64"
                        | "f32"
                        | "f64"
                        | "bytes"
                        | "uleb128"
                )
            })
        })
    });
    finite.then(Judgment::default)
}

struct Visitor<'a> {
    functions: &'a BTreeMap<String, Function>,
    summaries: &'a BTreeMap<String, Judgment>,
    budget_proofs: &'a [crate::sema::BudgetProof],
    budget_witnesses: Vec<budget::BudgetTerminationWitness>,
    parameters: BTreeMap<String, usize>,
    aliases: BTreeMap<String, Expr>,
    /// A direct operation can be bounded only by an already proved handler arm.
    /// Arms execute outside their own selected handler, so a recursive request
    /// never obtains its proof by assuming the handler being constructed.
    handlers: BTreeMap<String, Judgment>,
    callback_arguments: std::sync::Arc<BTreeMap<String, callbacks::ArgumentContext>>,
    contextual_calls: BTreeSet<String>,
    depth: u16,
    diagnostics: Vec<Diagnostic>,
    unsupported: Vec<crate::sema::UnsupportedFeature>,
}
impl Visitor<'_> {
    fn standard_argument<'a>(
        &self,
        callee: &Expr,
        arguments: &'a [Argument],
        index: usize,
    ) -> Option<&'a Argument> {
        fn name(
            visitor: &Visitor<'_>,
            expression: &Expr,
            seen: &mut BTreeSet<String>,
        ) -> Option<String> {
            match &expression.kind {
                ExprKind::Name(label) if !visitor.parameters.contains_key(label) => {
                    if let Some(alias) = visitor.aliases.get(label) {
                        if !seen.insert(label.clone()) {
                            return None;
                        }
                        name(visitor, alias, seen)
                    } else if !visitor.functions.contains_key(label) {
                        Some(label.clone())
                    } else {
                        None
                    }
                }
                ExprKind::Path(path) => Some(path.join("::")),
                ExprKind::Generic { base, .. } => name(visitor, base, seen),
                _ => None,
            }
        }
        let labels = name(self, callee, &mut BTreeSet::new())
            .and_then(|name| crate::sema::parallel_parameter_labels(&name));
        let Some(labels) = labels else {
            return arguments.get(index);
        };
        let mut ordered = vec![None; labels.len()];
        for argument in arguments {
            let slot = if let Some(label) = &argument.label {
                labels.iter().position(|parameter| *parameter == label)
            } else {
                ordered.iter().position(Option::is_none)
            }?;
            if ordered[slot].is_some() {
                return None;
            }
            ordered[slot] = Some(argument);
        }
        ordered.get(index).copied().flatten()
    }
    fn standard_callable(
        &self,
        expression: &Expr,
        seen: &mut BTreeSet<String>,
    ) -> Option<Judgment> {
        match &expression.kind {
            ExprKind::Name(name) if !self.parameters.contains_key(name) => {
                if let Some(alias) = self.aliases.get(name)
                    && seen.insert(name.clone())
                {
                    self.standard_callable(alias, seen)
                } else if !self.aliases.contains_key(name) && !self.functions.contains_key(name) {
                    standard_termination(name)
                } else {
                    None
                }
            }
            ExprKind::Path(path) => standard_termination(&path.join("::")),
            ExprKind::Generic { base, .. } => self.standard_callable(base, seen),
            _ => None,
        }
    }
    fn block(&mut self, block: &Block) -> Judgment {
        let aliases = self.aliases.clone();
        let parameters = self.parameters.clone();
        let handlers = self.handlers.clone();
        let mut result = Judgment::default();
        for statement in block.statements.iter().chain(&block.where_items) {
            if let StmtKind::Function(function) = &statement.kind {
                // Local function bodies require a separate lexical summary. In
                // particular a same-spelled global cannot stand in for them.
                self.aliases.insert(
                    function.name.clone(),
                    Expr {
                        hir_id: None,
                        kind: ExprKind::Ambient,
                        span: function.span,
                    },
                );
            }
        }
        for statement in &block.statements {
            result.include(match &statement.kind {
                StmtKind::Binding(binding) => {
                    let mut judgment = self.expression(&binding.value);
                    judgment.include(self.pattern(&binding.pattern));
                    if let Some(fallback) = &binding.fallback {
                        judgment.include(self.expression(fallback));
                    }
                    self.mask_pattern(&binding.pattern);
                    if let PatternKind::Name(name) = &binding.pattern.kind {
                        let value = if binding.mode.is_reassignable() {
                            Expr {
                                hir_id: None,
                                kind: ExprKind::Ambient,
                                span: binding.value.span,
                            }
                        } else {
                            binding.value.clone()
                        };
                        self.aliases.insert(name.clone(), value);
                    }
                    judgment
                }
                StmtKind::Assignment { target, value, .. } => {
                    let mut j = self.expression(target);
                    j.include(self.expression(value));
                    j
                }
                StmtKind::Expr { expression, .. } => self.expression(expression),
                StmtKind::Handler(arms) => {
                    let outer = self.handlers.clone();
                    let mut judgment = Judgment::default();
                    let mut selected = Vec::new();
                    for arm in arms {
                        // The selected group is masked throughout each arm.
                        self.handlers = outer.clone();
                        let aliases = self.aliases.clone();
                        let parameters = self.parameters.clone();
                        for parameter in &arm.parameters {
                            self.mask_pattern(&parameter.pattern);
                        }
                        let arm_judgment = self.expression(&arm.body);
                        self.aliases = aliases;
                        self.parameters = parameters;
                        judgment.include(arm_judgment.clone());
                        let name = match &arm.operation.kind {
                            ExprKind::Path(path) => Some(path.join("::")),
                            _ => None,
                        };
                        if let Some(name) = name {
                            selected.push((name, arm_judgment));
                        } else {
                            judgment.unresolved = true;
                        }
                    }
                    self.handlers = outer;
                    self.handlers.extend(selected);
                    judgment
                }
                StmtKind::HandlerApplication(_) => Judgment::unresolved(),
                _ => Judgment::default(),
            });
            if matches!(
                &statement.kind,
                StmtKind::Expr {
                    expression: Expr {
                        kind: ExprKind::Control {
                            operation: ControlOperation::Return,
                            ..
                        },
                        ..
                    },
                    ..
                }
            ) {
                break;
            }
        }
        self.aliases = aliases;
        self.parameters = parameters;
        self.handlers = handlers;
        result
    }
    fn callable(&mut self, expression: &Expr, seen: &mut BTreeSet<String>) -> Judgment {
        if let Some(judgment) = self.standard_callable(expression, &mut BTreeSet::new()) {
            return judgment;
        }
        match &expression.kind {
            ExprKind::Name(name) => {
                if let Some(actual) = self.actual_callback(name, seen) {
                    return actual;
                }
                if let Some(parameter) = self.parameters.get(name) {
                    return Judgment {
                        callable_parameters: [*parameter].into(),
                        ..Default::default()
                    };
                }
                if let Some(alias) = self.aliases.get(name).cloned() {
                    return if seen.insert(name.clone()) {
                        self.callable(&alias, seen)
                    } else {
                        Judgment::unresolved()
                    };
                }
                if let Some(summary) = self.summaries.get(name) {
                    return summary.clone();
                }
                match name.strip_prefix("Prelude::").unwrap_or(name) {
                    "assert" | "panic" | "len" | "clone" | "clone_immut" | "Some" | "Ok"
                    | "Err" => Judgment::default(),
                    _ => Judgment::unresolved(),
                }
            }
            ExprKind::Path(path) => {
                let name = path.join("::");
                if let Some(handler) = self.handlers.get(&name) {
                    return handler.clone();
                }
                self.summaries.get(&name).cloned().unwrap_or_else(|| {
                    if matches!(
                        name.as_str(),
                        "Prelude::assert"
                            | "Prelude::panic"
                            | "Prelude::len"
                            | "Prelude::clone"
                            | "Prelude::clone_immut"
                            | "Prelude::Some"
                            | "Prelude::Ok"
                            | "Prelude::Err"
                            | "Array::push"
                            | "Array::pop"
                            | "Array::truncate"
                            | "Array::insert"
                            | "Array::remove"
                            | "Array::reverse"
                            | "Array::clear"
                            | "Array::get"
                            | "Array::set"
                    ) {
                        Judgment::default()
                    } else {
                        Judgment::unresolved()
                    }
                })
            }
            ExprKind::Accessor(_) => Judgment::default(),
            ExprKind::Lambda {
                parameters, body, ..
            } => {
                let aliases = self.aliases.clone();
                let outer_parameters = self.parameters.clone();
                // A lambda's own callable argument has not been instantiated by
                // this invocation proof. Captured outer parameters keep theirs.
                for parameter in parameters {
                    self.mask_pattern(&parameter.pattern);
                }
                let result = self.expression(body);
                self.aliases = aliases;
                self.parameters = outer_parameters;
                result
            }
            ExprKind::Generic { base, .. } => self.callable(base, seen),
            _ => Judgment::unresolved(),
        }
    }
    fn named_callable(&self, expression: &Expr, seen: &mut BTreeSet<String>) -> Option<String> {
        match &expression.kind {
            ExprKind::Name(name) => {
                if self.aliases.contains_key(name) && seen.insert(name.clone()) {
                    self.aliases
                        .get(name)
                        .and_then(|value| self.named_callable(value, seen))
                } else if !self.aliases.contains_key(name)
                    && !self.parameters.contains_key(name)
                    && self.functions.contains_key(name)
                {
                    Some(name.clone())
                } else {
                    None
                }
            }
            ExprKind::Path(path) => {
                let name = path.join("::");
                self.functions.contains_key(&name).then_some(name)
            }
            ExprKind::Generic { base, .. } => self.named_callable(base, seen),
            _ => None,
        }
    }
    fn expression(&mut self, expression: &Expr) -> Judgment {
        if self.depth >= 128 {
            return Judgment::unresolved();
        }
        self.depth += 1;
        let result = self.expression_inner(expression);
        self.depth -= 1;
        result
    }
    fn known_optional(&self, expression: &Expr, seen: &mut BTreeSet<String>) -> bool {
        match &expression.kind {
            ExprKind::Name(name)
                if name == "None"
                    && !self.aliases.contains_key(name)
                    && !self.parameters.contains_key(name) =>
            {
                true
            }
            ExprKind::Name(name) if seen.insert(name.clone()) => self
                .aliases
                .get(name)
                .is_some_and(|value| self.known_optional(value, seen)),
            ExprKind::Call { callee, .. } => {
                let name = match &callee.kind {
                    ExprKind::Name(name) => Some(name.clone()),
                    ExprKind::Path(path) => Some(path.join("::")),
                    _ => None,
                };
                name.is_some_and(|name| {
                    (!self.aliases.contains_key(&name)
                        && !self.parameters.contains_key(&name)
                        && !self.functions.contains_key(&name)
                        && matches!(name.as_str(), "Some" | "Prelude::Some"))
                        || (!self.aliases.contains_key(&name)
                            && !self.parameters.contains_key(&name)
                            && self
                                .functions
                                .get(&name)
                                .and_then(|function| function.return_type.as_ref())
                                .is_some_and(|ty| matches!(ty.kind, TypeKind::Optional(_))))
                })
            }
            _ => false,
        }
    }
    fn mask_pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.parameters.remove(name);
                self.aliases.insert(
                    name.clone(),
                    Expr {
                        hir_id: None,
                        kind: ExprKind::Ambient,
                        span: pattern.span,
                    },
                );
            }
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.mask_pattern(item);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    self.mask_pattern(&field.pattern);
                }
                if let Some(name) = rest_binding {
                    self.parameters.remove(name);
                    self.aliases.insert(
                        name.clone(),
                        Expr {
                            hir_id: None,
                            kind: ExprKind::Ambient,
                            span: pattern.span,
                        },
                    );
                }
            }
            PatternKind::Type {
                binder: Some(name), ..
            } => {
                self.parameters.remove(name);
                self.aliases.insert(
                    name.clone(),
                    Expr {
                        hir_id: None,
                        kind: ExprKind::Ambient,
                        span: pattern.span,
                    },
                );
            }
            PatternKind::Mode { pattern, .. } => self.mask_pattern(pattern),
            _ => {}
        }
    }
    fn pattern(&mut self, pattern: &Pattern) -> Judgment {
        let mut result = Judgment::default();
        match &pattern.kind {
            PatternKind::Value(value) => result.include(self.expression(value)),
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    result.include(self.pattern(item));
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    result.include(self.pattern(&field.pattern));
                }
            }
            PatternKind::Mode { pattern, .. } => result.include(self.pattern(pattern)),
            _ => {}
        }
        result
    }
    fn expression_inner(&mut self, expression: &Expr) -> Judgment {
        let mut result = Judgment::default();
        match &expression.kind {
            ExprKind::Literal(_)
            | ExprKind::Name(_)
            | ExprKind::Path(_)
            | ExprKind::TypeValue(_)
            | ExprKind::Lambda { .. }
            | ExprKind::Accessor(_) => {}
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        result.include(self.expression(expression));
                    }
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    result.include(self.expression(item));
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    result.include(self.expression(key));
                    result.include(self.expression(value));
                }
            }
            ExprKind::Record {
                fields,
                spread,
                members,
                ..
            } => {
                if members.is_empty() {
                    if let Some(spread) = spread {
                        result.include(self.expression(spread));
                    }
                    for field in fields {
                        result.include(self.expression(&field.value));
                    }
                } else {
                    for member in members {
                        result.include(self.expression(match member {
                            RecordMember::Field(field) => &field.value,
                            RecordMember::Spread(value) => value,
                        }));
                    }
                }
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    result.include(self.expression(start));
                }
                if let Some(end) = end {
                    result.include(self.expression(end));
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Field { base: operand, .. }
            | ExprKind::Generic { base: operand, .. } => result.include(self.expression(operand)),
            ExprKind::Is { value, pattern } => {
                result.include(self.expression(value));
                result.include(self.pattern(pattern));
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                result.include(self.expression(left));
                if !(operator == "&&"
                    && matches!(left.kind, ExprKind::Literal(Literal::Bool(false)))
                    || operator == "||"
                        && matches!(left.kind, ExprKind::Literal(Literal::Bool(true))))
                {
                    result.include(self.expression(right));
                }
                if operator == "??"
                    && !self.known_optional(left, &mut BTreeSet::new())
                    && !matches!(right.kind, ExprKind::Literal(_))
                {
                    // Result fallback invokes its selected recovery. An unknown
                    // family cannot prove that a callable fallback is only data.
                    result.include(self.callable(right, &mut BTreeSet::new()));
                }
            }
            ExprKind::Index {
                base: left,
                index: right,
                ..
            }
            | ExprKind::ComputedField {
                base: left,
                key: right,
            } => {
                result.include(self.expression(left));
                result.include(self.expression(right));
            }
            ExprKind::Call { callee, arguments } => {
                result.include(self.expression(callee));
                for argument in arguments {
                    result.include(self.expression(&argument.value));
                }
                if let Some(bounded) = self.budget_call(expression.span, arguments, &result) {
                    result.include(bounded);
                    return result;
                }
                if let Some(called) = self.standard_callable(callee, &mut BTreeSet::new()) {
                    for index in called.callable_parameters {
                        if let Some(argument) = self.standard_argument(callee, arguments, index) {
                            result.include(self.callable(&argument.value, &mut BTreeSet::new()));
                        } else {
                            result.unresolved = true;
                        }
                    }
                    return result;
                }
                let called = self.callable(callee, &mut BTreeSet::new());
                let contextual_name = self.named_callable(callee, &mut BTreeSet::new());
                if (!called.callable_parameters.is_empty()
                    || (called.unresolved && !self.handlers.is_empty()))
                    && let Some(name) = &contextual_name
                    && !self.functions[name].is_halt
                    && let Some(actual) = self.contextual_call(name, arguments)
                {
                    result.include(actual);
                    return result;
                }
                result.may_diverge |= called.may_diverge;
                result.unresolved |= called.unresolved;
                let named = self.named_callable(callee, &mut BTreeSet::new());
                if named
                    .as_ref()
                    .is_none_or(|name| !self.functions.contains_key(name))
                {
                    result
                        .callable_parameters
                        .extend(called.callable_parameters);
                    return result;
                }
                let halt = named
                    .as_ref()
                    .and_then(|name| self.functions.get(name))
                    .is_some_and(|function| function.is_halt);
                for parameter in called.callable_parameters {
                    let Some(argument) = arguments.get(parameter) else {
                        result.unresolved = true;
                        continue;
                    };
                    let actual = self.callable(&argument.value, &mut BTreeSet::new());
                    if halt && actual.may_diverge {
                        self.diagnostics.push(diagnostic(
                            "E0534",
                            argument.span,
                            "halt callback argument has no finite invocation proof",
                        ));
                    }
                    if halt && actual.unresolved {
                        self.unsupported.push(crate::sema::UnsupportedFeature {
                            span: argument.span,
                            description: "termination of an indirect halt callback argument".into(),
                        });
                    }
                    result.include(actual);
                }
            }
            ExprKind::Block(block) => result.include(self.block(block)),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                result.include(self.expression(condition));
                match condition.kind {
                    ExprKind::Literal(Literal::Bool(true)) => {
                        result.include(self.expression(then_branch))
                    }
                    ExprKind::Literal(Literal::Bool(false)) => {
                        if let Some(branch) = else_branch {
                            result.include(self.expression(branch));
                        }
                    }
                    _ => {
                        result.include(self.expression(then_branch));
                        if let Some(branch) = else_branch {
                            result.include(self.expression(branch));
                        }
                    }
                }
            }
            ExprKind::Loop(block) => {
                result.include(self.block(block));
                if !block.statements.iter().any(|statement| {
                    matches!(
                        &statement.kind,
                        StmtKind::Expr {
                            expression: Expr {
                                kind: ExprKind::Control {
                                    operation: ControlOperation::Last | ControlOperation::Return,
                                    ..
                                },
                                ..
                            },
                            ..
                        }
                    )
                }) {
                    result.may_diverge = true;
                }
            }
            ExprKind::While { condition, body } => {
                result.include(self.expression(condition));
                if !matches!(condition.kind, ExprKind::Literal(Literal::Bool(false))) {
                    result.include(self.block(body));
                    result.unresolved = true;
                }
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                result.include(self.expression(iterable));
                let aliases = self.aliases.clone();
                let parameters = self.parameters.clone();
                self.mask_pattern(pattern);
                result.include(self.block(body));
                self.aliases = aliases;
                self.parameters = parameters;
                if !matches!(
                    iterable.kind,
                    ExprKind::Array(_)
                        | ExprKind::Range {
                            start: Some(_),
                            end: Some(_),
                            ..
                        }
                ) {
                    result.unresolved = true;
                }
            }
            ExprKind::Match { value, arms, .. } => {
                result.include(self.expression(value));
                for arm in arms {
                    result.include(self.pattern(&arm.pattern));
                    let aliases = self.aliases.clone();
                    let parameters = self.parameters.clone();
                    self.mask_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        result.include(self.expression(guard));
                    }
                    result.include(self.expression(&arm.body));
                    self.aliases = aliases;
                    self.parameters = parameters;
                }
            }
            ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    result.include(self.expression(value));
                }
            }
            _ => result.unresolved = true,
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn divergence_and_halt_callback_requirements_survive_named_calls() {
        let parsed = ril_syntax::parse(
            "halt fn invoke(action: fn() -> ()) { action() }\nfn spin() { loop {} }\nfn example() { invoke(spin) }",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let analysis = analyze(&parsed.program);
        assert!(analysis.diagnostics.iter().any(|d| d.code == "E0534"));
        assert!(analysis.judgments["spin"].may_diverge);
        let parsed = ril_syntax::parse("halt fn forever() { loop {} }");
        assert_eq!(analyze(&parsed.program).diagnostics[0].code, "E0820");
    }
    #[test]
    fn every_record_spread_retains_its_current_invocation_dependency() {
        let parsed = ril_syntax::parse(
            "fn spin() -> { a: int } { loop {} }\nfn done() -> { b: int } { .{ b: 1 } }\nhalt fn joined() -> { a: int, b: int } { .{ ..spin(), ..done() } }",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        assert!(
            analyze(&parsed.program)
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0820")
        );
    }
    #[test]
    fn finite_collection_traversal_requires_the_actual_callback_and_never_a_stale_var_initializer()
    {
        let parsed = ril_syntax::parse("halt fn finite()->[]int{Array::map([1,2],\\x:int->x+1)}");
        assert!(parsed.is_ok());
        let analysis = analyze(&parsed.program);
        assert!(
            !analysis.judgments["finite"].may_diverge && !analysis.judgments["finite"].unresolved
        );
        let parsed = ril_syntax::parse(
            "fn spin(_x:int)->int{loop{}}\nhalt fn bad()->[]int{Array::map([1],spin)}",
        );
        let analysis = analyze(&parsed.program);
        assert!(
            analysis
                .diagnostics
                .iter()
                .any(|error| error.code == "E0820")
        );
        let parsed = ril_syntax::parse(
            "fn spin(_x:int)->int{loop{}}\nhalt fn changed()->[]int{var action=\\x:int->x;action=spin;Array::map([1],action)}",
        );
        assert!(analyze(&parsed.program).judgments["changed"].unresolved);
    }
}
