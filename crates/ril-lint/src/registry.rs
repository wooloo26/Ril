//! Static registry of all Ril lint rules (36 rules + 4 directive meta-lints).

use ril_source::fix::{DiagnosticTag, FixSafety};

use crate::config::{LintCategory, LintLevel};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LintStage {
    Syntax,
    Hir,
    Typed,
    Access,
}

#[derive(Clone, Copy, Debug)]
pub struct LintDescriptor {
    pub id: &'static str,
    pub category: LintCategory,
    pub default_level: LintLevel,
    pub stage: LintStage,
    pub summary: &'static str,
    pub fix_safety: Option<FixSafety>,
    pub tags: &'static [DiagnosticTag],
}

const NO_TAGS: &[DiagnosticTag] = &[];
const UNNECESSARY: &[DiagnosticTag] = &[DiagnosticTag::Unnecessary];

// Directive meta-lints (4)
pub const CANNOT_SUPPRESS_ERROR: LintDescriptor = LintDescriptor {
    id: "cannot_suppress_error",
    category: LintCategory::Correctness,
    default_level: LintLevel::Deny,
    stage: LintStage::Syntax,
    summary: "Spec-normative compiler errors (E0xxx) cannot be suppressed by lint directives",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const UNKNOWN_LINT_RULE: LintDescriptor = LintDescriptor {
    id: "unknown_lint_rule",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Lint directive references an unknown rule or category",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const UNFULFILLED_EXPECT: LintDescriptor = LintDescriptor {
    id: "unfulfilled_expect",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "`-- ril: expect(...)` directive matched zero findings in its scope",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const MALFORMED_LINT_DIRECTIVE: LintDescriptor = LintDescriptor {
    id: "malformed_lint_directive",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Syntax or placement error in `-- ril:` / `--! ril:` directive",
    fix_safety: None,
    tags: NO_TAGS,
};

// Correctness (9)
pub const SELF_COMPARISON: LintDescriptor = LintDescriptor {
    id: "self_comparison",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Comparing a side-effect-free expression to itself (exempting `f64` NaN checks)",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const SELF_ASSIGNMENT: LintDescriptor = LintDescriptor {
    id: "self_assignment",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Assigning a place directly to itself",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const IDENTICAL_BRANCHES: LintDescriptor = LintDescriptor {
    id: "identical_branches",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "`if` / `else` branches or `match` arms have identical bodies",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const ERASING_OP: LintDescriptor = LintDescriptor {
    id: "erasing_op",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Pure integer operation that always evaluates to zero (`x * 0`, `x & 0`, `x ^ x`, `x - x`)",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const SUSPICIOUS_EMPTY_DEFER: LintDescriptor = LintDescriptor {
    id: "suspicious_empty_defer",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Empty `defer {}` or `defer ()` cleanup does nothing",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const UNUSED_EFFECT_HANDLER: LintDescriptor = LintDescriptor {
    id: "unused_effect_handler",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Access,
    summary: "`with` effect handler is never exercised in its governed scope",
    fix_safety: Some(FixSafety::Unsafe),
    tags: UNNECESSARY,
};
pub const REDUNDANT_WITH_SHADOW: LintDescriptor = LintDescriptor {
    id: "redundant_with_shadow",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "`with` handler is immediately shadowed by another handler for the same operation",
    fix_safety: Some(FixSafety::Unsafe),
    tags: UNNECESSARY,
};
pub const UNUSED_PURE_EXPR: LintDescriptor = LintDescriptor {
    id: "unused_pure_expr",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Access,
    summary: "Pure non-unit expression statement value is discarded",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const IGNORED_OPTION_RESULT: LintDescriptor = LintDescriptor {
    id: "ignored_option_result",
    category: LintCategory::Correctness,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Optional `?T` expression statement discarded without `let _ = ...`",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};

// Unused (7)
pub const UNUSED_IMPORT: LintDescriptor = LintDescriptor {
    id: "unused_import",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Imported module or symbol is never referenced",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};
pub const UNUSED_BINDING: LintDescriptor = LintDescriptor {
    id: "unused_binding",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Plain local binding is never read (prefix with `_` if intentional)",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};
pub const UNUSED_PARAM: LintDescriptor = LintDescriptor {
    id: "unused_param",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Function parameter is never referenced (prefix with `_` if intentional)",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};
pub const UNUSED_PRIVATE_ITEM: LintDescriptor = LintDescriptor {
    id: "unused_private_item",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Private declaration is never referenced",
    fix_safety: Some(FixSafety::Unsafe),
    tags: UNNECESSARY,
};
pub const UNREACHABLE_PUB: LintDescriptor = LintDescriptor {
    id: "unreachable_pub",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "`pub` item inside a private `sub` cannot be reached outside the module",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};
pub const UNREACHABLE_CODE: LintDescriptor = LintDescriptor {
    id: "unreachable_code",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Statement or branch can never execute",
    fix_safety: Some(FixSafety::Unsafe),
    tags: UNNECESSARY,
};
pub const UNUSED_GENERIC_PARAM: LintDescriptor = LintDescriptor {
    id: "unused_generic_param",
    category: LintCategory::Unused,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Generic parameter on function or type alias is never used",
    fix_safety: Some(FixSafety::Unsafe),
    tags: UNNECESSARY,
};

// Idiom (13)
pub const REDUNDANT_CLONE: LintDescriptor = LintDescriptor {
    id: "redundant_clone",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Access,
    summary: "`clone(...)` on an already deeply immutable snapshot received as immutable",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const NOOP_DERIVE: LintDescriptor = LintDescriptor {
    id: "noop_derive",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Access,
    summary: "`derive` updater performs no writes on its `Derived<T>` handle",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const PREFER_ACCESSOR_SHORTHAND: LintDescriptor = LintDescriptor {
    id: "prefer_accessor_shorthand",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Simple projection closure `\\x -> x.field` can use `\\.field` shorthand",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const PREFER_SHORTHAND_RECORD: LintDescriptor = LintDescriptor {
    id: "prefer_shorthand_record",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Record field `.{ x: x }` can use shorthand `.{ x }`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const MANUAL_QUESTION_MARK: LintDescriptor = LintDescriptor {
    id: "manual_question_mark",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Trivial `match` propagating `Err`/`None` can use `?`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const MANUAL_FALLBACK: LintDescriptor = LintDescriptor {
    id: "manual_fallback",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Trivial `match` providing fallback for `None`/`Err` can use `??`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const MANUAL_SAFE_NAV: LintDescriptor = LintDescriptor {
    id: "manual_safe_nav",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "`match opt { Some(v) -> Some(v.f); None -> None }` can use `opt?.f`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const PREFER_LET_ELSE: LintDescriptor = LintDescriptor {
    id: "prefer_let_else",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "`let x = match e { Pat(v) -> v; _ -> return ... }` can use `let ... else`",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const REDUNDANT_LET_DISCARD: LintDescriptor = LintDescriptor {
    id: "redundant_let_discard",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "`let _ = expr` where `expr` already has type `()`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const REDUNDANT_BOOL_BRANCH: LintDescriptor = LintDescriptor {
    id: "redundant_bool_branch",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Redundant boolean literal branch or comparison (`if c { true } else { false }`, `x == true`)",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const MATCH_ON_BOOL: LintDescriptor = LintDescriptor {
    id: "match_on_bool",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "`match` on `bool` can be written more clearly as `if / else`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const SINGLE_ARM_MATCH: LintDescriptor = LintDescriptor {
    id: "single_arm_match",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Single-action `match` on `?T` can use `if let`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const COLLAPSIBLE_IF: LintDescriptor = LintDescriptor {
    id: "collapsible_if",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Nested `if a { if b { ... } }` can be combined with `&&`",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const NEEDLESS_RETURN: LintDescriptor = LintDescriptor {
    id: "needless_return",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Explicit `return` on the final tail expression of a function",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const REDUNDANT_TRAILING_PARENS: LintDescriptor = LintDescriptor {
    id: "redundant_trailing_parens",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Empty `()` immediately before a trailing closure (`f() \\x -> ...` → `f \\x -> ...`)",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const REDUNDANT_CLOSURE: LintDescriptor = LintDescriptor {
    id: "redundant_closure",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Closure `\\x -> f(x)` can be replaced directly with `f`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const NEEDLESS_NOMINAL_ROUNDTRIP: LintDescriptor = LintDescriptor {
    id: "needless_nominal_roundtrip",
    category: LintCategory::Idiom,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Immediate wrap/unwrap round-trip (`inner(T::(x))` or `T::(inner(w))`)",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const REDUNDANT_CHECKED_ACCESS: LintDescriptor = LintDescriptor {
    id: "redundant_checked_access",
    category: LintCategory::Idiom,
    default_level: LintLevel::Allow,
    stage: LintStage::Typed,
    summary: "Checked `?[i]`/`?[k]` where Ril's DBM prover already proves bounds/membership",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const PANIC_IN_FALLIBLE_FN: LintDescriptor = LintDescriptor {
    id: "panic_in_fallible_fn",
    category: LintCategory::Idiom,
    default_level: LintLevel::Allow,
    stage: LintStage::Typed,
    summary: "Explicit `panic(...)` inside a function returning fallible `!<T, E>`",
    fix_safety: None,
    tags: NO_TAGS,
};

// Style (9)
pub const IMPORT_ORDER: LintDescriptor = LintDescriptor {
    id: "import_order",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Top-level `use` imports are not canonically grouped (`ril/` → deps → `pkg/`) and sorted",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const DUPLICATE_IMPORT_MODULE: LintDescriptor = LintDescriptor {
    id: "duplicate_import_module",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Multiple `use` statements import from the same module in the same scope",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const REDUNDANT_IMPORT_ALIAS: LintDescriptor = LintDescriptor {
    id: "redundant_import_alias",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Import alias matches the default imported name",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};
pub const REDUNDANT_PARENS: LintDescriptor = LintDescriptor {
    id: "redundant_parens",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Unnecessary parentheses around condition, return value, or single atom",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const SHADOWED_LIVE_BINDING: LintDescriptor = LintDescriptor {
    id: "shadowed_live_binding",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Hir,
    summary: "Inner binding shadows an outer live `var`/`mut`/`^mut`/`ref` binding",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const GLOB_IMPORT: LintDescriptor = LintDescriptor {
    id: "glob_import",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Syntax,
    summary: "Module-level wildcard `use M::*` risks name collisions on upstream additions",
    fix_safety: Some(FixSafety::Unsafe),
    tags: NO_TAGS,
};
pub const MISSING_DOC_COMMENT: LintDescriptor = LintDescriptor {
    id: "missing_doc_comment",
    category: LintCategory::Style,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Public declaration is missing a leading `--` documentation comment",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const NON_CANONICAL_FALLIBLE_TYPE: LintDescriptor = LintDescriptor {
    id: "non_canonical_fallible_type",
    category: LintCategory::Style,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Use idiomatic `!<T, E>` / `?T` instead of `Result<T, E>` / `Option<T>`",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};
pub const UNNECESSARY_CLOSURE_BRACES: LintDescriptor = LintDescriptor {
    id: "unnecessary_closure_braces",
    category: LintCategory::Style,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Single-expression closure `\\x -> { e }` does not need braces (when not before `|>` or `?`)",
    fix_safety: Some(FixSafety::Safe),
    tags: NO_TAGS,
};

// Perf & Complexity (6)
pub const CLONE_IN_LOOP: LintDescriptor = LintDescriptor {
    id: "clone_in_loop",
    category: LintCategory::Perf,
    default_level: LintLevel::Warn,
    stage: LintStage::Access,
    summary: "Deep `clone(...)` of a loop-invariant shared object inside a loop",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const STRING_CONCAT_IN_LOOP: LintDescriptor = LintDescriptor {
    id: "string_concat_in_loop",
    category: LintCategory::Perf,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Repeated string interpolation onto an outer `var` string inside a loop (O(n²))",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const DEEP_NESTING: LintDescriptor = LintDescriptor {
    id: "deep_nesting",
    category: LintCategory::Complexity,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Control-flow nesting depth exceeds `lint.options.max_nesting`",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const TOO_MANY_ARGUMENTS: LintDescriptor = LintDescriptor {
    id: "too_many_arguments",
    category: LintCategory::Complexity,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Function parameter count exceeds `lint.options.max_args`",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const LARGE_FUNCTION: LintDescriptor = LintDescriptor {
    id: "large_function",
    category: LintCategory::Complexity,
    default_level: LintLevel::Allow,
    stage: LintStage::Syntax,
    summary: "Function body line count exceeds `lint.options.max_lines`",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const UNEXPECTED_BEHAVIOR_IN_PUB: LintDescriptor = LintDescriptor {
    id: "unexpected_behavior_in_pub",
    category: LintCategory::Complexity,
    default_level: LintLevel::Allow,
    stage: LintStage::Access,
    summary: "Public function may implicitly panic, abort, or diverge",
    fix_safety: None,
    tags: NO_TAGS,
};
pub const REDUNDANT_PROOF_BASE_TYPE: LintDescriptor = LintDescriptor {
    id: "redundant_proof_base_type",
    category: LintCategory::Style,
    default_level: LintLevel::Warn,
    stage: LintStage::Typed,
    summary: "Base type before `|>` is redundant when the leading static proof uniquely determines it",
    fix_safety: Some(FixSafety::Safe),
    tags: UNNECESSARY,
};

pub const ALL_LINTS: &[&LintDescriptor] = &[
    &CANNOT_SUPPRESS_ERROR,
    &UNKNOWN_LINT_RULE,
    &UNFULFILLED_EXPECT,
    &MALFORMED_LINT_DIRECTIVE,
    &SELF_COMPARISON,
    &SELF_ASSIGNMENT,
    &IDENTICAL_BRANCHES,
    &ERASING_OP,
    &SUSPICIOUS_EMPTY_DEFER,
    &UNUSED_EFFECT_HANDLER,
    &REDUNDANT_WITH_SHADOW,
    &UNUSED_PURE_EXPR,
    &IGNORED_OPTION_RESULT,
    &UNUSED_IMPORT,
    &UNUSED_BINDING,
    &UNUSED_PARAM,
    &UNUSED_PRIVATE_ITEM,
    &UNREACHABLE_PUB,
    &UNREACHABLE_CODE,
    &UNUSED_GENERIC_PARAM,
    &REDUNDANT_CLONE,
    &NOOP_DERIVE,
    &PREFER_ACCESSOR_SHORTHAND,
    &PREFER_SHORTHAND_RECORD,
    &MANUAL_QUESTION_MARK,
    &MANUAL_FALLBACK,
    &MANUAL_SAFE_NAV,
    &PREFER_LET_ELSE,
    &REDUNDANT_LET_DISCARD,
    &REDUNDANT_BOOL_BRANCH,
    &MATCH_ON_BOOL,
    &SINGLE_ARM_MATCH,
    &COLLAPSIBLE_IF,
    &NEEDLESS_RETURN,
    &REDUNDANT_TRAILING_PARENS,
    &REDUNDANT_CLOSURE,
    &NEEDLESS_NOMINAL_ROUNDTRIP,
    &REDUNDANT_CHECKED_ACCESS,
    &PANIC_IN_FALLIBLE_FN,
    &IMPORT_ORDER,
    &DUPLICATE_IMPORT_MODULE,
    &REDUNDANT_IMPORT_ALIAS,
    &REDUNDANT_PARENS,
    &SHADOWED_LIVE_BINDING,
    &GLOB_IMPORT,
    &MISSING_DOC_COMMENT,
    &NON_CANONICAL_FALLIBLE_TYPE,
    &UNNECESSARY_CLOSURE_BRACES,
    &CLONE_IN_LOOP,
    &STRING_CONCAT_IN_LOOP,
    &DEEP_NESTING,
    &TOO_MANY_ARGUMENTS,
    &LARGE_FUNCTION,
    &UNEXPECTED_BEHAVIOR_IN_PUB,
    &REDUNDANT_PROOF_BASE_TYPE,
];

pub fn find_rule(id: &str) -> Option<&'static LintDescriptor> {
    ALL_LINTS.iter().copied().find(|d| d.id == id)
}

pub fn is_compiler_error_code(key: &str) -> bool {
    key.parse::<ril_source::diag::Code>().is_ok()
}

pub fn suggest_rule(input: &str) -> Option<&'static str> {
    let mut best: Option<(&'static str, usize)> = None;
    for desc in ALL_LINTS {
        let d = edit_distance(input, desc.id);
        if d <= 3 && best.is_none_or(|(_, bd)| d < bd) {
            best = Some((desc.id, d));
        }
    }
    for cat in LintCategory::ALL {
        let name = cat.as_str();
        let d = edit_distance(input, name);
        if d <= 3 && best.is_none_or(|(_, bd)| d < bd) {
            best = Some((name, d));
        }
    }
    best.map(|(s, _)| s)
}

fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0usize; b.len() + 1];
    for (i, &ca) in a.iter().enumerate() {
        if let Some(slot) = curr.first_mut() {
            *slot = i + 1;
        }
        for (j, &cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            let del = prev.get(j + 1).copied().unwrap_or(usize::MAX) + 1;
            let ins = curr.get(j).copied().unwrap_or(usize::MAX) + 1;
            let sub = prev.get(j).copied().unwrap_or(usize::MAX) + cost;
            if let Some(slot) = curr.get_mut(j + 1) {
                *slot = del.min(ins).min(sub);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev.last().copied().unwrap_or(usize::MAX)
}
