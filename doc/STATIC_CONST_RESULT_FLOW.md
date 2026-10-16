# Const integer roles in the static Result proof

Status: the v30 combined component gate passes on Windows and Linux: 25 targets,
679 Rust tests and one explicit ignored test per host. This includes all four
Result-flow groups, pointer32/64 Source/Core checks, and pointer64 native-IR
lowering. Both hosts also execute this fixture through the fresh native CLI.
Compiler Clippy passes with all targets and warnings denied. This is not a
whole-compiler completion or current full-corpus certificate.

`typing::const_int` owns the classified declaration IDs and immutable const
selections. The Result engine consumes only its checked visible binding views.
Each visible const has ordinary type `int`; a selected closed value can also
provide its integer value fact. An own universal binder has no selected value,
even when every observed call uses the same literal. Both static target layouts
remain explicit. These scalar facts contain no Result producer, permission,
origin, inspection, or freshness information.

`result_flow_consts.rs` seeds these views after installing a universal or actual
named scope. It writes directly to the ordinary environment: creating the
generic binding must not masquerade as an ordinary shadow. Actual invocation
preparation continues to use the same owner and selected scope as argument
typing and invocation.

Explicit const arguments follow their real generic parameter's value sort.
They do not enter the complete Type-source query used by Type arguments. Their
original syntax and lexical scope reach the same prepared selection solver;
retained generic callables that need a different captured-scope substitution
still retain the existing NI rather than borrowing a later shadow's binding.

Ordinary bindings and successful pattern bindings mask a same-spelled visible
const role. Historical ID selections remain immutable, so earlier closures and
frozen result contexts keep their own environment. Block, pattern-test, match
arm, loop-body and callable restoration restore both the ordinary environment
and its original bound-scope `Arc`. Failed match arms also restore their lexical
bindings; inspections and other actual path facts remain in the state.

The first scalar-only stage does not admit const-dependent array types or other
const-dependent Type syntax. That rejection must precede Source/result-context
normalization, including for a closed actual selection. An observed array length
cannot select a const parameter or turn a dynamic extent into a fixed extent.
The broader extent, key and constructor contracts remain in
`STATIC_GENERIC_SORTS_DESIGN.md`.

The registered `static_const_result_flow` target has four groups: complete
Source/Core/native-IR checks under pointer32/64 for block, pattern and loop
shadows; a transferred but uninspected Result requiring E0720; actual const 2
that cannot settle an obligation on another universal branch; and fresh versus
edited Session outcomes. The universal-branch check explicitly permits retained
NI and is only a nonauthorization regression in that case. Its positive native
adapter executes successfully on both hosts. The complete frozen native batch
has 17 executables, 22 Rust tests, 49 distinct positive Ril sources and 53 entry
executions per host, with all 19 artifact hashes unchanged. Evidence is under
`target/const-int-and-dependent-bound-native-{windows,linux}-v30`.

Preserved baselines in `target/static-const-int-*-before-v23.*` identify the old
frozen v21 CLI and record its hash. They show the earlier const-sort NI; they are
not a certificate for the newly registered compiler. The separate shadowed-debt
probe already reports E0720 with that old compiler and is not a newly discovered
authorization bug.
