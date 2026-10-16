# Numeric literal selection

Status: implementation in progress after the frozen v17 snapshot. This document
does not change SPEC. The implementation checkpoint below identifies the closed
paths; the rest remains a design contract, not a claim of support.

## Problem and normative rules

SPEC, Numeric Literals, requires a compatible context to select an unsuffixed
integer's type. Only when no such context exists does it default to target `int`.
An integer selected as floating-point rounds once to that format. Written
suffixes fix the type; already typed values do not undergo implicit promotion.
Integer range checks include an immediately applied minus. The floating-point
rules require nearest, ties-to-even, signed zero, and the stated IEEE widths.

The current checker parses an integer into host `i128` and checks its initial
`int` range before later context is available. Its contextual compatibility rules
also exclude integer-to-float selection. Core lowering has no corresponding
integer-to-float literal branch. Removing only that compatibility restriction
would leave an incorrect representation or a later lowering failure.

The probes under `target/numeric-context-probe/` preserve the current outcomes:

| Source initializer and receiving type | Current outcome | Required outcome |
| --- | --- | --- |
| `let x:f32=16777217` | E0301 | f32 `16777216.0` |
| `let x:f64=1` | E0301 | f64 `1.0` |
| `let x:f32=-16777217` | E0301 | f32 `-16777216.0` |
| `let x:[]f32=[16777217]` | E0301 | a float element rounded to `16777216.0` |
| `let x:u64=18446744073709551615` | premature int E0326 | exact u64 maximum |
| `let x:bigint=340282366920938463463374607431768211456` | i128-parser E0326 | exact bigint, 2^128 |
| that same integer in an f64 context | E0326 and E0301 | exact f64 2^128 |

These are false rejections, not demonstrated wrong native execution. The earlier
owned-AST span collision is a separate demonstrated wrongcode issue, now guarded
before verification. Its conservative ambiguity guard remains until typed syntax
identities replace diagnostic-span lookup.

## Selection contract

Use the sequence **exact source value and constraints -> selected type -> range
check or one rounding -> committed typed value** in both ordinary and static
checking. Host integer width must not decide whether a well-formed source literal
is valid before the source type is selected.

1. Syntax validation checks radix, digits, separators, exponent, and suffix.
   Keep E0111 here, including the owned-AST boundary. Parse all six integer radix
   prefix spellings into an exact magnitude with existing `num-bigint` support.
2. Keep a pending numeric hole for an unsuffixed literal. An integer hole admits
   the integer family or a compatible float context; a decimal float hole admits
   f32/f64. A suffix selects and locks its format immediately.
3. Collect the ordinary expected-type constraints at initialization, parameter
   reception, return, branch, operator, and fresh aggregate construction sites.
   Apply existing generic inference rules; do not invent an enclosing binder or
   infer a type from an unrelated invocation at the same span.
4. Resolve a pending hole when its receiving context is known. At an ordinary
   defaulting boundary with no constraint, choose target `int` or f64 as specified.
   Unresolved generic evidence that cannot establish a complete choice stays NI.
5. Check the exact signed integer against the chosen integer interval, or round
   the exact integer/decimal text directly to the chosen float format. A bigint
   selection has no fixed integer range. Commit the selected type and value.
6. Remove pending-literal authority when a value is stored, returned as a typed
   result, or otherwise crosses a typed value boundary. Later reads may carry a
   constant value fact, but cannot reopen its type choice.

For example, `let x:f32=1` may select f32, but both `let x:f32=1int` and
`let n=1; let x:f32=n` remain E0301. A fresh tuple can receive per-element numeric
context; reading a previously stored tuple cannot retype its elements. Likewise,
`meta let N=1` commits an int, while `meta let N:f32=1` commits a float before
evaluation and reification.

Context travels along actual result/type dependencies, not every parent in an
explanation graph. Conditions, shift counts, bounds, and unrelated arguments do
not inherit the result's float type. Operations execute in their selected operand
types: exact-literal representation does not authorize folding an entire integer
arithmetic expression and rounding only its final result.

## Proposed frontend representation

Keep the implementation in a compiler-local `numeric_literals` module. The
compiler already depends on `num-bigint` and `num-traits`; no new crate,
dependency direction, runtime dictionary, or native ABI is needed.

The proposed data contract is:

- `ExactLiteral`: integer magnitude (`BigUint`) or validated decimal float text,
  plus written suffix and sign information. Preserve an immediately applied
  negative sign even for zero. Source spelling and span remain diagnostic data.
- `NumericUseId`: one semantic literal-evaluation occurrence. It is distinct
  from a syntax location and is linked to the producing CauseId and full
  `InvocationContext`. It is not the future repository-wide AST NodeId.
- `NumericHoleId` and a pending numeric type: an unresolved literal is not a
  solved `Ty::Int("int")`. Numeric constraints refer to its permitted domain and
  exact source value. Non-numeric operations cannot treat this placeholder as
  ordinary int evidence.
- `LiteralSelection`: use ID, selected source type, target layout where relevant,
  exact integer or final float bits, sign application, and proof cause. It records
  the committed representation rather than requesting another interpretation.

The exact names are proposed interfaces, not existing public APIs. A checked
integer value may still expose the current small `Constant::Integer(i128)` and
`StaticCoordinate::Index` facts when representable and of the correct selected
sort. Failure to fit those optional optimization facts is not a literal-range
error and must not substitute an arbitrary value, including zero.

Each literal fact follows the existing named invocation, closure invocation, and
DefaultUse partitions. A default is evaluated before the named body enters, so
its selection belongs to the precise DefaultUse view, not a fabricated body
invocation. Its callee static witnesses must already agree with the eventual
completed application certificate. Declaration probes remain separate from
actual evaluations. An early default exit cannot acquire a selection from a
successful sibling application.

The specialization planner projects these selections alongside contextual types,
handlers, and budget proofs. Equal native instances must agree on selected format
and encoded value at each emitted literal site. Their dynamic CauseIds or use IDs
need not be equal. An inconsistent or missing selection remains NI. A global
`contextual_types[span]` entry must never fill that hole. Existing typed ConstGraph
nodes and previously evaluated static values are already selected; they do not
become pending literals again.

### Late context and frozen invocation identity

A later return or aggregate context can affect more than a literal's encoding.
If it changes an argument's inferred type, it may also change a generic binder,
an effect instance and operation ID, a handler selection, or a default's static
environment. Updating only `LiteralSelection`, `Value.ty`, or the final return
type is therefore forbidden once that invocation's static witnesses are frozen.

The initial implementation must solve these constraints before committing the
application's static witnesses and checking its body. Expected types already
known from a function return, parameter, or fresh aggregate must be delivered to
that solve even if the current traversal would otherwise discover them later.
If a genuinely later constraint requires a different binder selection, either
revalidate the entire application/instance from its original pre-application
proof state, or report NI. The first implementation should retain NI until that
complete replay exists; walking Cause parents and changing their types is not a
substitute.

For example, with these declarations:

```ril
fn identity<T>(value:T)->T{value}
eff Read<T>{get()->T}
fn read<T>(witness:T)->T @Read<T>{Read<T>::get()}
```

| Use | Required selection and boundary |
| --- | --- |
| `let x:f32=identity<f32>(16777217)` | The explicit binder is f32 before entry; select and round its literal accordingly. |
| `fn answer()->f32{identity(16777217)}` | Infer T=f32 from the declared return constraint before freezing the call, or fully revalidate it. A completed T=int invocation cannot simply acquire a float result. |
| Under `with Read<f32>::get()->resume 7.0f32`, `let values:[]f32=[read(16777217)]` | The fresh aggregate context must select T=f32 and the `Read<f32>` operation before the instance certificate is committed. If that cannot be established, retain NI. |
| `let x:f32=identity<int>(1)` | E0301: an explicitly selected int binder cannot be changed to satisfy the destination. |
| Under a `Read<int>` handler, `let stored=read<int>(1); let x:f32=stored` | E0301: the first call and stored result are already typed int. A float destination cannot retarget the operation or the stored value. |

For the aggregate positive, a previously recorded `Read<int>` operation is not
interchangeable with `Read<f32>`, even if both handlers happen to be installed.
The actual parameter type, generic/effect identity, operation ID, handler recipe,
and returned value must all come from one consistently checked instance. The
same rule applies to a default-created callable and its retained recipe.

A future complete replay must replace or explicitly supersede the old witness
bundle atomically. Recheck arguments/defaults and body, permissions and loans,
copy and Result duties, selected handlers and answer transport, return types,
cleanup, finite/budget coverage, and every affected transitive call. Preserve
the real application/default identity and source evaluation order; do not count
one argument or default as two source executions. Old Completed records cannot
remain available as authority for the newly selected instance. If any affected
domain cannot be reconstructed, no partial replacement certificate is issued.

## Exact integer-to-float rounding

Use a small pure integer algorithm that produces the destination IEEE bit string.
This is the proposed production path for integer literals, including hexadecimal,
octal, and binary integers of arbitrary magnitude. Do not use `as f64 as f32`,
`to_f64().map(|x| x as f32)`, or an intermediate parsed f64.

Let `n` be the exact nonnegative magnitude. For f32 use precision `p=24`, maximum
unbiased exponent `127`, and bias `127`; for f64 use `p=53`, exponent `1023`, and
bias `1023`.

1. If `n=0`, return zero with the selected sign. Otherwise let `L=bit_length(n)`
   and `e=L-1`. Nonzero integers are at least one, so this conversion cannot
   produce a subnormal; decimal floating literals still need their existing
   direct-format parser and subnormal handling.
2. If `L<=p`, left-shift `n` by `p-L` to obtain the exact normalized significand
   `q`. Otherwise let `s=L-p`, `q=n>>s`, and `r=n-(q<<s)`.
3. For the latter case compare `r` with `2^(s-1)`. Increment `q` precisely when
   the remainder exceeds half, or equals half and `q` is odd. This is nearest,
   ties-to-even with the exact discarded bits. No float operation has occurred.
4. If the increment produces `2^p`, shift `q` right once and increment `e`.
   Encode sign, biased exponent, and `q-2^(p-1)`. An exponent above the format's
   maximum rounds to the signed infinity required by literal IEEE behavior.
   A source magnitude already beyond that exponent can take this overflow result
   without constructing an enormous remainder mask.

The remainder partitions the exact value between adjacent representable floats;
its comparison with half and the retained least-significant bit completely
determine the result. Sign is applied after magnitude rounding. This also makes
negative halfway cases symmetric. A zero sign bit must not be reconstructed from
`BigInt::sign()`, which cannot distinguish the source `-0` from `0`.

Two fixed counterexamples make a double-rounding implementation fail:

| Exact integer | Direct f32 bits | Incorrect f64-then-f32 bits |
| --- | --- | --- |
| `18014399583223809`, or `0X40000040000001` (2^54 + 2^30 + 1) | `0x5a800001` | `0x5a800000` |
| `170141193601674033557522515689509748737`, or `0X80000080000000000000000000000001` (2^127 + 2^103 + 1) | `0x7f000001` | `0x7f000000` |

The second value exceeds signed i128 but remains a finite f32 after rounding.
Its f64 intermediate loses the `+1`, lands exactly on the f32 midpoint, and rounds
the wrong way. Equivalent decimal, octal, binary, and hexadecimal spellings must
produce identical bits. Test the values immediately below, at, and above both
even and odd midpoint cases, including negative values.

Local dependency review supports this choice: installed `num-bigint 0.4.8`
(`src/biguint/convert.rs`, `high_bits_to_u64` and `ToPrimitive::to_f32`) retains
discarded information using round-to-odd and casts directly to f32, not through
f64. The signed implementation in `src/bigint/convert.rs` applies the sign after
magnitude conversion. That implementation is a useful independent comparison,
not an assumed permanent API proof for Ril's selection contract. The proposed
quotient/remainder implementation keeps Ril's rounding decision explicit and
independent of host word size or a dependency's future conversion internals.

Existing decimal literal parsing already calls Rust `parse::<f32>()` directly
for f32 and widens the resulting f32 exactly for storage; static evaluation does
the same. Preserve that direct-format route when selecting decimal literals.
The local toolchain has no installed Rust library source, so this audit does not
claim an independent review of Rust's decimal parser. Existing halfway decimal
regressions and differential bit tests remain required.

`Runtime::numeric_convert` uses exact integer-to-decimal text followed by direct
format parsing, and has its own `NumError::OutOfRange` policy. Literal selection
must not reuse that Result-producing runtime API or import its overflow policy.
This work adds no runtime conversion call, Result obligation, or budget event.

## Ordinary, static, and Core integration

| Area | Required change |
| --- | --- |
| Ordinary literal creation | Keep exact magnitude and a pending type instead of immediately reporting int/i128 range failure. A written suffix still selects and validates immediately. |
| Type constraints | Resolve numeric holes through actual receiving contexts, including fresh aggregates and branches; reject incompatible suffixes and committed values. Preserve type-alternative boundaries. |
| Generic calls and defaults | Reuse actual static binder witnesses and DefaultUse contexts. Publish a concrete literal selection only after its own constraints are solved; do not consult another instance's span map. |
| Patterns and static coordinates | Use the corresponding selected subject/integer context; a fixed array length is still nonnegative target int, with the existing wrong-sort/negative/range diagnostics. |
| Static typing | Replace its early i128-based integer validation and `IntegerConstant(i128)` assumptions for pending literals with the same exact-value/selection contract. Universal checks still precede requested evaluation. |
| Static evaluation | Evaluate from the solved selection. Helpers, branches, and arithmetic operate on selected values; never default and execute an int operation and then reinterpret its result as float. |
| Static reification and ConstGraph | Emit explicit int/fixed-width/float forms or typed pool literals from selected values. Preserve scalar sorts, aliases, field qualifications, float bits and negative zero. |
| Core lowering | Consume `LiteralSelection` to emit Integer, BigInteger, or Float. Fixed integers fit i128 only after their source range check; bigint uses the existing decimal/string representation. For f32, widening `f32::from_bits(bits)` to the existing f64 carrier is exact. |
| Unary lowering | Consume the recorded immediate sign exactly once, including `-0`. A second negation of an already evaluated fixed-width minimum remains a runtime panic. |
| Native backend | Use the existing typed literal representation and constructors; no ABI change, runtime type dictionary, or additional source-level call. |

Do not insert host conversions during type compatibility checking. Selection is
performed once and recorded. Scalar parsing/resource limits remain explicit
implementation limits: exhausting them is not proof of E0326.

### Implementation resources are not the static language budget

SPEC's Static Evaluation budget charges one unit for each meta/type function
entry, static callback entry, and loop iteration. A count of AST visits, input
digits, BigUint limbs, or rounding work is not one of those language events.
New exact parsing limits must therefore use separate implementation-resource
accounting and report an explicit implementation limitation if reached. They
must not masquerade as a source range failure or exhaustion of the language's
event allowance.

The v17 static evaluator charged expression visits and bigint spelling bytes to
the same allowance. The later static-budget work now separates those operations
from language events and exposes a positive per-root configuration; its targeted
quota checks and remaining integration limits are recorded in
[STATIC_EVALUATION.md](STATIC_EVALUATION.md). Exact literal parsing and selection
must use only implementation-resource accounting. Preserving the old combined
totals would not establish the required event semantics. Unproved paths stay
incomplete rather than acquiring a budget or range proof from parsing work.

Runtime `Div::budget` is also a distinct event system. Its exact-quota tests must
show that literal selection adds no function entry, callback, or loop event and
does not hide an existing one. The static-budget suite independently checks
meta/type calls, callbacks and supported iteration events; numeric integration
must preserve those quotas independently of spelling length and host parsing.

## Required validation before opening the paths

- Ordinary/core: all recorded false rejections above, signed and unsigned
  boundaries on pointer32/pointer64, direct return/argument/ascription contexts,
  immediate minus, negative zero, and default int overflow with no context.
  Check the emitted literal kind, width, value, and float bits, not just acceptance.
- Rounding: both integer counterexamples, every radix/case, ties on both parities,
  exponent carries, f32/f64 maximum-finite overflow thresholds, and negative
  counterparts. Compare a reference implementation based on neighboring exact
  powers of two; a second copy of the production formula is not an oracle.
- No promotion: explicit `int`, `u64`, `bigint`, or f64 suffixes in incompatible
  float contexts; stored scalars and stored aggregate fields cannot be reselected.
  Wrong operator families, shift counts, and incompatible numeric operands keep
  their existing diagnostics.
- Static: mirror ordinary cases through meta bindings/functions, local meta
  tuples/arrays, typed records, type/value argument canonicalization, and reified
  literals. Assert equivalent bits in static formatting, ConstGraph, Core, and
  native execution. Preserve distinct float zero signs in static type identity.
- Aggregates/control: fresh tuple, array, record, Optional/Result payloads and
  conditional results with per-leaf contexts; independently typed conditions and
  bounds; expected types arriving after construction; stored-container negatives.
- Generic/defaults: two closed instances and repeated same-key calls, explicit
  versus omitted slots, defaults with f32/u64/bigint literal contexts, later
  default/helper calls, and default-created closures retaining the right recipe.
  Missing witnesses, unclosed binders, and early-default exits retain NI. No
  blanket change to capability, finite, borrow, copy, or Result obligations.
- Late selection: the identity/read-effect examples above through return and
  fresh aggregate contexts. Assert matching binder keys, operation IDs, handler
  selections and literal bits. Explicit int binders and stored results remain
  negative cases; a missing complete revalidation path must produce NI rather
  than mutate a previously Completed certificate.
- Budget/native: zero allowance skips runtime action evaluation, exact entry
  quotas remain unchanged, helpers still consume their entries, defaults still
  execute before the callee body-entry charge, and normal/metered literals have
  identical values. Run the existing budget Result exit tests too.
- Authority: owned-AST ambiguity remains guarded; repeated actual evaluations
  at one legitimate source site receive separate numeric use records. Contradictory
  actual selections cannot be combined into one unspecialized native literal.

## Implementation order and review boundary

First add the exact parsing/rounding module and bit-level oracle tests while the
affected acceptance gates remain closed. Then add pending/selected semantic
facts and context-owned snapshots, route static typing/evaluation through the
same contract, and teach Core/negative/aggregate lowering to consume the solved
facts. Open a source path only after its complete chain is present. In particular,
do not ship a temporary `Int -> Float` compatibility relaxation with the old
integer-only Core branch or eager default-int range check.

The first implementation should cover the demonstrated source forms and their
shared paths together. Generic or dynamic cases without complete evidence stay
explicitly NI. Whole-project formatting, both-host tests and Clippy, and a new
frozen corpus run are subsequent integration evidence; the v17 snapshot must not
be modified to manufacture support for this later work.

## Ordinary implementation checkpoint

The pure exact parser and integer-to-IEEE selector are implemented with independent
neighbor-distance oracles. Known receiving contexts for ordinary bindings,
declared returns, fresh aggregates, named parameters and named defaults select
the exact literal before its range check. Immediate negation is part of that
selection. Core consumes the context-owned `NumericSelection` encoding directly;
no runtime conversion or new ABI is involved.

Named applications resolve parameter/return templates in the callee's canonical
binder environment before written arguments are evaluated. A known numeric
result context, explicit suffix or already committed numeric binding can constrain
the same binder. Argument expressions still run once in written order. A prepared
record keyed by the actual `CopyCallEventId` must match the independently inferred
body instance before its static witnesses are frozen. This covers nested
`identity` calls when that prior context exists, concrete `f32` arithmetic
parameters, and separate `Read<f32>` / `Read<int>` operation identities. Numeric
metadata does not replace permission, effect, Result or default-use checks.

For a direct unresolved scalar binder, pure literal/negation/arithmetic arguments
now produce typed pending terms. After later arguments have been evaluated once,
their actual types constrain the same canonical parameter templates. Before
defaults or body entry, the solver selects leaf encodings and updates scalar
expression facts by `NumericHoleId`; it preserves the source operator tree.
The current deferred operator set is `+`, `-`, `*`, `/` and `%`. A selected
integer division or overflow still faults before later runtime argument effects;
selecting the same tree as floating-point can instead produce infinity. Invalid
fixed-width arithmetic results are not published as constant facts. Pending and
equivalent explicitly typed trees have matching budget cutoffs.

Known rigid operator operands also constrain their partner before its evaluation.
A pure numeric tree paired with a dynamic call or projection can use the same
pending mechanism. Remaining complex producers cannot use the old contextual
cache to relabel an integer as a float: without an exact producer certificate
that crossing is explicitly unsupported. Committed static float markers keep
their original width even inside pending terms.

Effectful blocks, unsolved nested calls and branch joins without prior context
are not reconstructed or replayed as numeric terms. Their remaining unsupported
or legacy-rejection paths are not claimed as full bidirectional support.
Expected-only generic binders absent from input templates remain explicitly
unsupported. Row/static-key projections retain their full ordinary inference
instead of being guessed as direct numeric templates. Pending holes and
non-frozen prepared records cannot cross the verified boundary.

## Static implementation checkpoint

Static evaluation now uses that same exact kernel before evaluating literals in
known bindings, selected parameters/defaults, returns and fresh aggregate leaves.
Rigid typed peers constrain arithmetic literals, while stored values and suffixes
remain committed. Actual applications preserve written argument order; unresolved
generic or late context preparation remains NI. No completed call is replayed or
retargeted to a new binder. Annotation evaluation owns or inherits its specified
root, and parsing charges implementation work rather than language entry events.

ConstGraph and ordinary reification retain selected widths and float values,
including negative zero and non-finite results. A strict private width/IEEE-bit
carrier makes normalized type/effect/foreign arguments portable independently of
constant-pool insertion order. It is rejected at public AST boundaries and never
opens a new ordinary numeric hole. Its replacement with a typed normalized node
is recorded in `REFACTORING.md`.

Thirteen source/Core groups and five CLI groups pass on Windows and Linux;
four CLI sources execute natively, and the fifth group checks forbidden
reselection. Details and evidence paths are in
[STATIC_EVALUATION.md](STATIC_EVALUATION.md#contextual-static-numeric-selection).
