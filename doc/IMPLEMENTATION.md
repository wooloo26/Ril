# Implementation evidence

This file records partial implementation evidence. It is not a declaration of
complete SPEC or STD conformance.

## Executed corpus snapshots

| Snapshot | Host | Selected | Passed | Failed | Unimplemented | Other OS | Harness errors | Native builds |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| v3 | Windows MSVC | 1,067 | 852 | 190 | 23 | 2 | 0 | 225 |
| Linux v1 | Linux GNU in WSL | 1,067 | 852 | 190 | 23 | 2 | 0 | 225 |
| v4 | Windows MSVC | 1,067 | 894 | 148 | 23 | 2 | 0 | 251 |
| Linux v2 | Linux GNU in WSL | 1,067 | 899 | 147 | 19 | 2 | 0 | 252 |
| v5 | Windows MSVC | 1,067 | 912 | 125 | 28 | 2 | 0 | 260 |
| v6 | Windows MSVC | 1,067 | 938 | 101 | 26 | 2 | 0 | 275 |
| v7 | Windows MSVC | 1,067 | 958 | 74 | 33 | 2 | 0 | 287 |
| Linux v3 | Linux GNU in WSL | 1,067 | 958 | 74 | 33 | 2 | 0 | 287 |
| v8 | Windows MSVC | 1,067 | 1,001 | 42 | 22 | 2 | 0 | 317 |
| Linux v4 | Linux GNU in WSL | 1,067 | 1,001 | 42 | 22 | 2 | 0 | 317 |
| v9 | Windows MSVC | 1,067 | 1,012 | 36 | 17 | 2 | 0 | 324 |
| Linux v5 | Linux GNU in WSL | 1,067 | 1,012 | 36 | 17 | 2 | 0 | 324 |
| v10 | Windows MSVC | 1,067 | 1,020 | 30 | 15 | 2 | 0 | 328 |
| Linux v6 | Linux GNU in WSL | 1,067 | 1,020 | 30 | 15 | 2 | 0 | 328 |
| v11 | Windows MSVC | 1,067 | 1,041 | 10 | 14 | 2 | 0 | 337 |
| Linux v7 | Linux GNU in WSL | 1,067 | 1,041 | 10 | 14 | 2 | 0 | 337 |
| v12 | Windows MSVC | 1,067 | 1,062 | 0 | 3 | 2 | 0 | 351 |
| Linux v8 | Linux GNU in WSL | 1,067 | 1,062 | 0 | 3 | 2 | 0 | 351 |
| v13 | Windows MSVC | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| Linux v9 | Linux GNU in WSL | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| v14 | Windows MSVC | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| Linux v10 | Linux GNU in WSL | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| v15 | Windows MSVC | 1,067 | 1,064 | 0 | 1 | 2 | 0 | 353 |
| Linux v11 (v15 binary) | Linux GNU in WSL | 1,067 | 1,064 | 0 | 1 | 2 | 0 | 353 |
| v16 | Windows MSVC | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| Linux v12 (v16 binary) | Linux GNU in WSL | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| v17 | Windows MSVC | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| Linux v13 (v17 binary) | Linux GNU in WSL | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| v18 | Windows MSVC | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |
| Linux v14 (v18 binary) | Linux GNU in WSL | 1,067 | 1,065 | 0 | 0 | 2 | 0 | 354 |

Snapshots use the real CLI subprocess adapter, actual Ril sources, independent
case directories, timeouts, process cleanup, and native linking/execution. The
v4 through v18 compiler and runtime were copied together before each run so later builds
could not change that run's result. Machine-readable reports are development
artifacts under `target/full-report-v18.json` and
`target/linux-full-report-v14.json`; they are not checked into source control.
Failures, unavailable environments, and unimplemented stages are never passes.

The v18 pair is a frozen-binary corpus checkpoint, not a new full-workspace or
complete-implementation certificate. Each host actually passes 1,065 applicable
cases, including 354 native builds/executions; the passed-ID union is all 1,067
original cases. Each report retains its two other-OS cases as incomplete and the
runner exits nonzero for that explicit exclusion. There are no failures, NI
cases or harness errors. These binaries include the bounded CPU task scheduler,
pending timer/channel/join/scope/host/foreign operations, transactional Heap CPS
and exact budget coverage, finite recursive capability scans, ordinary non-tail
reference answers and scope-exit writer evidence, static immutable loops and the
large-capture implementation-work admission fix. Subsequent full source-type
witness, lexical static publication and channel message-ledger changes are not
included; those have separate component gates and remain under integration.
Windows hashes are in `target/snapshots/v18/manifest.json`; Linux copies and
hashes are in `/home/ayan/.cache/ril-native-snapshot-v18/SHA256SUMS`.

Both v15 runs expose one lowering regression: the process spawn/wait/terminate
case reaches `derive` inside CPS, which lacked a lowering branch. It is an
unimplemented result, not a pass or a runtime success. The other 1,064 applicable
cases pass on each host. The frozen binaries and reports remain unchanged while
the missing CPS path receives implementation and targeted native tests.

The v4 snapshot has one erroneous static acceptance: effectful top-level clock
initialization. The unified initializer obligation check was repaired after that
snapshot and has a source regression. Linux v2 verifies that negative case and
contains no accepted static negative case. Windows v5 also contains no accepted
static negative case. Windows v6 has no accepted static negative case or native
runtime expectation failure. An increase in unimplemented results may reflect a newly
enforced proof boundary; it does not count as additional conformance.
Snapshots through v6 had no native runtime expectation failure. Windows v7 and
Linux v3 expose one: optional safe indexing evaluated the index of a None
receiver. Managed and CPS branches were repaired after freezing these reports;
the original corpus case and a source regression with an effectful index now
execute successfully. The frozen report remains unchanged as evidence.
Windows v8 and Linux v4 contain no accepted static negative case and no native
runtime expectation failure. They expose one static regression from the stronger
whole-graph immutable-publication check: the lawful fresh array in Order's
stable-ties case is rejected. This is recorded as a failure, not a pass; its
qualification path was repaired after freezing the reports, with source
regressions and an actual Windows native regression. Old live children remain
ineligible. The frozen failures remain unchanged.
Windows v9 and Linux v5 have no accepted static negative case, no native runtime
expectation failure, and no regression from a passing v8 case. All five original
Iter cases execute successfully. The remaining failures and unsupported stages
still prevent complete conformance and the implementation milestone commit.

Windows v10 and Linux v6 also have no accepted static negative, native runtime
expectation failure or regression from a passing v9 case. Eight more original
cases pass, including the local-effect boundary pair, integer arithmetic and
negative shifts, fresh factory results and file open modes. Full workspace tests,
all-target Clippy and formatting checks pass on both hosts. These checks still do
not establish complete conformance: 30 failing cases and 15 unsupported cases
remain per host, in addition to two explicitly other-platform native cases.

Windows v11 and Linux v7 add 21 passing original cases, including the complete
original concurrency/channel groups and row preservation. Both reports contain
no accepted static negative, native runtime expectation failure or regression
from a passing v10 case. Full workspace tests, all-target Clippy, format and diff
checks pass. Ten failing and fourteen unsupported original cases remain on each
host, as well as broader implementation gaps listed below; this is still not the
complete-implementation milestone or its commit.

Windows v12 and Linux v8 add another 21 passing original cases, with no failing
case or regression from a passing v11 case. Both have 351 actual native builds.
Three cases remain unsupported: the two documentation loop examples and buffered
IO. The two other-platform cases on each host remain explicit exclusions, not
passes. These snapshots include native Parallel, generic effect instances,
parameterized and retained tail-resume handlers, and cancellable standard streams.
Follow-up tests found interactions beyond the original corpus (retained handlers
inside budgets and nested named callable creation); their fixes were made after
freezing v12. The broader gaps below still prevent the implementation milestone.

Windows v13 and Linux v9 pass all 1,065 applicable original cases on each host;
their matrix union covers all 1,067 cases. Each performs 354 native builds, with
no failing, unimplemented or harness-error case. Full reports retain the explicit
two other-platform cases as incomplete; CI's `--applicable-only` selection omits
them rather than counting them as passes. This original-corpus milestone is not
complete implementation: the full workspace suite exposes an existing source
regression, `native_scope_body_abort_preserves_the_outer_answer_and_cleanup_order`,
which the frozen v13 compiler rejects with E0301. Its immediate scope action must
preserve the caller's abort boundary. The regression and the broader remaining
language/runtime paths must be resolved before the implementation commit.

Post-v13 source regressions now establish immediate scope-body abort and retained
fixed-copy answer behavior on both hosts. These repairs do not rewrite the frozen
v13 evidence. Subsequent full-workspace runs exposed another ordinary-loop sum
carrier regression, repaired together with the additional Result-exit and finite
copy-class paths. Partial observed field sets never establish object disjointness;
the earlier inference was removed from both copy paths and has alias regressions.

The external binding path now carries stable module/declaration identities through
Core, native CPS adapters, CLI manifests and isolated provider processes. Typed
graph encoding/decoding preserves aliases and cycles, fixed array lengths,
nominal identities, and ordinary opaque representations. Temporary callback
values and continuations remain rooted on their owning Ril task. Provider waits,
termination, reaping and thread joins occur outside the heap gate. Replay,
unknown-token and malformed callback requests have source-native regressions.
Foreign calls now preserve the zero-invocation path and a callback's definite
nonlocal abort as separate heap/Result exits. Internal mixed normal/abort callback
paths and exits with unresolved cleanup still require further source proofs.
Concrete generic descriptors now carry static arguments, including phantom
arguments, and the concrete schema arena. Source-native tests on both hosts
establish explicit type/scalar instances, fixed-array type arguments, aliases,
repeated references and equivalent computed static arguments. Generic defaults,
compound static arguments, and effect/capability argument substitution remain
in progress; this subset does not establish complete generic source support.

After the foreign runtime bridge and static-argument validation changes, runtime
library tests pass on Windows (148 tests) and Linux (149 tests), including six
typed graph/argument codec tests. The one Windows and two Linux ignored tests are
subprocess fixtures exercised by their parent tests, not conformance cases.
Windows runtime all-target Clippy also passes. These are component results, not
a new frozen corpus snapshot or full implementation acceptance.

Two further codec regressions pass on both hosts: 20,000 nested opaque envelopes
resolve to one shared managed representation without recursion or quadratic
re-traversal, and a nonproductive alias cycle in a later root is rejected before
any managed allocation. All eight codec tests and runtime all-target Clippy pass
on both hosts after these changes. The external source-native suite subsequently
passes all seven groups on both hosts, including the caller's live-handler abort.
Generic instances and later local functions share the compiler's definition
identity allocation; a mixed local-function/lambda regression guards collisions.

The complete workspace suite then passes on Windows (913 tests, one subprocess
fixture ignored by the direct harness) and Linux (915 tests, two such fixtures).
Both runs include the seven external groups and four ordinary-loop/copy native
groups. Two later source regressions expose a nested cleanup double-fault bug on
both hosts: outer cleanup either replaced the inner causes or continued callbacks
after fatal failure. The cleanup driver now propagates an already fatal outcome
without composing it again. Rebuilt runtime libraries pass both new cases plus
21 existing concurrency/effect/retained-handler native tests on each host. These
additional cases were not part of the preceding workspace totals.

Windows v14 and Linux v10 again pass all 1,065 applicable original cases each,
with 354 native builds per host and all 1,067 cases covered by the matrix union.
There is no accepted original negative case or regression from v13. These frozen
ABI 2 binaries include ordinary external bindings, concrete explicit external
generics, the definite callback-abort exit, finite ordinary copy classes, and the
nested double-fault repair. The subsequent mixed callback exits, nested row
transport, filesystem cancellation and ABI 3 cleanup work are not included in
this snapshot and require their own validation.

A subsequent capability audit reproduces an unsafe acceptance in frozen v14
outside the original corpus: `target/copy-summary-alias-probe.ril` is accepted
with no diagnostics (`target/copy-summary-v14-unsafe.json`). A formal collection
element can represent several objects, and distinct tuple members can also alias.
A member replacement must not discard the previous field of other possible
aliases or leave their field facts stale. This could otherwise manufacture a
false disjointness proof after cloning. Multiplicity and may-alias write updates
now reject that exact source with E0619 in the rebuilt CLI; the frozen acceptance
is preserved. Complete-Session regressions also cover tuple/map/nested aliases,
readonly paths, escaping scope authority and dropped Result producers. Original-corpus
success therefore does not establish the capability engine's soundness.

The ABI 3 logical cleanup driver runs callbacks in the existing trampoline.
Its task-owned exit frames trace pending values and resources, preserve fault
causes, and retain budget/cancellation masks across suspension. Activations
retain their actual handler extent: protected-body cleanup can still invoke its
handler, whereas an arm's cleanup uses the masked outer extent. Delimiters retire
after cleanup and after any deferred arms created during cleanup. Fault and
concurrent-scope recovery traverse that changing region rather than a snapshot
of its original deferred arms. Superseded exits transfer their pending primary
cause and retire their masks.

Component validation after this change passes 161 Windows and 164 Linux runtime
tests (one/two direct-harness subprocess fixtures ignored), plus Windows runtime
all-target Clippy. Source-native handler-extent cases cover repeated abort,
different handler owners, and an arm created during an existing panic. They
also exposed a separate frontend failure: a scope with a diverging body can
recover child cancellation as Err, but was typed Never, so subsequent operations
lacked lowering facts. The pre-fix failure log remains preserved. A conservative
cancellation certificate now retains every
same-task prefix after children exist, requires a stable external reference
graph, widens scalar facts and intersects caller-owned Result inspection.
The complete nine-case handler-extent native suite now passes on both hosts.
The existing-panic case also forces an observer cleanup to panic in a separate
run, positively proving that the outer cleanup ran and that both causes survive.
Broader mutation/resource cancellation exits still require precise certificates.

Static interpolation now executes the same pure scalar formatting rules as the
native runtime through `ril-text-format`. Syntax, ordinary typing and static
typing share its format grammar; width and precision bounds explicitly use the
selected pointer32/pointer64 Ril int layout. Static output-budget exhaustion is
NotImplemented rather than a malformed-format diagnostic. Component and source
tests cover integer bases/sign padding, shortest f32/f64 output, decimal rounding,
scientific carry, signed zero, Unicode scalar truncation and padding, and special
float space padding. The combined static/native source test passes on Windows
and Linux; runtime expressions are also checked for single evaluation in order.

The first complete nextest CI-profile run of this batch reports 1,023 passing,
13 failing and one skipped fixture on Windows, and 1,027 passing, 13 failing and
two skipped fixtures on Linux. Logs are `target/pre-v15-nextest-windows.log` and
`target/pre-v15-nextest-linux.log`. The failures expose a cancellation gate that
rejects wait-then-panic sentinels, native named-callable/iterator regressions,
and an incomplete ordinary-container copy witness. These are real regressions,
not unavailable environments. Their original assertions are retained while the
implementations are repaired. No v15 corpus snapshot or complete-implementation
milestone has been claimed from this run.

Those implementation regressions have been repaired. The subsequent complete
CI-profile runs pass 1,051 tests on Windows and 1,055 on Linux, with only the
one/two explicitly ignored subprocess fixtures. Both workspace all-target
Clippy runs, actual resolved-dependency checks, formatting and doc-test commands
complete successfully. The deterministic cancellation fixture now starts the
failing child only after the body and deferred-arm cleanup registrations exist;
it no longer relies on a sleep. Typed non-retaining builtin-adapter evidence
preserves receiver captures and resource permissions while proving that an
adapter does not retain an unrelated creation-site handler.

These component results precede the ABI 3 v15 corpus runs, whose binaries
were copied together with hash manifests. Those reports now record the one CPS
derive gap described above. Broader symbolic copy-template authorization beyond
the private direct-call path below, general cancellation exit transport, richer
retained answers and other gaps below remain separate implementation work.

The v16 engineering checkpoint passes complete CI-profile runs on both hosts:
1,164 Windows tests and 1,168 Linux tests, with only the one/two ignored
subprocess fixtures. Both actual workspace all-target builds, all-target Clippy
with warnings denied, formatting, resolved architecture checks and doc-test
commands also complete successfully. Logs are `target/pre-v16-*`; the doc-test
commands contain no doctests and are not additional semantic test passes.
Compiler/runtime/corpus-runner binaries were frozen together at
2026-10-13T23:01:49Z with SHA-256 manifests in `target/snapshots/v16` and the Linux
snapshot directory. The 1,067-case corpus runs use only those frozen binaries.
`target/full-report-v16.json` and `target/linux-full-report-v12.json` each record
1,065 passes, 354 successful native builds, and no failures, unimplemented cases
or harness errors. The two other-platform cases on each host are explicit
exclusions; the matrix union covers all 1,067 cases. In particular, the actual
process case that exposed the v15 CPS derive gap now executes successfully.
This does not establish complete language implementation; the broader gaps
below still require independent implementation and evidence.

A subsequent Result-exit audit reproduces an unsafe acceptance in frozen v16
outside the original corpus. `target/budget-result-exits-audit.ril` creates an
uninspected Err before a positive-quota budget. Its action first calls a helper,
then inspects the Result; the exhaustion handler simply returns unit. The
checker incorrectly supplies the completed action's inspection fact to the
earlier exhaustion path. The frozen CLI accepts it with no diagnostics, saved
in `target/budget-result-exits-v16.json`. The ordinary/recovery flow snapshots
and actual producer duties require independent exit analysis. The failure is
retained as a regression while that repair is implemented; corpus success does
not cover this additional safety case.
Native witnesses under `target/budget-exit-probe/` independently confirm the
control-flow difference: quota 1 returns unit before inspecting the Err; quota
100 reaches an assertion-failure sentinel after inspection. These executions
are evidence of the old acceptance defect, not passing language-conformance
cases.
The subsequent rebuilt Windows CLI rejects that exact frozen-audit source with
E0720 (`target/budget-result-exits-after.json`). Its seven-cause explanation
distinguishes the normal inspection from the exhausted path's pending duty.
An independent source oracle enumerates 32 combinations of limit and inspection
placement, checks every accepted program against finite concrete exits, and
requires entry-inspected and both-path-inspected positive controls to be accepted.
That oracle passes after the repair. Broader related regression runs remain
separate from this targeted evidence and the frozen v16 reports.

The v17 engineering checkpoint passes the complete workspace CI-profile suite:
1,247 Windows tests and 1,251 Linux tests, with only the one/two ignored
subprocess fixtures. Both workspace all-target builds, all-target Clippy with
warnings denied, formatting, resolved architecture checks and doc-test commands
pass. There are no doctests, so those commands add no semantic pass count.
Logs are `target/pre-v17-*`. Compiler, runtime and corpus runner were frozen
together at 2026-10-14T00:54:45Z, with hash manifests in `target/snapshots/v17`
and the matching Linux snapshot directory. Their full corpus reports,
`target/full-report-v17.json` and `target/linux-full-report-v13.json`, each record
1,065 passes and 354 actual native builds, with no failures, unimplemented cases
or harness errors. Each retains two other-platform exclusions, and the matrix
union again covers all 1,067 cases. Broader implementation and additional audits
remain; the complete-implementation milestone has not been claimed.

## Implemented paths

After v16, fixed-array length-changing operations receive E0301 instead of an
incomplete result, including aliases, helper arguments and cloned static data.
Element writes and fresh dynamic reverse/concat shells remain valid. Static
closed records also retain mutable-field type declarations independently of
their readonly constant handles, so later ordinary clones have the correct slot
modes. Source/Core checks and native clone observations exercise this extension;
construction/view conversions, nested Immut and nominal static values still need
complete type witnesses. See STATIC_CONSTANT_GRAPHS.md for the exact boundary.

The post-v15 constant arena now has real native graph evidence on both hosts:
nine source groups preserve shared children, distinct equal-content allocations,
later projections, new shells containing old children, Map/Option edges, fixed
arrays, scalar representations, normal/metered identity and worker roots. A pool
of 400 distinct empty arrays necessarily crosses the initial GC threshold before
user code, verifying roots between node construction and cell publication.
Frontend/Core tests also cover forged owned-AST references, module forwarding,
edited/fresh Sessions and solved collection-type constraints. Detailed scope and
remaining qualification limits are in STATIC_CONSTANT_GRAPHS.md.

This work exposed a lexical evaluation-family bug: a static local variable named
`child` was mistaken for an ordinary global function with that name. A separate
phase visitor now tracks parameters, sequential bindings, match arms and block
scopes, while retaining rejection of actual cross-family calls, defaults and
unused bodies. Source and native regressions cover the collision. An additional
owned-AST regression established that bypassing the lexer could forge a reserved
static declaration name and incorrectly obtain VerifiedProgram. The public AST
boundary now shares identifier spelling checks with the lexer and lexes raw
annotations before resolution. The original failure is preserved in
`target/static-phase-owned-collision-before.log`; the corrected phase suite passes.

An independent specialization audit also found an owned-AST wrong-code path:
two distinct handlers with the same diagnostic span and callable owner acquired
one lexical handler ID. The ordinary source executed successfully, but changing
only those spans still yielded a certificate and then an unhandled operation.
Verification and normal lowering now refuse ambiguous same-owner handler or
closure occurrences, while permitting equal spans under distinct callable
owners. Three source/owned-AST boundary tests verify this temporary conservative
gate. Typed AST node identities, rather than dynamic handler indices, are the
planned replacement during refactoring. The original evidence remains under
`target/specialization-audit/`.

A second owned-AST audit found a distinct wrong-code path: assigning a default
float literal the same diagnostic span as an earlier f32-context expression
changed the former's inferred type from f64 to f32. Normal native execution
returned unit; the colliding AST was still verified and then failed its numeric
format assertion. Evidence is `target/specialization-audit/numeric-span-evidence.log`.
The temporary syntax-identity gate now rejects this ambiguity across the whole
program, including cross-function and composite-expression collisions. Four
source/Core tests and an independent native audit verify normal f64 behavior
and pre-lowering rejection (`numeric-span-gated.log`). Evaluated static int
values are reified with their already selected int type, preventing shared
constant diagnostic spans from introducing new unsuffixed numeric holes.

- Recovering lexer/parser, source AST, module resolution, project Sessions,
  type checking, static evaluation, and private semantic verification boundary.
- Heap shapes, conditional BDD relations, permission roots, capture identities,
  recursive summaries, narrowing, Result inspection, and traceable causes.
- Verified HIR to structured Core, typed provenance, abstract pointer layouts,
  native Cranelift code, platform linking, and actual execution on both targets.
- Generation handles, nonmoving tracing collection, alias/cycle-preserving clone,
  precise continuation roots, selective CPS, affine tail resumption and checked
  copy-value non-tail resumption, logical
  scoped activation lifetime, nonlocal handler exits, explicit effect-abort,
  panic and double-fault causes.
- Numeric, strings, Unicode 17, bytes, binary encoding, digest, array/map/set,
  Option/Result combinators, time, random, native strings, lexical paths,
  environmental snapshots, file streams/filesystem operations, and testing with source
  contracts and native tests. Further library modules are under construction.
- Explicit-path process invocation, native argument preservation, separate input
  and capture workers, combined capture limits, termination/reaping, and cached
  child status. Duplex and cancellation worker tests run on both hosts; actual
  Ril child programs verify invocation and byte-exact output on both hosts.
- Structured Core stream-helper loops preserve real callbacks and suspension;
  read/write response validation, linear byte accumulation, constant-time byte
  suffixes, and checked partial/error/abort paths have source/native regressions.
- Native structured scopes, child tasks, joins and bounded channels use shared
  managed handles, explicit task ownership and cancellation. Scope bodies keep
  their caller's handlers; children start isolated handler contexts. Scope exit
  waits for children and closes its physical channels. Detached transfer uses
  new descriptors on reception/return so consumed aliases cannot revive.

## Required work still outstanding

- Complete the remaining generic/type-function, structural-bound, existential
  and static-expression paths. The exact numeric selection kernel and static
  immutable loops now have targeted two-platform evidence; their separate proof
  limits remain in NUMERIC_LITERAL_SELECTION.md, STATIC_EVALUATION.md and
  STATIC_RESULTS.md. In particular, a record constraint must support universal
  known-field projection and validate every actual application without treating
  an unknown row as a closed type.
- Finish the outcome-indexed channel Result evidence. It must independently
  cover send failure, received payloads, unread messages, helpers, nested and
  quantified payload families, and every normal exit. Complete source-type
  witnesses, lexical static publication, and fixed-storage generic IO receiver
  schemas have targeted two-platform gates; those component gates do not
  certify the remaining channel or structural-bound paths.
- Complete remaining retained resource/callable answer, recursive Result-family
  and higher-order specialization paths. Ordinary non-tail reference answers
  and scope-exit writer evidence have their own completed component gates in
  NON_TAIL_REFERENCE_ANSWERS.md; those do not certify the remaining categories.
- Complete platform cancellation coverage and broader multiworker
  cancellation/GC stress validation. Bounded CPU execution and separate pending
  host IO are implemented. Interruptible filesystem-open/read/write waits have
  real Windows/Linux regressions; host operations without an interruption
  mechanism retain documented limits.
- Full generic stream-position reservation tracking for independent custom read
  implementations. Selected callable identities and observed delegated file
  endpoints are tracked, but this does not yet classify every arbitrary helper.
- Full fresh/incremental equivalence, concrete-model/property coverage, and
  passing applicable corpus execution in both CI environments.

The source tests include newly discovered cases beyond the original corpus:
permission laundering through published wrappers, conditional clone aliases,
independent ambient roots, named capture environments, contradictory narrowing,
dynamic argument labels, propagation, and cleanup across native suspension.
The compiler uses explicit incomplete results when these proofs are unavailable.

The layout selected during semantic verification now accompanies the facts and
Core provenance. The default Core entry reads that layout, and the explicit
entry refuses a different layout. Native lowering refuses a known non-64-bit
layout; `pointer32` remains available for checking and Core inspection. The
before-fix layout regression is preserved in
`target/target-layout-boundary-before-windows-v1.log`. Both repaired boundary
tests passed on Windows in `target/target-layout-boundary-windows-v2.log`, using
the fresh first-integration test binary whose hash is recorded beside the log.
Both also passed on Linux in
`target/channel-ledger-production-targets-linux-v3.log`.

Three file corpus expressions were corrected from `metadata(path)?.size` to
`(metadata(path)?).size`. SPEC defines `?.` only for Optional receivers; a Result
must first be propagated and then projected. The case count and assertions are
unchanged. Snapshots through v5 predate this fixture correction.

Standard streams perform unbuffered byte IO, including zero-length access-mode
validation. Native tests on both hosts cover non-newline UTF-8, arbitrary output
bytes, wrong-mode empty transfers and closed-pipe errors. Linux pipe writes use a
temporary thread-local SIGPIPE mask, preserve any pre-existing pending signal,
and restore the caller's mask; no process-wide signal disposition is replaced.
Additional native tests now cancel blocked stdin, stdout, print and println on
both hosts, retaining pipe ends so EOF or a drain cannot fake cancellation.
Required cleanup still completes its host output. Linux tests also alias all
three standard descriptors to one file description and verify flags are restored
after cancellation. Unexpected Rust/internal host failures remain distinct from
cancellation even when both arrive together.

Non-tail resumption evidence records the actual protected-body answer, delayed
arm answer, continuation cause and owning handler in verified HIR and Core.
Source/native regressions cover scalar answers, repeated operation LIFO order,
and body cleanup before suffix before arm cleanup. Reference/owning answers and
unresolved outward requests remain explicit incomplete checks.

The opt-in shared-heap infrastructure publishes worker roots at each managed
access boundary and restores the gate after unexpected host unwinding. Tests
exercise four native threads with forced collection, cross-worker visibility,
shared cycles, native callback reentry and suspended continuations. These are
runtime infrastructure tests. Subsequent source task/channel integration and its
remaining cancellation limitations are recorded below.

Budget execution now uses explicit language-event charges and paired normal
and metered CPS callable entries over the same environment. Independent allowance
traces and native runtime tests cover zero/one/negative limits, outer ownership,
cleanup masks and 20,000 recursive entries through one trampoline. Internal
Core-to-object-to-native tests also cover nested recovery and cleanup double
faults. The actual source coverage registry is now connected to normal lowering,
with independent explicit-argument, action and recovery termination judgments
retained in Core. All 18 original totality cases pass through the real CLI in the
v8 pair. Additional source-native tests check precise loop and callback counts,
builtin callbacks without double charging, negative limits, nested boundaries and
20,000 recursive entries. Unknown callable coverage, outward state, foreign/I/O/
resource computation, and unproved retained handler environments remain gated.

Public semantic analysis now follows module resolution and static verification
before constructing VerifiedProgram, just like Session's source and owned-AST
paths. Static failures cannot bypass that boundary. Closed row substitution
preserves exact remaining fields, modes and lacks constraints; unknown nested
tails remain represented. Fresh outer storage cannot freeze an old live child.

After the v8 freeze, native host requests for standard streams, sleep, entropy,
process operations, file streams and implicit file/child cleanup separate host
work from the managed-heap gate. Sleep and child waits use wakeable cancellation
tokens; process run completes transfer cancellation and terminate/reap. Active
child-wait cancellation is tested on both hosts;
the owning authority remains available and cleanup still reaps with an already
cancelled token. Implicit file/child cleanup now performs host release outside
the gate. Other filesystem operations and cancellable standard-stream/file
transfers and source scheduler integration remain unfinished. These are
infrastructure tests, separate from source-task conformance. A shared-heap
double-fault regression also
checks that abandoned logical cleanup actions are removed from their stack.

Source and owned-AST verification now perform the same syntax role checks before
resolution. Sum facts retain exact per-tag payload witnesses, including origins
and permissions, across branch joins and Core lowering. They use one payload
owner rather than duplicate recursive trees; the expanding-instance regression
and a 96-level model exercise the finite representation. Source Iter cursor/
pull, actual custom steps, sticky EOF, abort without successor installation and
map/take/collect/filter/fold examples execute natively. Original Iter cases and
additional dynamic-state, 40-item tail, readonly accumulator and abort tests have
actual native coverage. Unknown repeated Result-family coverage remains gated.

Callable return contracts distinguish sequential ascriptions from alternative
branches and explicit raw paths. Immutable Arc DAGs preserve source sharing;
Core uses a graph arena with stable local references rather than recursive
copies. Both model substitution and Core projection keep a 64-level diamond at
129 nodes. Source regressions cover repeated opaque ascription, raw/sealed branch
isolation and nested generic returned callables.

After freezing v9, an additional Linux source-native FIFO test demonstrated a
SIGPIPE crash in File::write. File stream and whole-file writes now use the same
thread-local signal boundary as standard streams. The FIFO and standard-output
broken-pipe source-native regressions pass; no process-wide signal disposition
is replaced. This new case was not present in the frozen corpus reports.

After v9, all remaining filesystem requests (including open, whole-file IO,
directory operations and metadata) also perform host work outside the managed
heap gate. Requests own native paths and bytes, and replies install handles only
after returning to the heap. Tests collect the original managed inputs before
executing a prepared request, including transferring that request to another
thread. File stream transfers use separate host workers. Windows cancellation
requests synchronous IO cancellation until completion; Linux transfers use
temporary nonblocking flags under the file authority's mutex. Both platforms
verify that a blocked read returns cancellation, keeps the file authority usable,
and still permits implicit cleanup. Linux also verifies restoration of descriptor
flags. Standard-stream and filesystem-open cancellation remain unfinished.

The next source/frontend batch adds closed record-rest binding with one subject
evaluation and complete child permissions. Single rigid generic row tails now
carry symbolic graph edges, source identities, permissions and Result families
through spread, rest and nested generic calls. Nested record, tuple, array, map,
optional and witnessed Result containers retain the original member-family
edges, source identities and Result obligations. The proof checks every source
alternative and meets permissions along its actual reference path; field slot
mutability does not grant or remove child-reference authority. Missing payload
witnesses, truncated recursive formal shapes, multiple unknown tails and unknown
overrides/producers remain explicit unsupported proofs. Deep cloning an unknown
tail still requires complete resource, environment and Result multiplicity
evidence: a rigid binder or field-type schema is not copy eligibility. Closed
eligible instances use the ordinary graph-copy proof. Integer shifts accept independent integer
counts, keep the left operand's representation, and enforce the left width in
both native and static execution. Static pointer32/pointer64 tests distinguish
the abstract target from the host. Safe integer division/remainder have Optional
results, and conditional type mismatches retain their specific diagnostics.

First-class storage operations now instantiate checked signatures and preserve
receiver retention obligations. Local effect identity is lexical; residual
effects and reachable escaping callables are checked at the declaring boundary.
Result control transfers carry invocation- and exit-specific coverage evidence;
branch joins cannot borrow inspection from a different path, and loop-created
families that escape still require a multiplicity-aware proof. New negative
tests exercise early return, uninspected loop exits, later iterations at the same
callsite and different invocations.

Result-bearing field replacement is admitted only when every possibly affected
old producer and the replacement's producers are already inspected, and the
affected objects have singleton evidence. A possible surviving reference is not
a proof that an uninspected old producer was retained or returned. A concrete
caller that overwrites and loses that producer reports `E0720`; symbolic pending
producer transfer and summarized member families still report NotImplemented.
Exact member reconstruction for later copies after such storage changes remains
a separate proof. Tests for those conservative gates are distinct from language
negative tests that require the specified diagnostic.

Ordinary-data loop graphs use a finite recent/older representation. Deep copies
intern canonical classes by the original allocation base, selected shape and
readonly qualification; copy-of-copy depth does not create new classes. Each
copy batch snapshots source edges and relations before recency updates, then
joins merged fields and weakens relation evidence. A class with multiple possible
objects has no singleton equality certificate. Internal aliases, cycles and
explicit immutable descendants survive copying. Different observed field sets
never prove disjointness. Independent concrete-graph oracles, source permission
counterexamples and native cyclic-copy tests calibrate these rules. Resources,
summarized Result families, callable environments and unresolved rows retain
their separate transfer gates.

Copy boundaries now preserve typed owner and activation identities, conditional
source and output graph snapshots, multiplicity, permissions, constituent
qualification and pending requirements in Core provenance. A missing payload is
a type-only potential member with no invented origin or immutable permission.
Callable types alone do not prove an environment-free payload; a formal
`Result<fn, E>` therefore retains its unproved environment condition. Conversely,
an actual `None` contains no resource to copy even when its declared payload
type is a file handle. Actual resources and retained callable environments still
report `E0530`. Closed ordinary recursive shapes retain their established graph
copy proof without adding alias or singleton facts from type structure.
Opaque Deque/Heap constructors also retain an explicit complete-member witness
inside the semantic graph; a type name or a partial observed element set cannot
create it. Copying checks every actual element and Heap comparator separately.
The witness follows existing graph transport and is invalidated by unknown
writes; one later insertion cannot restore knowledge of earlier members.
Resource/environment and summarized nonordinary transfer restrictions remain.

Conditional copy identities propagate through values, nested sums, fields,
joins, projections, invocation summaries and further copies. They cannot grant
freshness, writable reception, immutable publication or graph-copy eligibility.
Private named direct-call `T`/row forwarding templates now retain these conditions
until each actual invocation supplies a complete graph witness. The closure
certificate covers every instance and the acyclic template dependency graph;
one successful substitution cannot discharge another invocation. Declaration
boundaries remain conditional with no established output. Actual invocation
rechecks permission reception, Result duties and graph transfer, including
nested carriers and further copies. A generic template can now select either
an ordinary-copy witness or a separate Sender-clone witness at an actual use.
The latter never becomes ordinary deep-copy isolation or a freshness proof for
the shared channel. Conditional declaration boundaries still have no fabricated
ordinary output.

Sender evidence freezes the exact application/callee event, intrinsic clone
selection, existing CloneSender boundary, source/output descriptor graphs,
scope/task/channel metadata and required Fiber effect. Validation recomputes
these links and rejects evidence from another invocation; source spans and an
equally shaped value are insufficient. The contract permits legitimate ancestor
Sender borrowing. Immutable clone, wrapped resource graphs and nonclonable
resources cannot use this branch. The 28 component checks and actual Windows
and Linux Sender native groups pass; the latter also reject four invalid source
programs with their required diagnostics.

Resource allocation uses finite static named/closure call contexts, including
operation identity, rather than dynamic invocation IDs. Repeated targets mark
recursive contexts; the context arena has an explicit 4,096-entry allowance.
Recency preserves all descriptor metadata alternatives and task/message duties.
Many-instance or unresolved scope/channel/task identity never supplies individual
resource authority. Scope entry, exit and implicit cleanup also require exact
identity: an abstract scope equality cannot release another instance's borrow.
Unresolved families and exhausted context allowance remain incomplete.

Each callee evaluation records independent reference and call event identities,
including repeated source defaults and distinct owned-AST nodes with equal
diagnostic spans. An invocation consumes its own syntax event; extraction or an
indirect call cannot borrow a previous direct-use classification. Final Core
validation reconstructs expression/reference coverage, event ownership, every
instance and template dependency. Selecting a template as the native entry
requires its own substitution proof rather than borrowing a source call.
Exported, extracted, dynamic, recursive and uninstantiated templates remain
unsupported, as do unresolved resource, environment, multiplicity, window or
Result-transfer conditions. Source tests cover ordinary and forbidden instances,
permission reception, independent Result producers and adversarial equal-span
uses; native tests exercise reference cycles, internal aliases and nested copies.
Call events also freeze the dynamic named parent separately from the lexical
owner, so equal-span tokens cannot be exchanged between invocation instances;
an outer handler's lexical owner is not used to infer its executing parent.

Formal collection elements and opaque row families now carry explicit
`One`/`MayMany` multiplicity in both semantic facts and Core provenance. One
formal pivot is not itself a singleton certificate. Exact one-element array
contracts can remove that array's multiplicity reason without removing an inner
collection or row family's reason. Field writes update every live possibly
aliased object; only a proved singleton target receives a strong update, and
other targets retain the old/new union with permission meets. Array, tuple, map
and nested-container source counterexamples require `E0619`, with separate
concrete graph oracles for unselected objects and readonly permissions.

Native or-pattern bindings retain the selected alternative's cells across
suspension. Native CPS also hoists named local-function cells before initializing
their captures, supporting late bindings and recursive/mutually recursive local
calls. The directly effectful named-local source proof remains incomplete;
separate internal Core-to-native tests establish only the backend path. Source
native, frontend and internal IR suites pass on both supported platforms.

Structured scope/fork/join and channel source programs now execute on both hosts.
The four original concurrency and four original channel native cases pass, as
do ten additional source-native tests for handler isolation, abort/cleanup,
method values, sender release, cancellation and Detached return. A source test
also retains an earlier child's result while another child forces collection.
Channel state, managed transport and native-step tests cover queue/in-flight
roots, old-alias invalidation, partial graph replacement with cycles, and a
pre-cancelled send through the complete trampoline. Data is published and rooted
before acknowledging a receipt; cancelled sends close transferred authorities
instead of reporting Closed or successful progress.

An independent source audit exposed and repaired two additional static acceptance
bugs before freezing this implementation batch: capturing an inner scope's
resource into an outer scope's child, and repeatedly consuming outside authority
through a loop. The checker now tracks target-scope ancestry and resource changes
across reachable backedges. The runtime also truncates each child's scope context
to its actual owner. Calibration cases preserve valid ancestor Sender borrowing,
single-iteration and necessarily exiting loops, fresh per-iteration descriptors,
and ordinary repeated send/receive operations. Dynamic multi-owner scopes and
unresolved transfer/message-family proofs remain explicit unsupported cases.

Parallel now invokes actual bounded native workers. Source and runtime tests on
both hosts cover ordered results, source-index fault reporting, rightward fault
suppression after an earlier decisive match, independent branch completion and
retained writes, fixed 64-element fold groups with pairwise merge, nested workers,
callback-local effects and budgets, and GC after worker retirement. Internal Rust
faults are never suppressed as language outcomes. Verified Core preserves each
callback's conditional access paths, participants, selected handlers, termination
judgment and causes.

Generic effect instances retain structural static argument keys and canonical
binder owners. Completed closed direct calls now produce distinct native function
and local-handler identities, including transitive generic calls and normal and
metered entries. Nested closures and escaped retained recipes now preserve their
actual creation and invocation owners across static instances. Completed default
applications also have separate fact views, including local handlers, budgets,
transitive calls and returned closures; supplied-only private instances prune
only their unused fallback. Both hosts pass the targeted generic/default suites
listed in `EFFECT_SPECIALIZATION.md`; these are not a new full-workspace or corpus
run. Unclosed static arguments, unknown callbacks, callable extraction, nested
named functions, captured binders, closure parameter defaults and default exits
without completed application evidence retain explicit NI boundaries.

Retained tail-resume handlers capture exact lexical cells in reusable native recipes; each
call creates fresh delimiters. Tests collect the old creation activation, invoke
the escaped closure repeatedly, preserve lexical shadowing/outer forwarding, and
cross a Parallel worker boundary. Post-v12 regressions also establish metered
handler entries and exact budget counts for recipes created outside the budget.
Persistent non-tail/abort handlers now have native scalar-copy answer regressions;
reference/owning answers still require additional proof. Suspended cleanup uses
the ABI 3 driver described above.

An audit after v16 found an acceptance bug outside the frozen conformance corpus:
budget recovery inherited the completed action's Result inspection state. The
minimal source in `target/budget-result-exits-audit.ril` was accepted by the
frozen v16 compiler with no diagnostics (`target/budget-result-exits-v16.json`).
Native probes in `target/budget-exit-probe/1.json` and `100.json` confirm that the
small allowance returns through recovery before inspecting the caller's Result,
while the larger allowance reaches the action's final assertion panic. The
repair now starts recovery from the budget entry state, preserves normal and
recovery producer identities separately, and checks every continuing exit. The
v16 corpus result remains an observation about that frozen corpus, not evidence
that this additional semantic path was complete. Both hosts pass the independent
exit oracle, Result carrier/alias checks, and four CLI regressions (three native
execution tests plus the original source's E0720 rejection). Cause chains retain
the distinct normal and exhaustion dispositions. Ordinary reference-only
recovery, scoped ownership and recovery writes keep their separate proof gates.

### Recursive summaries use declaration identity

A post-v17 owned-AST audit found two false acceptances when distinct function
declarations had the same diagnostic `Span`. The old recursive summary key used
only `(file, start)`, so a later function could replace an earlier function's
return relation despite their distinct semantic `DefinitionId`s. A recursive
readonly identity consequently borrowed another function's clone/write proof;
an unproductive recursive cycle borrowed another function's scalar return.
The original accepted outcomes remain in `target/recursive-identity-probe.log`.

Recursive analysis now takes canonical `(DefinitionId, &Function)` inputs, and
recursive cutoff instantiation selects the same typed declaration identity.
Repeated registrations deduplicate only identical symbolic syntax; conflicting
syntax for one ID stays unresolved. Distinct same-named IDs remain ambiguous,
and a shadowing local callable cannot fall back to a global function or builtin
contract. The original readonly-write source now reports E0528/E0520, and the
unproductive cycle retains its explicit normal-return-proof NI. A local callable
alias without a composable recursive contract also remains NI. Same-span valid
readonly recursion and independent cloning still verify.

Local Rust verification passed all 326 compiler library tests and 68 targeted
integration tests, including four complete Session/owned-AST regressions in
`tests/recursive_identity.rs`. Evidence is in
`target/recursive-identity-lib.log` and `target/recursive-identity-regressions.log`;
the current shared compiler also passed all-target Clippy with warnings denied
(`target/nested-result-clippy.log`). This repair did not change SPEC, STD, the
original conformance corpus, or any frozen snapshot.

### Historical access evidence across allocation recency

A separate post-v17 source audit found that an unrelated allocation inside a
Parallel callback could hide two writes to the same outside object. Within an
ordinary loop, both callbacks wrote `shared.value`; inserting `cell()` before
or after one write changed the frozen v17 verdict from E0619 to Accepted. The
programs were checked only and were not executed. Reproducers and original
verdicts remain in `target/parallel-recency-alias-audit.ril`,
`target/parallel-recency-alias-v17.json`, and
`target/parallel-recency-after-write-v17.json`.

The repair records an allocation-history epoch on each AccessFact. Before an
access is used against the current heap, only subsequent recent-to-older moves
are applied to its origins and conditional alternatives. Completed invocation
summaries and stored Parallel boundaries use transported accesses as well.
Local callback inputs, for_each regions and fold accumulators retain their own
transport cursors. Older heap nodes retain the prior allocation's owner and
join historical owners at a proved common ancestor; the new allocation does
not acquire ownership of old objects.

Each access also freezes its observed owner alternatives per origin, separately
from the current heap's owner. Transport unions only those observed alternatives;
missing or empty ownership evidence is Unknown and cannot prove locality. This
keeps legitimate callback-local writes local after unrelated histories merge,
without making a MayMany node a singleton or granting current borrow/escape
authority. Core preserves the original observation epoch, current transport
epoch, conditional origins, owner alternatives, participants and causes. Their
meaning and limits are documented in `ACCESS_PROOFS.md`; a complete independent
replay validator for every relation, root and escape judgment is not claimed.

Normalizing access records exposed an adjacent operand bug in the intermediate
compiler: a Binary left Value could still name recycled storage after the right
expression allocated. The exact alias source in
`target/binary-recency-alias-audit.ril` was rejected with E0524 by v17 but accepted
by that intermediate state (`target/binary-recency-alias-current.json`). Binary
checking now transports only the previously evaluated left operand across right
or fallback evaluation, including a separately tracked fallback invocation.
The alias source again reports E0524, while distinct-origin comparisons remain
accepted. Call arguments and aggregate member temporaries are separate transport
consumers and are being repaired in the coordinated evaluation work.

Verification for the access/Parallel repair passed 333 compiler library tests,
64 relevant integration tests, and compiler/CLI all-target Clippy with warnings
denied. The new CLI regression group passed both hosts: five valid sources
executed natively, while the two racing sources were checked and rejected only.
The final combined Binary/Parallel/Result follow-up passed 29 targeted
integration tests and repeated compiler/CLI all-target Clippy successfully.
Logs: `target/parallel-recency-final-lib.log`,
`target/parallel-recency-final-source.log`,
`target/parallel-recency-final-clippy.log`,
`target/parallel-recency-final-native-windows.log`,
`target/parallel-recency-final-native-linux.log`,
`target/access-history-final-regressions.log`, and
`target/access-history-final-clippy.log`. The original corpus and frozen snapshots
were not modified.

### Independent solved-structure consistency checks

`sema::validate::solved_facts` now provides a separate structural consistency
pass over final SemanticFacts. It cross-checks graph/field equations, origins,
binding roots, loan parents, scope registration, causes, condition references,
allocation-transition identities, historical access coverage and canonical
epochs, plus the available Parallel/Concurrent boundary references. The checker
exports its real allocation history and allocated scope registry; the validator
does not infer valid scopes from the owner values it is meant to check.

The result is deliberately named `ValidatedStructure`. Historical owner truth,
full transport replay, resource lifetime/transfer proof and historical
disjointness are outside this token. The missing original observations and
event material needed for those proofs are described in `ACCESS_PROOFS.md`.
The checker now invokes the pass only when its preceding semantic checks would
otherwise accept. A structural failure becomes NI through the existing
Provenance path, with the specific issue kind and available span/cause; earlier
language diagnostics keep priority. The structural token grants no new authority.

Six independent test groups calibrate ordinary, Result, channel, Sender, copy,
cycle and Parallel sources and then damage epochs, owner coverage, graph edges,
roots, loans, scope IDs, causes, relations, handler references and callback
evidence. A read-only corpus calibration checked all 698 accepting-mode source
cases through normal verification and then through this pass: all verified,
and none failed the new structural checks. This is a static calibration, not
a new native or full-corpus verdict. Evidence is retained in
`target/solved-structure-calibration.log` and
`target/solved-structure-corpus-calibration.log`; the original sources and
frozen snapshots were unchanged.
After integrating the verification-boundary hook, all 339 compiler library
tests passed (`target/solved-structure-hook-lib-windows.log`).

## Conditional closure exclusivity and exact-object coverage

A new compile-only counterexample captures a readable `Cell` and passes the
same `Cell` as an independent mutable closure argument. Frozen v17 accepts it
(`target/closure-capture-alias-v17.json`); the current compiler rejects it with
E0524 (`target/closure-capture-alias-current.json`). The input is preserved in
`target/closure-capture-alias-audit.ril`. Neither version of this conflicting
program was executed. This is new evidence beyond v17's original corpus report.

Actual closure calls now check exclusivity before their formal loans are
normalized. Signature probes retain conditional requirements instead of treating
their hypothetical parameters as actual arguments or using type-coverage flags
as an alias proof. Per-object coverage closes a finite private direct-factory
subset across every actual creator and invocation, including distinct generic
instances. Public/extracted/uninstantiated factories, uncovered sibling objects,
unknown creation ancestry and unproved recursion retain NI.

The explicit expression-statement discard subset records a complete frozen
Value graph, newly created object/call intervals and actual invocation ancestry.
It restores the existing capturing-callee recency positive containing
`{make(cell());1}` without borrowing another object's successful invocation.
Returning a stored object for discard does not prove it cannot be called later;
the stored exposure still blocks coverage. Discard does not clear creation-time
capture, loan, copy or Result duties.

Final closure-domain validation reconstructs coverage, requires a check for
every completed invocation and compares the result against the stored
certificate. Check, creation, exposure, discard, observed/current epoch and
historical-owner evidence map into Core using shared typed identities. Missing
probes, missing snapshots, absent sibling coverage and cyclic dynamic ancestry
fail closed. This is a scoped consistency and coverage validator, not a proof
of all historical relation truth; see `CLOSURE_EXCLUSIVITY.md` and
`ACCESS_PROOFS.md` for the exact boundary.

Validation: compiler library 342/342, closure source/Core mutation groups 9/9
and evaluation-recency groups 9/9 pass in
`target/closure-exclusivity-final-tests.log`. The independent footprint oracle
checks 216 concrete object/field assignments. Both hosts pass the two native
groups (`target/closure-exclusivity-native-windows.log` and
`target/closure-exclusivity-native-linux.log`): legal repeated/disjoint calls and
explicit discard execute, while three conflict variants are only checked.
A read-only calibration verifies all 698 accepting-mode original sources and
then validates their closure certificates and solved structures, with no
failure (`target/closure-exclusivity-corpus-final.log`). Original corpus inputs
and frozen artifacts remain unchanged.

The independent escaping shared-loan limitation remains documented separately:
two results of `make(^mut cell)` followed by sequential `first();second()` can
still report E0523 because maker loan participants survive. This batch does not
claim to normalize those escaped loans. Its unchanged source is
`target/escaping-shared-closure-loans.ril`.

## Ended maker loans and sequential retained closure calls

The follow-up to conditional closure coverage fixes the independently preserved
E0523 false positive above. Two `make(^mut cell)` results can now be invoked
sequentially, including interleaved use of the original cell, local marked
aliases, tuple storage and conditional construction. The maker's parameter
loan ends at its invocation boundary while the original retained source
authority survives. Source and permission facts are not erased.

Actual formal-loan entry and end records now cover named calls, closure calls
and productive recursive summaries. Exact globally allocated loan IDs,
activation/lexical ownership and named/closure invocation identities determine
the ended mapping. Current nested Values are normalized, and footprint
consumers normalize restored saved values. Active parent loans and ambient
captured paths remain independent; historical check snapshots remain frozen.
The independent validator checks modes, entry/end membership, source registry
agreement, invocation coverage, binding scopes and cycles. Both event tables
and cause chains are preserved in Core. `INVOCATION_LOANS.md` gives the precise
scope and limitations.

The original rejection is preserved in
`target/escaping-shared-closure-loans-before.json`. Five compiler source/Core
groups cover the restored positive examples and adversarial facts. Genuine
active/captured overlap remains E0523, independent shared closures in Parallel
remain E0619, and uninspected Results remain E0720. The ordinary temporary-mut
escape example retains its explicit NI classification rather than being counted
as a completed language rejection.

Validation logs for this follow-up: the compiler library's 343 then-current
tests and 50 provenance groups passed (`target/invocation-loans-full.log`),
followed by both independent loan-normalization oracle tests
(`target/invocation-loans-oracle.log`). The final five source/Core groups pass on
Windows and Linux (`target/invocation-loans-source.log` and
`target/invocation-loans-linux-source-final.log`); both hosts pass the two CLI
groups (`target/invocation-loans-native-windows.log` and
`target/invocation-loans-linux.log`). All 698 original accepting-mode sources
still verify and pass the structural/closure validators
(`target/invocation-loans-corpus-calibration.log`). The exact original example
now checks as Accepted in `target/escaping-shared-closure-loans-after.json`.
Compiler all-target Clippy passes with warnings denied
(`target/invocation-loans-clippy.log`).

## Complete static result contexts and bounded structural channel guards

The v21 Windows MSVC and Linux GNU component gates each pass 637 Rust tests
across 21 targets, with one explicit ignored test. Native gates each pass 14
executables (19 Rust tests), covering 44 distinct positive Ril sources and
48 entry executions. All 16 compiler/runtime/test artifacts have unchanged
before/after SHA-256 hashes per host. Evidence uses the
`target/static-result-context-and-structural-guards-*-v21` prefixes.

Written receiving contexts now constrain missing static Type arguments while
preserving complete dimensions, lexical binders, actual callable interfaces
and Result identities. Constructors, branches, return operands, Optional
fallbacks and loop exits retain their appropriate contexts. Explicit/input
selections cannot be replaced by the receiver. Frozen computed alias instances
are read by exact declaration/environment/argument key; a missing cache entry
does not execute its alias body under the caller's names. See
`STATIC_GENERIC_RESULT_CONTEXT_DESIGN.md` and `STATIC_RESULT_CONTEXT_FLOW.md`.

Channel conjunction avoids redundant products using complete physical
structural equality, raw clause-set inclusion and witnessed term subsumption.
The selected original operand still undergoes the existing normalization, and
all comparisons share the existing conjunction work counter. No event metadata,
custody, ownership, inspection, queue, clock or execution history is removed.
Six private tests, seventeen guard-law tests and independent finite truth/basis/
support models cover this slice; independent model runs are not compiler or
native passes. Details and preserved operands are in `CHANNEL_GUARD_BDD_DESIGN.md`.

The unchanged single-entry nine-scope source remains NotImplemented: it passes
the former guard-work failures at records 657, 661 and 858, then reaches the
256-case replay bound at record 957. Its registered test is explicitly a
non-authorization regression. Complete Session/Core and native positive gates
remain pending, and this source is excluded from the positive native counts
above. `CHANNEL_STATE_OBSERVER_DESIGN.md` records the next observation contract.

These are component gates, not a current-source full-corpus certificate or a
declaration that the complete native implementation is finished. Scoped symbolic
members, static const/key/constructor applications and remaining quantified
collection/lifecycle obligations continue to be tracked separately. The first
implementation commit, architectural refactoring and editor tooling remain in
the user's required order.

## Current integration after the v21 checkpoint

The v22 and v23 scoped symbolic-member Source gates compiled on both hosts but
failed six of their eight new test groups. The twenty-three older nested,
rigid and scoped groups still passed. Explicitly forwarding U did not solve
the failure: ordinary named explicit application retains its checked-instantiation
NI, and dependent input inference had not selected U from T's structural fields.
Those failures are preserved; they are not positive semantic or native passes.
The subsequent transactional dependent-input implementation and its independent
replay await their combined gate. See `ORDINARY_BOUND_INPUT_INFERENCE_DESIGN.md`.

The v23 frozen Windows library ran seven symbolic-member pure laws successfully.
That filtered algebra run does not certify the failing Source inputs. A separate
frozen test-only observation of the unchanged nine-scope source completed in
69.97 seconds, retained its record957 NI and preserved both executable and source
hashes. Its first failing merge had 263 inputs, a processed prefix of 257 unique
complete states and six unprocessed inputs. Inspection histories had 205 distinct
values; omitting inspection alone would reduce that prefix to 37 projected keys.
No projection is used in production. An actual retained guard contains the false
outcome of a recorded-constant-true Result pattern test, so the next proof must
establish both Source truth and actual evaluation on the relevant path. Global
constant substitution or deletion of inspected debt is not authorized by this
observation. See `CHANNEL_STATE_OBSERVER_DESIGN.md`.

The scalar Meta int-generic and Result-role integration compiles on both hosts.
The v25 scalar target passes all six Source groups on each host, including its
seven-value positive fixture; its newly registered native adapter has not yet
executed. The separate Result-role target passes two nonauthorization groups but
still fails its two positive-dependent groups because a const value argument
entered a Type-source query. The fix awaits its next gate;
`STATIC_CONST_RESULT_FLOW.md` records that distinction. Const
dependent Type syntax, symbolic array extents, keys and constructors remain
separate outstanding work.

Unused duplicate build caches and incremental caches were cleared, releasing
approximately 83 GiB of logical cache space. Verification now reuses one target
directory per host with incremental compilation disabled and two Cargo jobs.
Frozen snapshots, reports and reproducers were retained. The disk-cleanup report
also records the legacy cache that could not be removed by the available cleanup
mechanism; no rejected deletion was bypassed.

## Scoped symbolic members and scalar Meta int generics (v30)

The combined component checkpoint now passes on Windows MSVC and Linux GNU:
25 compiler targets, 679 passed Rust tests and one explicit ignored test per
host. Compiler Clippy passes with all targets and warnings denied. The fresh
frozen native batch passes 17 executables and 22 Rust tests, exercising 49
distinct positive Ril sources and 53 entry executions per host. All 19 artifact
hashes remain unchanged, including the unchanged ABI3 runtime libraries.
The machine-readable checkpoint is
`target/const-int-and-dependent-bound-v30-checkpoint.json`; per-platform Source,
Clippy, build, native logs and before/after hashes share that prefix.

Scoped symbolic array and callable members retain their genuine caller Type
identities, complete dimensions and actual callable interfaces. Dependent U
selection comes from complete structural input equations, with a transactional
producer and independent Source replay. Numeric preparation can defer a possible
bound input, but only the actual invocation's completed proof can freeze it;
the result receiver cannot replace an incompatible input selection. The three
original inferred positive sources now execute natively on both hosts.

Scalar Meta `n:int` has separate real value IDs, closed selections and lexical
role masks. Universal definitions retain unknown int values. The Result proof
keeps producer identity through const forwarding and block, pattern and loop
shadows, and freezes a pure value argument when constructing its application.
Static const scalars do not authorize dependent Type syntax or symbolic extents.

Lint integration packs private contexts without changing inference order and
boxes only large control payloads/range cursors, with compile-time size bounds.
The subsequent workspace format check passes in v31; its three corrections are
Rust whitespace only, with no source-semantic change or artifact rebuild.

This remains a component checkpoint. The original nine-scope channel source
still reports NI at the replay case bound; its accepted-program gates and native
adapter remain pending. Complete Boolean evaluation receipts and a Source-grounded
reader are designed and independently modeled, but not registered in production.
Symbolic static extents, other static sorts, ordinary explicit named applications,
composite dependent Type leaves and other quantified obligations remain separate
work. The full current corpus and first implementation commit are still pending;
architectural refactoring and editor tooling follow that commit.

## Complete condition receipts (v35/v37)

The conservative complete-pattern receipt is registered. Its actual operand
token comes from the real expression emitter, and the independent reader uses
the frozen analyzed Source, original formal/capture identities and actual
control path. Unknown prefixes, computed callees, preceding operands, later
match arms, unresolved incoming calls and heap-bearing carriers provide no
truth. Refinement constrains only a receipt's executed case; custody, inspection
history, queues, task clocks and permissions are preserved.

Windows MSVC and Linux GNU each pass the v35 complete 25-target component suite:
704 Rust tests and one explicit ignore. The strengthened v37 business fixture
then passes three focused Source/Core tests and compiler all-target Clippy on
both hosts. Its native Some(Ok), Some(Err) and None entries require successful
scope completion and exact message round trips. Nested and cloned unpaid
business Results reject with E0720 and are never executed.

The v37 frozen native cohort passes 18 executables and 25 Rust tests per host,
with all 20 CLI/runtime/test artifact hashes unchanged. The unchanged previous
49-source/53-entry adapter inventory plus the new one-source/three-entry fixture
gives 50 distinct positive Ril sources and 56 entry executions. This source
inventory is distinct from the runner's automatically counted Rust tests.
Evidence is recorded in `target/boolean-evaluation-receipts-v37-checkpoint.json`.
The v37 whole Source suite was not rerun; v35 and the later focused gate are
reported separately.

The unchanged E508 nine-scope fixture still reports NI. A separate frozen v37
CLI check records the case-bound failure at event1040, cause52625, Source0:208,
with unchanged CLI and fixture hashes. The earlier event957 is historical v23
evidence, not the current sequence. This refused input has no Core/native pass.

Independent receiving review also exposed nine old v30 erroneous acceptances:
stored dynamic/fixed dimensions and callback signatures can be overwritten at
call, default, binding, return and typed-member boundaries before comparison.
Their exact frozen before checks are retained. The common source-coordinate
model and argument/default epoch metadata pass eight focused Rust tests per
host at v38; receiving gates and their independent replay remain in progress.
See `SOURCE_RECEIVING_VALIDATION.md`. Neither this component checkpoint nor the
older corpus report establishes whole-compiler completion. The first
implementation commit, architectural refactoring and editor tooling are pending.
