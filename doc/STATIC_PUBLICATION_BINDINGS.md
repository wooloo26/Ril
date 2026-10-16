# Static publication binding contract

This is the implementation contract for the legal inner-shadowing failure in
`target/implementation-gap-audit/static_reference_shadowing.ril`. The original
source and NI report remain unchanged. Its renamed-inner-binding control already
passes. SPEC lexical resolution permits inner declarations to shadow outer ones.
This document records the approved change; validation evidence is added after
implementation, not inferred from the design.

Collection identity and lexical binding identity are separate. An evaluator
collection ID selects one object, regardless of spelling or equal contents. A
private monotonically allocated `PublicationBindingId` identifies one lexical
publication/binder. A visible-name table selects the current token for a name.
Source spans remain diagnostic locations. Existing EnvironmentIds continue to
identify evaluated declaration-group captures and are not reused as object IDs
or fabricated for blocks that have no declaration group.

Publication records carry collection ID, binding token and spelling. Reification
may emit an ordinary Name only when its recorded token is still the visible
binding for that spelling. Multiple aliases may denote one collection, and a
different allocation with equal contents remains a different pool node. Scope
restoration restores visible tokens without rewinding the fresh-token counter.
Out-of-scope publication records confer no lexical visibility.

Every completely typed, exportable closed local reference uses the existing
sealed constant-reference representation at its first runtime publication. This
avoids publishing an inline object and later creating a second pool object when
its name is hidden. If no recorded alias remains visible, the same collection-ID
pool node supplies the reference. This is the same representation used for
module constants; there is no new AST node, public value API or runtime ABI.
Resource, opaque, callable/family and graph-shape boundaries continue to apply.

The first-publication order is:

1. Resolve the initializer and written type in the preceding lexical scope.
   Run existing static typing, evaluation, numeric reception and shape checks.
2. Retain the actual immutable value and its collection ID. Export a closed
   reference through the existing constant pool, or propagate its explicit
   diagnostic/NI boundary. A previous pool node is reused only for the same ID.
3. Commit the new lexical binding token after the initializer. Register its
   collection publication only after successful reification. Scalar, type and
   callable binders also mask older same-spelled runtime publications.
4. Preserve the existing universal Result-flow check and its later receipt-seal
   phase. Export is provisional; an evaluated inspection never seals a Result
   before every required normal path has been proved. Failed proof cannot lower
   an unsealed constant into a verified program.

| Lexical entrance | Required visibility/restoration |
| --- | --- |
| Meta and ordinary bindings | Initializer uses the preceding scope; every bound pattern name then gets a fresh token |
| Ordinary function/lambda parameters and generics | Sequential parameter/default scope, then callable body scope; restore the caller transform scope |
| Block and unconditional loop | Fresh local binders, hoisted declaration handling, restore outer values and visible tokens |
| For source/pattern/body | Source in the outer scope; pattern and body in their child scope |
| While condition/body | Condition in its scope; successful condition binders available only to the body |
| If and boolean conditions | Successful pattern binders mask only the paths on which the language makes them visible |
| Match arm pattern/guard/body | Pattern test in the outer scope, bindings in that arm, restore between arms |
| Handler parameters/body | Child lexical scope, without permitting static runtime-handler execution |

Runtime binders must also mask an older static value while transforming a scope;
the publication table must not cause a global constant to replace an unavailable
runtime local in a type computation or static initializer. Pattern traversal
includes tuple/record/rest, constructor, mode and type binders. Existing duplicate
declaration and phase/family diagnostics are retained.

Required evidence is the unchanged audit source through Session/Core and native
execution, fresh-versus-edited Session agreement, nested scope restoration,
same-object aliases, distinct equal-content objects, hidden local references,
ordinary parameter/pattern masking, immutable publication and clone isolation.
Unchecked Results, resources and unsupported qualification cases are negative
checks only. Existing graph and static-loop suites remain independent gates.

## Implemented checkpoint

`static_eval/publication.rs` now owns the private tokens and visibility table.
The transform restores both the value/declaration environment and visibility on
scope exit, including failure. Condition-pattern visibility computes both boolean
outcomes once per syntax node. An independent unit model enumerates every concrete
short-circuit path for eight small condition trees and compares both outcomes;
two other unit tests cover restored tokens and aliases of distinct objects.

All first local collection publications now select the existing constant arena.
An unhidden alias may still reify as its exact lexical Name; when every alias is
hidden, the same collection ID supplies its existing ConstRef. Repeated ordinary
calls to a function containing one local meta constant observe that same frozen
node. Different evaluated allocations, including equal-content ones, keep
different nodes. Native mutable-clone tests observe both facts and verify that
the original immutable pool remains intact.

The original audit source and the durable CLI fixture have identical SHA256
`E63854211B07AE6F4B2CC2E8A8459C8171254F0BBF33FD0B9C8E41A9DDA45709`.
Under an independent Linux 512 MiB/20-second process limit, its unchanged source
checks accepted in 0.10 seconds with maximum RSS 29336 KiB and executes the
existing `test_native` entry as returned-unit/exit 0 in 1.40 seconds with maximum
RSS 248828 KiB. Raw reports are
`target/static-reference-shadowing-after-linux-{check,test}.{json,time,exit}`.
The original NI/control reports remain unchanged.

The Windows checkpoint runs the same source under a preinstalled, verified
512 MiB job and 20-second deadline. Check returns accepted/exit 0 in 45 ms;
the native entry returns returned-unit/exit 0 in 1152 ms. Conservative job peaks
are 67186688 and 137539584 bytes and include the dedicated PowerShell helper.
Reports are `target/static-reference-shadowing-after-windows-{check,test}-bounded.json`.

Linux passes six new Session/Core groups and five new CLI groups. The related
static graph, loop, Result and tail-call CLI suites plus the bounded capture
regression bring the selected CLI gate to 37 groups, all passed. The compiler
unit gate passes 363 tests with the explicit full execution matrix ignored;
the three new ordinary boolean-loop groups also pass. Selected compiler and CLI
Clippy gates pass with warnings denied. Evidence is
`target/static-publication-{source-linux-v4,source-linux-v5,native-linux-v1,clippy-linux-v1,cli-clippy-linux-v1}.log`.

Windows also passes the six new groups and all related Source/Core gates in one
98-group run, and the same 37 selected CLI groups:
`target/static-publication-{source,native}-windows-v1.log`. Its compiler unit
checkpoint likewise passes 363 tests with one ignored explicit matrix. These
passing checkpoints precede a separate channel-schema edit window; the final
Windows defaults/Clippy follow-up was paused when that window temporarily made
the shared compiler unbuildable. That build failure is preserved in
`target/static-publication-source-witness-final-windows-v1.log`, and is not a
successful follow-up gate or a static-publication failure.

Result publication retains its separate boundary: an uninspected discarded
producer is E0720; an escaping pending top-level producer requires its runtime
inspection receipt and remains NI; local meta Result publication inside an
ordinary callable still requires a separate receipt scope and remains NI.
Readonly local constants reject writes with E0522. Nominal/unsupported nested
qualification checks still reject or report NI. None of these negative sources
is executed. This checkpoint does not establish complete static semantics or a
full frozen-corpus result.
