# Static constant graph implementation boundary

This records the constant graph contract and its implementation evidence. Native
execution is only established by the tests explicitly recorded below.

## Identity and scope

The evaluator already assigns each immutable collection an identity. Export a
finite constant arena with typed graph/node IDs, roots, scalar leaves and typed
container edges. Equal contents do not merge different allocations. A repeated
reference to one evaluator collection ID always selects the same arena node.
Variants preserve their payload references. Resource and callable-environment
values do not enter this ordinary constant arena.

Concrete module-level constants enter the arena after evaluation and static
typing. Closed local ordinary-data constants now use the same arena from their
first publication, with explicit lexical binding tokens as described in
`STATIC_PUBLICATION_BINDINGS.md`. Generic instances, recursive construction and
incomplete nominal/qualification information retain their separate boundaries;
local Result publication still requires its own receipt scope.

The initial frontend uses a private evaluator table of reserved internal names.
Public owned-AST validation rejects NUL in names and paths before resolution or
static evaluation, including when the input also contains a real meta constant.
Only compiler-created names can select the corresponding `ConstRef`. These
references never supply a new lexical binding or bypass ordinary binding checks.

## Frontend certificate

Do not materialize a nested graph by expanding many AST allocations with the same
source span. Current source allocation/fact lookup uses spans in several places;
such expansion could merge allocation identities or select another expression's
facts. Nor should source bytes, offsets or file IDs be fabricated to make those
allocations look distinct.

The evaluated program needs a private constant-reference table alongside its
ordinary syntax. Compiler-created references select arena IDs from that table;
untrusted source/owned AST cannot manufacture a populated table. Semantic
checking validates each referenced node once, creates its storage/permission
facts using constant-node identity, and then reuses that exact value at later
references. Source spans remain evidence locations. The verification boundary
must carry the arena, its type/qualification witnesses and the solved origin
mapping together.

The reference table is not a bypass around normal binding checks. Contextual
types, fixed lengths, immutable publication, named state access, Result duties,
and clone eligibility still run. Static execution of one branch cannot stand in
for checking the complete declaration. An unavailable witness produces an
incomplete result; it does not grant a fresh independent graph.

## Core and native initialization

Core and Native retain the typed constant arena and its provenance mapping.
Backend preparation orders its nodes with Kahn's algorithm, counting repeated
edges without expanding shared paths or merging equal contents. The native
program entry materializes this plan once, before foreign constants and the user
global initializer: each node gets one private global cell and each edge reads
the already-created target. These allocations occur after semantic verification
and use arena identity, not source-expression lookup. Both normal and metered
user code read those same cells. Original source constants and later meta
projections reference the shared nodes through the pure Core `ConstRef` leaf.

Existing managed globals provide precise GC roots, including shared workers.
The pool belongs to the compiled program, never to an individual function call
or physical native step. No new native ABI is needed merely to construct an
acyclic pool with existing allocation/field operations. A future cyclic pool
requires shell allocation followed by edge installation before publication.

## Required evidence

- A nested array/tuple/map graph with repeated children keeps those aliases when
  copied; distinct equal children remain distinct. Later meta constants that
  select an earlier child reuse its storage identity.
- Compiler facts and Core provenance identify each arena node independently of
  spans, including different nodes produced by one static call.
- Qualified immutable children cannot regain write authority through constant
  publication, wrappers, type annotations or cloning.
- Actual Windows/Linux programs observe alias preservation through a lawful
  mutable clone; forced GC and child tasks retain the immutable pool.
- Unused/dead static branches still receive required typing/Result checks.
  Fresh and edited Sessions agree on diagnostics and graph structure.
- Unsupported local/generic/nominal/resource cases remain visible and cannot be
  smuggled through the private reference table or a public owned-AST entry.

## Current frontend evidence

`ril-compiler/tests/static_constant_graphs.rs` currently passes twelve source-test
groups on Windows and Linux. They cover shared versus distinct equal-content children,
later projections, Map and Option edges, fixed nested array storage, explicit
numeric widths under pointer32/pointer64, readonly publication, forged owned AST,
fresh/edit Session equality, module forwarding, solved collection constraints,
and all nine pairs selected from three independently
allocated equal-content arrays. Core tests retain distinct node certificates at
the same source span and a new outer shell's old shared children. Immutable
evaluator collections share their backing storage; a 64-level binary DAG exports
66 nodes without unfolding its paths. The 30 static-evaluation unit tests and
complete 590-test compiler suite pass on both hosts at this checkpoint.

Static record constructors check their stated member types before export.
Closed structural record values now retain their field slot modes through static
typing, generic identity, evaluation, spreads, rest destructuring, the constant
arena and Core type provenance. These type modes do not grant write permission
to a published constant. Mutable clone slots follow the retained declaration;
explicit spread overrides introduce new readonly slots unless a typed constructor
specifies otherwise. Mutable field transfers are invariant, including callable
result types in unused definitions.

Written binding types and function result types also contextualize new record
syntax at value-producing tails, including blocks, if branches and match arms.
The same small elaboration is used by static typing and evaluation. It never
retypes an existing name or call result, and it does not reinterpret an explicit
return using an enclosing binding's type. Two additional record groups exercise
this distinction; all ten record source groups and both related native groups
pass on Windows and Linux (`target/static-record-context-*`).

The subsequent component checkpoint passes 29 frontend tests and 11 native
execution tests on each host: the 12 constant-graph tests, eight record tests,
six evaluation-family tests and three fixed-array mutation tests, followed by
nine constant-graph and two record/fixed-array native groups. The record tests
include Core slot types and fresh-versus-edited Session results after removing
and restoring a mutable field. Logs are `target/static-records-final-*` and
`target/static-records-native-*`. The broader simultaneous compiler run has four
failures in ongoing Sender-template work; it is not a new full-workspace pass.

Record slot-mode conversions without a construction/view witness, explicit
Immut signatures, nominal values, and reified mutable-record static arguments
remain incomplete. In particular, the implementation does not infer a reference
view from a storage node's identity: different views must carry their own type
witness without splitting the underlying object's identity.

Array length-changing operations now reject fixed storage with E0301, as required
by STD's dynamic-array parameter contract. Three source-test groups cover every
operation, no-op argument values, aliases, helper calls, clones and static pool
references. Rejected operations retain the original fixed-storage fact. Element
writes and fresh dynamic shells produced by reverse/concat remain available.

## Current native evidence

`ril-cli/tests/static_constant_graphs.rs` passes nine source-test groups on
Windows and Linux. Mutable clones observe shared children, distinct equal-content
allocations, later projections, ordered map and Option edges, and distinct outer
shells that still share their children. Empty and None-first containers preserve
their contextual types; int, u8, i64, bigint, f32, bytes, string and bool use the
existing runtime literal representations. Fixed arrays retain their shape.
Normal and budget entries also return the same child: cloning their combined
results and mutating one path changes the other, while the original stays intact.
The additional lexical-shadow regression uses a static local `child` alongside
an ordinary global function with that name, then tests alias-preserving cloning
through that actual function call.

Pool publication uses the existing managed handle-root path before allocating
the node's cell or private key. A 400-child constant pool forces GC during entry
initialization: array, cell and key allocations alone exceed the initial
1024-live-object threshold. A separate source worker allocates 1200 arrays,
crosses that same threshold and then reads the constant graph. Only collection
reduces the runtime live-object count, so these checks necessarily exercise GC.
Globals provide the roots and are carried into shared workers by the existing
worker contract.

Two backend boundary tests verify sparse IDs across graphs, repeated edges and a
64-level shared binary DAG without path expansion. Duplicate graph/node IDs,
unknown edges, mutable publication, inconsistent fixed lengths and private-cell
name conflicts fail closed. Cycles remain explicitly incomplete pending a shell
initialization contract. The existing native `static_formatting` and
`frontend_completion` suites also pass on both platforms.

## Next qualification boundary: per-reference type views

Explicit nested Immut remains disabled until the following contract is carried
through all phases. This is a design, not implemented coverage.

- A static reference view retains its type independently of the collection's
  physical identity. Qualifying one reference must neither retype every alias
  nor invent another object. Scalars and complete nested types need witnesses
  too; field-mode sets alone do not represent these views.
- A proposed constant alias node selects an already represented constant value
  with the same origins and handle, but a distinct qualified type certificate.
  Container members can refer to that view. Native initialization would use the
  target handle and its existing roots, without copying its object graph. This
  requires an explicit Core/backend contract before the frontend gate opens.
- Clone of an outer Immut wrapper drops only that outer wrapper. A nested
  qualified child keeps its restriction. If that child is also reachable through
  another ordinary path, graph cloning preserves the alias and must not leave a
  writable path into the same frozen copy.
- Container invariance must be checked independently of permitted top-level
  readonly qualification conversion. Checking convertibility in both directions
  is not enough when both directions preserve immutable provenance. Fresh record
  or container construction can type its new slots from the written context;
  an existing container cannot acquire different element qualifications that way.
- Required regressions include two views of one collection, nested and repeated
  Immut, outer-wrapper cloning, shared qualified/unqualified children, fixed
  lengths, constant forwarding, generic substitution and edited Sessions. Tests
  must inspect semantic origins/types and actual native clone behavior.

