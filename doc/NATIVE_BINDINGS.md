# Native external provider bindings

This document specifies the native implementation interface for `.d.ril`
declarations. It adds no Ril syntax and changes no language exchange contract.
It is an implementation design; features not yet connected to the compiler and
runtime remain unavailable and must not be reported as executed native support.

## Binding identity and configuration

An external declaration is identified by its project-relative logical module
path and original declaration name, for example `platform/text::get_data`.
The module path omits `.d.ril`. Import aliases and resolver-generated symbols
such as `ril__module_1_get_data` are not binding identities. The frontend retains
both the stable external identity and the internal declaration identity.

Build options and `--bindings PATH` accept an explicit bindings manifest. Semantic
check mode does not read the manifest or execute a provider. No declaration name selects
a platform library, shell command, or native symbol implicitly. A manifest has
this form:

```json
{
  "version": 1,
  "providers": [{
    "id": "text-provider",
    "program": "bin/text-provider",
    "args": ["--ril-provider"],
    "bindings": {
      "platform/text::get_data": "get_data",
      "platform/text::transform_text": "transform_text"
    },
    "max_frame_bytes": 67108864
  }]
}
```

The driver resolves a relative program path against the manifest directory and
stores the resulting absolute native path. Arguments remain separate strings;
the runtime does not invoke a shell. Provider identities and declaration
bindings must be unique. Unknown versions, duplicate keys, malformed identities,
missing required bindings, and unsupported contracts are explicit build errors
or unavailable outcomes before object emission. A missing or replaced executable
at execution time is a contained binding failure.

The default frame limit is 64 MiB. It is a configurable provider transport
limit, not a restriction on the Ril value graph or a new language type rule.
Exceeding it reports an explicit binding failure without sending a truncated
value. Providers must support wire protocol version 1 independently of the
version of the Ril native runtime ABI.

## Process and wire boundary

Each invocation runs in an isolated native provider process. Its standard input
and output carry protocol frames; its standard error is drained independently
with only a bounded diagnostic tail retained. A frame consists of an unsigned
64-bit little-endian JSON byte length followed by that many UTF-8 JSON bytes.
Receivers check the configured bound before reserving or reading the body.
Unknown message fields and invalid message order are protocol failures.

The provider first sends `Ready` with its protocol version. The owner then sends
`Invoke` with a fresh call identity, stable declaration identity, provider export,
concrete exchange signature, normalized static arguments, ordinary value graph,
and argument references. Each static argument includes its binder name and sort:
type identity with an optional schema index, typed constant value, effect identities,
or capability identities. Phantom arguments are retained even when no ordinary
argument or result mentions them. Several concrete instances of one declaration
share its export binding but have separate bound descriptors. The first protocol
implementation carries scalar static constants; unsupported compound static
values remain explicitly unavailable until their graph encoding is implemented.
Default arguments execute as ordinary Ril code before invocation. Native lifting
identifies their anonymous and local named callables by the concrete enclosing
function instance and lexical source site. Different instances therefore keep
their substituted bodies and capture cells, while normal and metered entries of
the same instance share a callable identity. A budget established inside a
default ends before the external invocation; external execution itself does not
gain finite-budget coverage from a closed effect row.
Retained-handler certificates carry the concrete named definition or anonymous
callable site identity, together with separately assigned handler definition
identities. An anonymous site belongs to its lexical callable owner; repeated
analysis or invocation does not create a different site. Source spans locate
sites within that owner but cannot authorize a different instance's recipe.
The Core and native metadata preserve these identities through lifting and
metered entry creation. Missing owner or handler-definition evidence remains an
explicitly unavailable retained-callable path. Existing effect, capability,
resource and answer obligations are still checked before this metadata is built.
The wire format is defined by
`ril-runtime-api::foreign`; it contains no platform addresses, managed generation
handles, native closure environments, or resource ownership.

Ordinary graphs use an explicit node table with indexed edges and ordered roots.
Arrays, maps, sets, ranges, tuples, record fields, constructors, nominal wrappers, and opaque ordinary
data can refer to existing nodes, including themselves. Repeated references and
cycles therefore survive exchange. Validation walks the table without recursively
expanding shared graphs. Integer widths and signedness are explicit; decimal
strings preserve full-width 64-bit and arbitrary integers. Floats carry their width and raw
bits, preserving signed zero and representable special values. Strings are UTF-8;
bytes are uninterpreted byte arrays. Map/set iteration order is preserved. Record
fields cannot repeat. Fixed array lengths and immutable qualifiers remain in the
schema arena rather than being discarded or confused with host memory layout.

Structural wire validation is followed by validation against the declaration's
exchange schema. A structurally valid graph does not grant a type, freshness,
write permission, resource authority, or callback authority. Runtime decoding
installs graph placeholders before edges so aliases and cycles are preserved.
Foreign results remain ordinary immutable exchange values under the existing
frontend provenance contract. Opaque ordinary payloads are serialized descriptors,
not host pointers. Listed external resource contracts requiring persistent realms,
including DOM descriptors, remain explicitly unavailable until their realm and
resource lifecycle protocol is implemented.

## Temporary callbacks and control flow

A separate callback argument is represented by a token scoped to this call.
Tokens do not occur in ordinary graph nodes. Schema callback locations retain
argument-and-projection paths; protocol version 1 supports separate top-level
callback arguments, and a nonempty path is explicitly unavailable until its input
encoding is implemented. The runtime retains the actual Ril
callable, its declared invocation permission, and the source-selected handlers
on the calling task. The provider cannot inspect the environment or execute Ril
code in another thread or process.

A `Callback` request carries the call identity, a strictly ordered request
identity, a supplied callback token, and ordinary argument roots. The owning
native trampoline validates the request and invokes that callable through a
normal callback continuation with its actual effects and permissions. It sends
`CallbackReturn` only after a valid ordinary result exists. The provider may
invoke a temporary callback more than once using distinct request identities;
the provider is obligated to await the response before another request. The
runtime serializes callback execution and checks logical request identities;
buffered pipe arrival alone does not prove when the provider sent a later frame,
so it does not claim to detect every violation of that causal obligation.
Token use after completion,
unknown tokens, replayed requests, nested callable payloads, and resource payloads
without a listed contract are rejected.

Ril panic, cancellation, or delimited abort abandons the external invocation and
terminates and reaps the provider. The foreign process cannot swallow or replace
the Ril control outcome. All temporary tokens expire. A successful provider
`Return` has one ordinary result root and must be followed by successful process
completion. Constants use a distinct declared constant-read binding entry with
zero arguments; they do not masquerade as source function declarations.

## Faults, roots, and cancellation

Process crashes, traps, nonzero exit, malformed replies, and protocol violations
become deterministic Ril language panics, contained by normal task/scope rules.
A provider can return a declared `Result` error as ordinary value data. Unexpected
Rust panic or violated runtime invariant inside the transport remains
`InternalFault` and takes priority over concurrent cancellation.

Protocol IO, provider waits, and termination run outside the managed heap gate.
Transport threads own bytes, native pipe handles, and cancellation tokens only.
Managed callback values and pending results remain precisely rooted in the
owning invocation while it is suspended. Every started transport worker is
joined and every provider is reaped before the invocation's host state retires.
Cancellation never fabricates a successful result, empty reply, or domain error.

The ordinary bodyless-function termination rule remains unchanged: foreign calls
are possibly divergent and excluded from `Div::budget`. The isolated provider
adapter does not certify arbitrary host execution as finite or budget-covered.

## IR and native integration

The shared frontend records external function/constant descriptors separately
from ordinary bodies, including stable identity, internal name, parameters,
defaults and labels, ordinary exchange schema, and separate callback slots.
The driver injects validated explicit provider bindings after semantic checking.
No missing external body is replaced by an empty body or guessed builtin.

Native lowering emits a real native continuation edge for the external call and
installs immutable bound descriptors during entry initialization. The backend
does not embed compiler types or AST into the runtime. The runtime resumes the
owner trampoline for callback requests and result publication; source evaluation
order, handler selection, scoped cleanup, and Result obligations retain their
ordinary native behavior.
