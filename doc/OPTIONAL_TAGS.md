# Optional constructor tracking

An unknown optional value has a distinct `OptionalTagId`. The identity names its
immutable Some/None choice, not its heap object, access permission, or Result
inspection. Two independent symbolic input positions receive independent tags.
An actual caller can pass the same value to two parameters and retain one tag.

The tag arena stores creation scope, original payload type, and a source cause.
Each constructor creates its own wrapper cause with the payload source as a
parent. Every copied or projected value carrying the tag must retain this
source in its cause ancestry. Branch joins retain the actual sources of that
same binding or stored member; unrelated values cannot replace those sources.

Copying and deep cloning preserve the tag bit. Cloning an inner Result creates
a new producer obligation. Inspecting the original does not inspect its clone,
even though both optional values agree on Some/None. A known Some/None wrapper
does not accidentally inherit an inner optional's identity.

Unknown writes clear the old tag and stored boolean evidence on affected
values. Detached immutable scalar copies retain their own identities and
evidence. Merely forgetting a known truth about an unchanged value does not
create a new tag.

Message completeness requires a typed payload witness and a tag when Some/None
is unknown. The private ledger and independent replay enumerate which business
producers actually exist. Some/None tests select these cases but pay no Result
debt. The inner Result still needs its actual inspection or return receipt.

Independent validation checks fresh declaration argument snapshots against
their real parameter positions and structural paths. Combining two independent
formal paths into one valid tag is rejected even when the supplied owner,
payload type and cause are individually valid. Actual input aliases remain
legal.

The real whole-function source header identifies a declaration entry. Probe,
caller, source-token and parent metadata cannot turn its independent inputs
into an actual alias or skip the required parameter count. Actual calls whose
tags provide a proof need their own source occurrence, evaluated named callee
and caller context. A surrounding callback application is not that call.

The proof dependencies include message carriers, ordinary Result inspections,
conditional inspection evidence and execution/exit guards. An Option<int> can
matter to an ordinary Result receipt even when every message payload is
Result-free. Unrelated scalar computations do not owe transport source proof.

An AnyIndex element family does not provide one shared bit for all collection
members. Formal array, set and map construction carries a family restriction;
it retains payload obligations without an individual presence identity. Unknown
collections and recursive or coarsened payloads still require further evidence.
The tag registry alone does not make an incomplete payload graph complete.

The IDs and arena are preserved in Core provenance. They are compiler facts;
the runtime ABI and executable value representation are unchanged.
