# Finite static map Result tracking

Exact finite map lookup returns an Optional containing the existing member.
Its Result producer identity and actual callable interface are preserved.
Key comparison and Optional presence do not inspect a business Result, and a
miss creates no hypothetical member or producer. Overwriting a dictionary key
does not pay the displaced producer's obligation.

The transfer rule accepts only the Result-flow engine's finite map graph and
established key equality. Unknown equality and unquantified formal maps retain
their incomplete obligations; actual finite arguments cannot supply a proof
for an otherwise unproved universal function body. Lookup charges the existing
proof work counter without changing its allowance.

The valid fixture was NotImplemented in the frozen v9 compiler, recorded in
`target/static-result-map-lookup-before-windows-v9-corrected.json`. An earlier
fixture incorrectly used a runtime-only panic in static code; its rejection
and source are preserved separately and are not evidence about map tracking.

The four compiler test groups cover both static layouts/Core, presence and
absence, overwritten debts, and refusal to borrow an actual finite input for a
universal map. One group independently enumerates all 288 combinations of two
producer identities or aliases, duplicate/distinct keys, two lookups and two
inspection choices. Each case uses a fresh Session; expected inspection debt
comes from a concrete dictionary and producer set, not the compiler's facts.

Both v11 combined gates pass 605 Rust tests, with one explicit ignore. This
includes those 288 concrete programs per host. Frozen v11 Windows MSVC and
Linux GNU native runs both pass all 12 test executables (17 Rust tests),
covering 38 distinct positive Ril sources and 42 entry executions. This
includes the new finite map program. All 14 artifacts (compiler, runtime and
test executables) have identical before/after SHA-256 hashes on each host.
Reports are `target/source-index-and-result-maps-native-windows-v11-report.json`
and `target/source-index-and-result-maps-native-linux-v11-report.json`.
Negative and incomplete checks in the adapters are not native executions.
This component gate does not establish complete map quantification or full
compiler conformance.
