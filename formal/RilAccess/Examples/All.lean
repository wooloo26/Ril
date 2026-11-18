import RilAccess.Examples.Provenance
import RilAccess.Examples.Access
import RilAccess.Examples.Call
import RilAccess.Examples.Graph
import RilAccess.Examples.Boundary
import RilAccess.Examples.Summary
import RilAccess.Examples.Draft
import RilAccess.Examples.Handoff
import RilAccess.Examples.Scoped
import RilAccess.Examples.Visibility
import RilAccess.Examples.Concurrency
import RilAccess.Examples.ResolvedProvenance
import RilAccess.Examples.Composition

namespace RilAccess.Examples

def allFixtures : List (String × Bool) :=
  fixtures ++ Integrated.Examples.fixtures ++ Calls.Examples.fixtures ++
    GraphAuthority.Examples.fixtures ++ CoreBoundary.Examples.fixtures ++
    CoreSummary.Examples.fixtures ++ Draft.Examples.fixtures ++
    Integrated.HandoffExamples.fixtures ++ Draft.Examples.loweringFixtures ++
    ScopedExamples.fixtures ++ VisibilityExamples.fixtures ++
    CoreConcurrency.Examples.fixtures ++ Provenance.Examples.fixtures ++ Provenance.Examples.compositionFixtures

end RilAccess.Examples
