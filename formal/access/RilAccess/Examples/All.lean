import RilAccess.Examples.Provenance
import RilAccess.Examples.Access
import RilAccess.Examples.Call
import RilAccess.Examples.Graph
import RilAccess.Examples.Boundary
import RilAccess.Examples.Summary
import RilAccess.Examples.Resumption
import RilAccess.Examples.Draft
import RilAccess.Examples.Handoff

namespace RilAccess.Examples

def allFixtures : List (String × Bool) :=
  fixtures ++ Integrated.Examples.fixtures ++ Calls.Examples.fixtures ++
    GraphAuthority.Examples.fixtures ++ CoreBoundary.Examples.fixtures ++
    CoreSummary.Examples.fixtures ++ CoreResumption.Examples.fixtures ++ Draft.Examples.fixtures ++
    Integrated.HandoffExamples.fixtures

end RilAccess.Examples
