import RilAccess.Examples.Provenance
import RilAccess.Examples.Access
import RilAccess.Examples.Call
import RilAccess.Examples.Graph
import RilAccess.Examples.Boundary
import RilAccess.Examples.Summary
import RilAccess.Examples.Draft
import RilAccess.Examples.Scoped
import RilAccess.Examples.Visibility
import RilAccess.Examples.Ctl
import RilAccess.Examples.ResolvedProvenance
import RilAccess.Examples.RecursiveStorage
import RilAccess.Examples.Results
import RilAccess.Examples.Composition

namespace RilAccess.Examples

def allExamples : List (String × Bool) :=
  examples ++ Integrated.Examples.examples ++ Calls.Examples.examples ++
    GraphAuthority.Examples.examples ++ CoreBoundary.Examples.examples ++
    CoreSummary.Examples.examples ++ RecursiveStorage.Examples.examples ++ Draft.Examples.examples ++
    Draft.Examples.loweringExamples ++
    ScopedExamples.examples ++ VisibilityExamples.examples ++
    CoreCtl.Examples.examples ++ ResultInspection.Examples.examples ++
    Provenance.Examples.examples ++ Provenance.Examples.compositionExamples

end RilAccess.Examples
