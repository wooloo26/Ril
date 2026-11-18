import RilAccess
import RilAccess.Examples.All
import AuditSupport

#check RilAccess.CoreVerification.verified
#print axioms RilAccess.CoreVerification.verified
#print axioms RilAccess.Provenance.verified_program
#print axioms RilAccess.Provenance.verified_machine
#print axioms RilAccess.Provenance.machine_progress
#print axioms RilAccess.Provenance.Examples.divergent_loop_steps
#print axioms RilAccess.Provenance.Examples.divergent_recursion_steps
#print axioms RilAccess.Provenance.summarize_at_call
#print axioms RilAccess.Provenance.Examples.exceptional_cleanup_executes
#print axioms RilAccess.Provenance.Examples.diverging_cleanup_stays_in_first_cleanup_call
#print axioms RilAccess.complete_sources_given_lowering

def main : IO Unit :=
  IO.println "Mathematical core certificate and imported declarations passed the transitive axiom audit."

audit_ril_access
