import RilAccess
import RilAccess.Examples.All
import AuditSupport

#check RilAccess.CoreVerification.verified
#print axioms RilAccess.CoreVerification.verified
#print axioms RilAccess.Provenance.verified_program
#print axioms RilAccess.Provenance.verified_machine
#print axioms RilAccess.Provenance.machine_progress
#print axioms RilAccess.complete_sources_given_lowering

def main : IO Unit :=
  IO.println "Mathematical core certificate and imported declarations passed the transitive axiom audit."

audit_ril_access
