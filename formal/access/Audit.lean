import RilAccess
import AuditSupport

audit_ril_access

#check RilAccess.CoreVerification.verified
#print axioms RilAccess.CoreVerification.verified
#print axioms RilAccess.complete_sources_given_lowering

def main : IO Unit :=
  IO.println "Mathematical core certificate and imported declarations passed the transitive axiom audit."
