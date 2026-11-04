import Lean

open Lean Elab Command

/-- Audit all project declarations, including generated helpers and fixture proofs. -/
elab "audit_ril_access" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut axiomNames : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`RilAccess).isPrefixOf name then
      declarations := declarations + 1
      if info.isUnsafe then throwError "Unsafe project declaration: {name}"
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | .axiomInfo _ => throwError "Unproved project axiom: {name}"
      | _ => pure ()
      let axioms ← liftCoreM (collectAxioms name)
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Forbidden axiom {axiomName}, transitively used by {name}"
        unless axiomNames.contains axiomName do axiomNames := axiomNames.push axiomName
  if theorems = 0 then throwError "No project theorems were audited"
  logInfo m!"Audit passed: {declarations} declarations, {theorems} theorems; axiom union: {axiomNames}"
