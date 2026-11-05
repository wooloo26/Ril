import Lean

open Lean Elab Command

/-- Declaration ownership, not namespace spelling, determines audit coverage. -/
private def projectModule (name : Name) : Bool :=
  (`RilAccess).isPrefixOf name || #[`Main, `Audit, `AuditSupport].contains name

private def projectDeclaration (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => true
  | some index => projectModule env.header.moduleNames[index.toNat]!

/-- Include private/generated declarations and the complete current probe module. -/
elab "audit_ril_access" : command => do
  let env ← getEnv
  for name in env.header.moduleNames do
    if projectModule name then logInfo m!"Audit module: {name}"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut axiomNames : Array Name := #[]
  for (name, info) in env.constants.toList do
    if projectDeclaration env name then
      declarations := declarations + 1
      if info.isUnsafe then throwError "Unsafe project declaration: {name}"
      if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
        throwError "Native implementation replacement: {name}"
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | .axiomInfo _ => throwError "Unproved project axiom: {name}; Forbidden axiom in project module"
      | _ => pure ()
      let axioms ← liftCoreM (collectAxioms name)
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Forbidden axiom {axiomName}, transitively used by {name}"
        unless axiomNames.contains axiomName do axiomNames := axiomNames.push axiomName
  if theorems = 0 then throwError "No project theorems were audited"
  logInfo m!"Audit passed: {declarations} declarations, {theorems} theorems; axiom union: {axiomNames}"
