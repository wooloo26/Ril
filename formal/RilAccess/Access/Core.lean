import RilAccess.Signatures
import RilAccess.Solver

/-! An integrated, finite, mode-erased access calculus. All authority and alias
facts below are computed from declarations and operations, not supplied flags. -/
namespace RilAccess.Integrated

structure Path where
  register : Nat
  fields : List Nat := []
  deriving Repr, DecidableEq

structure Pointer where
  object : Nat
  fields : List Nat
  source : Source
  deriving Repr, DecidableEq

def overlaps (a b : Pointer) : Bool :=
  decide (a.object = b.object) &&
    (a.fields.isPrefixOf b.fields || b.fields.isPrefixOf a.fields)

def contains (a b : Pointer) : Bool :=
  decide (a.object = b.object ∧ a.source = b.source) && a.fields.isPrefixOf b.fields

structure Field where
  coordinate : List Nat
  mode : MemberMode
  object : Bool
  deriving Repr, DecidableEq

abbrev Schema := List Field

/-- The recursion is on a finite path, even when a later model admits graph cycles. -/
def traverse (schema : Schema) (base : List Nat) (access : Access) :
    List Nat → Option (List Access × Access × Access × Bool × Bool)
  | [] => some ([], access, access, false, true)
  | field :: rest => do
    let member ← schema.find? fun member => decide (member.coordinate = base ++ [field])
    if rest.isEmpty then
      pure ([member.mode.access], attenuate access member.mode.access, access,
        member.mode.replaceable, member.object)
    else if member.object then do
      let (members, effective, parent, replaceable, object) ←
        traverse schema (base ++ [field]) (attenuate access member.mode.access) rest
      pure (member.mode.access :: members, effective, parent, replaceable, object)
    else none

structure Observation where
  kind : EventKind
  pointer : Pointer
  deriving Repr, DecidableEq

structure RawState where
  roots : List (Nat × Pointer) := []
  nextObject : Nat := 0
  observations : List Observation := []
  deriving Repr, DecidableEq

def rawLookup (s : RawState) (r : Nat) : Option Pointer :=
  (s.roots.find? fun pair => decide (pair.1 = r)).map Prod.snd

def rawPath (s : RawState) (p : Path) : Option Pointer := do
  let root ← rawLookup s p.register
  pure { root with fields := root.fields ++ p.fields }

def putRaw (s : RawState) (r : Nat) (p : Pointer) : RawState :=
  { s with roots := (r, p) :: s.roots.filter (fun pair => decide (pair.1 ≠ r)) }

inductive RawAtom where
  | allocate (destination : Nat)
  | copy (source : Path) (destination : Nat)
  | observe (kind : EventKind) (path : Path)
  | pairWrite (left right : Path)
  | skip
  deriving Repr, DecidableEq

/-- Runtime interpretation has no authority, alias, or scope checks. -/
def rawStep (a : RawAtom) (s : RawState) : Option RawState :=
  match a with
  | .allocate r =>
    let pointer := Pointer.mk s.nextObject [] ⟨.allocation, r⟩
    some { putRaw s r pointer with nextObject := s.nextObject + 1 }
  | .copy path destination => do
    let pointer ← rawPath s path
    pure (putRaw s destination pointer)
  | .observe kind path => do
    let pointer ← rawPath s path
    pure { s with observations := ⟨kind, pointer⟩ :: s.observations }
  | .pairWrite left right => do
    let l ← rawPath s left
    let r ← rawPath s right
    pure { s with observations := ⟨.write, r⟩ :: ⟨.write, l⟩ :: s.observations }
  | .skip => some s

abbrev ParameterMode := RilAccess.ParameterMode

inductive Atom where
  | allocate (destination : Nat) (mode : MemberMode) (schema : Schema)
  | allocateResource (destination : Nat) (schema : Schema)
  | allocateScoped (destination : Nat) (mutable : Bool) (schema : Schema) (resource : Bool := false)
  | bind (source : Path) (destination : Nat) (mode : MemberMode)
  | assign (source : Path) (destination : Nat)
  | read (path : Path)
  | write (path : Path)
  | replaceScalar (path : Path)
  | retain (path : Path)
  | handoff (source destination : Nat)
  | pairWrite (left right : Path)
  | enterScope
  | leaveScope
  | beginHold (source : Path) (destination : Nat)
  | parameter (source : Path) (destination : Nat) (mode : ParameterMode)
  | activateParameters
  | skip
  deriving Repr, DecidableEq

def eraseAtom : Atom → RawAtom
  | .allocate destination _ _ | .allocateResource destination _ |
      .allocateScoped destination _ _ _ => .allocate destination
  | .bind source destination _ | .assign source destination => .copy source destination
  | .read path => .observe .read path
  | .write path | .replaceScalar path => .observe .write path
  | .retain path => .observe .retain path
  | .handoff source destination => .copy ⟨source, []⟩ destination
  | .pairWrite left right => .pairWrite left right
  | .beginHold source destination | .parameter source destination _ => .copy source destination
  | .enterScope | .leaveScope | .activateParameters | .skip => .skip

structure Grant where
  object : Nat
  source : Source
  declared : Access
  schema : Schema
  resource : Bool := false
  deriving Repr, DecidableEq

structure Token where
  id : Nat
  region : Pointer
  active : Bool
  scopedHold : Bool
  qualified : Bool
  retained : Bool
  scope : Nat
  parents : List Nat
  dependencies : List Nat
  deriving Repr, DecidableEq

structure BindingAccess where
  register : Nat
  mode : MemberMode
  dependencies : List Nat
  alive : Bool
  scope : Nat
  immutableSource : Bool
  isScoped : Bool := false
  deriving Repr, DecidableEq

structure Hold where
  token : Nat
  region : Pointer
  access : Access
  scope : Nat
  active : Bool
  deriving Repr, DecidableEq

structure Frame where
  parentScope : Nat
  hold : Option Nat
  deriving Repr, DecidableEq

inductive UseKind where
  | writable | replacement | retention | sharedReception
  deriving Repr, DecidableEq

structure Use where
  register : Nat
  kind : UseKind
  deriving Repr, DecidableEq

structure Requirement where
  register : Nat
  mode : MemberMode
  deriving Repr, DecidableEq

/-- Authority ancestry is distinct from scope dependencies. An independently
retained writer can persist beyond its parent scope while preserving its checked provenance. -/
def tokenAncestors (tokens : List Token) (id : Nat) : List Nat :=
  solve (Rule.mk [] id :: tokens.flatMap fun token =>
    token.parents.map fun parent => Rule.mk [token.id] parent)

structure Resolved where
  pointer : Pointer
  binding : BindingAccess
  grant : Grant
  members : List Access
  effective : Access
  parentAccess : Access
  replaceable : Bool
  object : Bool
  tokens : List Token
  authorityAncestors : List Nat
  deriving Repr, DecidableEq

def live (r : Resolved) : Bool :=
  r.binding.alive && !r.binding.dependencies.isEmpty &&
    decide (r.tokens.length = r.binding.dependencies.length) &&
    r.tokens.all (fun token => token.active && contains token.region r.pointer) &&
    decide (r.grant.object = r.pointer.object ∧ r.grant.source = r.pointer.source)

/-- Independent shared participants can alias. Passing a shared participant as a nested call-scoped mut argument
participant keeps this compatibility with the shared holds of its outer call. -/
def compatibleSharedHold (r : Resolved) (holds : List Hold) (hold : Hold) : Bool :=
  decide (hold.access = .shared) && (decide (r.effective = .shared) ||
    holds.any fun ancestor => ancestor.active && decide (ancestor.access = .shared ∧
      hold.scope ≤ ancestor.scope ∧ ancestor.token ∈ r.authorityAncestors))

def noHoldConflict (r : Resolved) (holds : List Hold) (writing : Bool := true) : Bool :=
  holds.all fun hold => !hold.active || !overlaps hold.region r.pointer ||
    decide (hold.token ∈ r.authorityAncestors) ||
    compatibleSharedHold r holds hold ||
    (!writing && (!hold.access.writes || r.binding.immutableSource || decide (r.effective = .immutable)))

def noScopedHold (r : Resolved) : Bool := r.tokens.all (fun token => !token.scopedHold)

def deepImmutable (r : Resolved) : Bool :=
  r.binding.immutableSource || decide (r.effective = .immutable)

inductive ObservationRule where
  | read | write | replaceScalar | retain
  deriving Repr, DecidableEq

structure AccessCheck where
  observation : Observation
  rule : ObservationRule
  resolved : Resolved
  holds : List Hold
  peers : List Pointer
  deriving Repr, DecidableEq

/-- A declarative, decidable policy on a concrete binding-access snapshot. -/
def authorizedLocal (e : AccessCheck) : Bool :=
  let r := e.resolved
  decide (e.observation.pointer = r.pointer) && live r &&
    noHoldConflict r e.holds (decide (e.rule ≠ .read)) &&
    e.peers.all (fun peer => !overlaps peer r.pointer) &&
    decide (r.effective = pathAccess r.binding.mode.access r.members) &&
    match e.rule with
    | .read => decide (e.observation.kind = .read)
    | .write => decide (e.observation.kind = .write) && r.object &&
        r.effective.writes && r.grant.declared.writes
    | .replaceScalar => decide (e.observation.kind = .write) && !r.object &&
        r.replaceable && r.parentAccess.writes && r.grant.declared.writes
    | .retain => decide (e.observation.kind = .retain) && r.object &&
        !r.grant.resource && !r.binding.isScoped &&
        r.effective.writes && r.grant.declared.writes && noScopedHold r

/-- Recheck the complete physical path against its original allocation schema.
Alias-local metadata alone cannot certify a writable originally-immutable member. -/
def originalPolicy (e : AccessCheck) : Bool :=
  match traverse e.resolved.grant.schema [] e.resolved.grant.declared e.observation.pointer.fields with
  | none => false
  | some (_, effective, parent, replaceable, object) =>
    match e.rule with
    | .read => true
    | .write | .retain => object && effective.writes
    | .replaceScalar => !object && replaceable && parent.writes

def authorized (e : AccessCheck) : Bool := authorizedLocal e && originalPolicy e

structure World where
  raw : RawState := {}
  bindings : List BindingAccess := []
  grants : List Grant := []
  tokens : List Token := []
  nextToken : Nat := 0
  scope : Nat := 0
  frames : List Frame := []
  holds : List Hold := []
  requirements : List Requirement := []
  uses : List Use := []
  accessChecks : List AccessCheck := []
  deriving Repr, DecidableEq

def lookupBinding (w : World) (r : Nat) : Option BindingAccess :=
  w.bindings.find? fun binding => decide (binding.register = r)

def putBinding (w : World) (p : BindingAccess) : World :=
  { w with bindings := p :: w.bindings.filter (fun old => decide (old.register ≠ p.register)) }

def lookupToken (w : World) (id : Nat) : Option Token :=
  w.tokens.find? fun token => decide (token.id = id)

/-- Unknown dependencies do not establish expiry. An explicitly ended dependency
does establish that this derived path can no longer act. -/
def bindingEnded (w : World) (binding : BindingAccess) : Bool :=
  !binding.alive || binding.dependencies.any fun id =>
    match lookupToken w id with
    | some token => !token.active
    | none => false

def resolve (w : World) (path : Path) : Option Resolved := do
  let binding ← lookupBinding w path.register
  let root ← rawLookup w.raw path.register
  let grant ← w.grants.find? fun grant => decide (grant.object = root.object)
  let (members, effective, parent, replaceable, object) ←
    traverse grant.schema root.fields binding.mode.access path.fields
  let pointer := { root with fields := root.fields ++ path.fields }
  let tokens := binding.dependencies.filterMap (lookupToken w)
  let ancestors := binding.dependencies.flatMap (tokenAncestors w.tokens)
  pure ⟨pointer, binding, grant, members, effective, parent, replaceable, object, tokens, ancestors⟩

def snapshot (w : World) (path : Path) (kind : EventKind) (rule : ObservationRule)
    (peers : List Pointer := []) : Option AccessCheck := do
  let r ← resolve w path
  pure ⟨⟨kind, r.pointer⟩, rule, r, w.holds, peers⟩

def certified (w : World) : Bool :=
  decide (w.raw.observations = w.accessChecks.map AccessCheck.observation) && w.accessChecks.all authorized &&
    w.accessChecks.all (fun e => decide (e.resolved.grant ∈ w.grants))

def initialWorld : World := {}

def unused (w : World) (r : Nat) : Bool := (lookupBinding w r).isNone

def markUse (w : World) (r : Nat) (kind : UseKind) : World :=
  { w with uses := ⟨r, kind⟩ :: w.uses }

def addRequirement (w : World) (r : Nat) (mode : MemberMode) : World :=
  { w with requirements := ⟨r, mode⟩ :: w.requirements }

def invalidateQualification (w : World) (pointer : Pointer) : World :=
  { w with tokens := w.tokens.map fun token =>
      if overlaps token.region pointer then { token with qualified := false } else token }

def endTokens (w : World) (ids : List Nat) : World :=
  { w with tokens := w.tokens.map fun token =>
      if token.id ∈ ids then { token with active := false, qualified := false } else token }

def addToken (w : World) (region : Pointer) (scopedHold qualified retained : Bool)
    (scope : Nat) (parents : List Nat := []) : World :=
  { w with
    tokens := ⟨w.nextToken, region, true, scopedHold, qualified, retained, scope, parents,
      if scopedHold then parents else []⟩ :: w.tokens,
    nextToken := w.nextToken + 1 }

def install (w : World) (register : Nat) (mode : MemberMode) (dependencies : List Nat)
    (scope : Nat) (immutableSource : Bool) (isScoped : Bool := false) : World :=
  addRequirement (putBinding w ⟨register, mode, dependencies, true, scope, immutableSource, isScoped⟩)
    register mode

def eligibleHandoff (w : World) (r : Resolved) : Bool :=
  live r && !r.binding.isScoped && noHoldConflict r w.holds && r.object && r.effective.writes &&
    r.grant.declared.writes && !r.binding.mode.replaceable &&
    decide (r.binding.dependencies.length = 1) &&
    r.tokens.all (fun token => token.qualified && !token.scopedHold && !token.retained &&
      decide (token.region = r.pointer)) &&
    w.bindings.all (fun binding =>
      bindingEnded w binding ||
      match rawLookup w.raw binding.register with
      | none => false
      | some pointer => !overlaps pointer r.pointer ||
          binding.dependencies.all (fun id => decide (id ∈ r.binding.dependencies))) &&
    w.tokens.all (fun token => !token.retained || !overlaps token.region r.pointer)

def receiving (w : World) (r : Resolved) (mode : MemberMode) (scope : Nat) : Bool :=
  live r && !r.binding.isScoped && noHoldConflict r w.holds mode.access.writes && r.object &&
  match mode.access with
  | .immutable => !r.grant.resource && deepImmutable r
  | .ref => !r.binding.mode.replaceable &&
      r.tokens.all (fun token => decide (token.scope ≤ scope) || token.retained)
  | .mut => false
  | .shared => !r.grant.resource && r.effective.writes && r.grant.declared.writes && noScopedHold r

def checkSchema (schema : Schema) : Bool :=
  decide ((schema.map Field.coordinate).Nodup) &&
    schema.all (fun field => !field.coordinate.isEmpty &&
      (field.object || decide (field.mode.access = .immutable)) &&
      (traverse schema [] .mut field.coordinate).isSome)

def closeScope (w : World) (frame : Frame) : World :=
  { w with
    scope := frame.parentScope, frames := w.frames.drop 1,
    bindings := w.bindings.map fun p =>
      if p.scope > frame.parentScope then { p with alive := false } else p,
    tokens := w.tokens.map fun token =>
      if token.scope > frame.parentScope && !token.retained then
        { token with active := false, qualified := false } else token,
    holds := w.holds.filter (fun hold =>
      match lookupToken w hold.token with
      | some token => decide (token.scope ≤ frame.parentScope)
      | none => true) }

/-- Metadata transfer is separate from erased execution. No user-supplied alias,
escape, qualification, or liveness assertion occurs in Atom. -/
def transfer (w : World) (atom : Atom) : Option World := do
  let raw ← rawStep (eraseAtom atom) w.raw
  match atom with
  | .allocate destination mode schema =>
    if unused w destination && checkSchema schema &&
        (decide (mode.access = .immutable) || decide (mode.access = .mut) ||
          (mode.replaceable && decide (mode.access = .shared))) then
      let pointer := Pointer.mk w.raw.nextObject [] ⟨.allocation, destination⟩
      let grant := Grant.mk pointer.object pointer.source mode.access schema false
      let next := addToken w pointer false
        (decide (mode.access = .mut) && !mode.replaceable) false w.scope
      pure (install { next with raw, grants := grant :: w.grants } destination mode
        [w.nextToken] w.scope (decide (mode.access = .immutable)))
    else none
  | .allocateResource destination schema =>
    if unused w destination && checkSchema schema then
      let pointer := Pointer.mk w.raw.nextObject [] ⟨.allocation, destination⟩
      let grant := Grant.mk pointer.object pointer.source .mut schema true
      let next := addToken w pointer false true false w.scope
      pure (install { next with raw, grants := grant :: w.grants } destination ⟨false, .mut⟩
        [w.nextToken] w.scope false)
    else none
  | .allocateScoped destination mutable schema resource =>
    if unused w destination && checkSchema schema then
      let access : Access := if mutable then .mut else .ref
      let pointer := Pointer.mk w.raw.nextObject [] ⟨.allocation, destination⟩
      let grant := Grant.mk pointer.object pointer.source .mut schema resource
      let next := addToken w pointer false false false w.scope
      let base := { next with raw, grants := grant :: w.grants }
      pure (install base destination ⟨false, access⟩
        [w.nextToken] w.scope false true)
    else none
  | .bind source destination mode =>
    let r ← resolve w source
    if unused w destination && receiving w r mode w.scope then
      if mode.access = .shared then
        let next := addToken (invalidateQualification w r.pointer) r.pointer false false false w.scope
          r.binding.dependencies
        pure (install (markUse (markUse { next with raw } source.register .writable)
          destination .sharedReception) destination mode
          [w.nextToken] w.scope false)
      else
        pure (install { w with raw } destination mode r.binding.dependencies w.scope
          (deepImmutable r))
    else none
  | .assign source destination =>
    let target ← lookupBinding w destination
    let targetPath ← resolve w ⟨destination, []⟩
    let r ← resolve w source
    if target.alive && !target.isScoped && target.mode.replaceable && live targetPath && noHoldConflict targetPath w.holds then
      if target.mode.access = .mut then
        if !r.grant.resource && eligibleHandoff w r then
          let next := addToken (endTokens w r.binding.dependencies) r.pointer false false false target.scope
            r.binding.dependencies
          pure (install (markUse (markUse { next with raw } destination .replacement)
            source.register .writable) destination target.mode [w.nextToken] target.scope false)
        else none
      else if receiving w r target.mode target.scope then
        if target.mode.access = .shared then
          let next := addToken (invalidateQualification w r.pointer) r.pointer false false false target.scope
            r.binding.dependencies
          pure (install (markUse (markUse (markUse { next with raw } destination .replacement)
            source.register .writable) destination .sharedReception)
            destination target.mode [w.nextToken] target.scope false)
        else
          pure (install (markUse { w with raw } destination .replacement) destination target.mode
            r.binding.dependencies target.scope (deepImmutable r))
      else none
    else none
  | .read path | .write path | .replaceScalar path | .retain path =>
    let kind := match atom with | .read _ => EventKind.read | .retain _ => .retain | _ => .write
    let rule := match atom with
      | .read _ => ObservationRule.read
      | .retain _ => .retain
      | .replaceScalar _ => .replaceScalar
      | _ => .write
    let accessCheck ← snapshot w path kind rule
    if authorized accessCheck then
      let next := { w with raw, accessChecks := accessCheck :: w.accessChecks }
      match atom with
      | .read _ => pure next
      | .retain _ =>
        let next := addToken (invalidateQualification next accessCheck.resolved.pointer)
          accessCheck.resolved.pointer false false true 0 accessCheck.resolved.binding.dependencies
        pure (markUse (markUse next path.register .writable) path.register .retention)
      | _ => pure (markUse next path.register .writable)
    else none
  | .handoff source destination =>
    let r ← resolve w ⟨source, []⟩
    if unused w destination && eligibleHandoff w r then
      let next := addToken (endTokens w r.binding.dependencies) r.pointer false true false w.scope
        r.binding.dependencies
      pure (install (markUse { next with raw } source .writable) destination ⟨false, .mut⟩
        [w.nextToken] w.scope false)
    else none
  | .pairWrite left right =>
    let l ← resolve w left
    let r ← resolve w right
    let le ← snapshot w left .write .write [r.pointer]
    let re ← snapshot w right .write .write [l.pointer]
    if authorized le && authorized re then
      pure (markUse (markUse { w with raw, accessChecks := re :: le :: w.accessChecks }
        left.register .writable) right.register .writable)
    else none
  | .enterScope =>
    pure { w with raw, scope := w.scope + 1, frames := ⟨w.scope, none⟩ :: w.frames }
  | .leaveScope =>
    let frame ← w.frames.head?
    pure { closeScope w frame with raw }
  | .beginHold source destination =>
    let r ← resolve w source
    if unused w destination && live r && noHoldConflict r w.holds && r.object &&
        r.effective.writes && r.grant.declared.writes then
      let scope := w.scope + 1
      let next := addToken w r.pointer true false false scope r.binding.dependencies
      let next := { next with
        raw, scope, frames := ⟨w.scope, some w.nextToken⟩ :: w.frames,
        holds := ⟨w.nextToken, r.pointer, .mut, scope, true⟩ :: w.holds }
      pure (install (markUse next source.register .writable) destination ⟨false, .mut⟩
        (w.nextToken :: r.binding.dependencies) scope false)
    else none
  | .parameter source destination mode =>
    let r ← resolve w source
    let writing := match mode with | .immutable | .observe => false | _ => true
    if unused w destination && live r && noHoldConflict r w.holds writing && r.object then
      match mode with
      | .immutable =>
        if !r.grant.resource && !r.binding.isScoped && deepImmutable r then
          let next := addToken w r.pointer false false false w.scope r.binding.dependencies
          pure (putBinding { next with raw }
            ⟨destination, ⟨false, .immutable⟩, [w.nextToken], true, w.scope, true, false⟩)
        else none
      | .observe =>
        let next := addToken w r.pointer true false false w.scope r.binding.dependencies
        pure (putBinding { next with
          raw,
          holds := ⟨w.nextToken, r.pointer, .ref, w.scope, false⟩ :: w.holds }
          ⟨destination, ⟨false, .ref⟩, w.nextToken :: r.binding.dependencies,
            true, w.scope, deepImmutable r, false⟩)
      | .mutable =>
        if r.effective.writes && r.grant.declared.writes then
          let next := addToken w r.pointer true false false w.scope r.binding.dependencies
          pure (putBinding (markUse { next with
            raw,
            holds := ⟨w.nextToken, r.pointer, .mut, w.scope, false⟩ :: w.holds } source.register .writable)
            ⟨destination, ⟨false, .mut⟩, w.nextToken :: r.binding.dependencies, true, w.scope, false, false⟩)
        else none
      | .retained =>
        if !r.grant.resource && !r.binding.isScoped && r.effective.writes && r.grant.declared.writes && noScopedHold r then
          let next := addToken (invalidateQualification w r.pointer) r.pointer false false false w.scope
            r.binding.dependencies
          pure (putBinding (markUse { next with
            raw,
            holds := ⟨w.nextToken, r.pointer, .shared, w.scope, false⟩ :: w.holds } source.register .writable)
            ⟨destination, ⟨false, .shared⟩, [w.nextToken], true, w.scope, false, false⟩)
        else none
      | .construction =>
        if eligibleHandoff w r then
          let next := addToken (endTokens w r.binding.dependencies) r.pointer false true false w.scope
            r.binding.dependencies
          pure (putBinding (markUse { next with raw } source.register .writable)
            ⟨destination, ⟨false, .mut⟩, [w.nextToken], true, w.scope, false, false⟩)
        else none
    else none
  | .activateParameters =>
    pure { w with raw, holds := w.holds.map fun hold =>
      match lookupToken w hold.token with
      | some token => if token.scope = w.scope then { hold with active := true } else hold
      | none => hold }
  | .skip => pure { w with raw }

inductive Error where
  | rejected (atom : Atom)
  | invalidCertificate
  | absentUse (requirement : Requirement)
  | unclosedScope
  | invalidSource
  deriving Repr, DecidableEq

def expectedGrants (w : World) : Atom → List Grant
  | .allocate destination mode schema =>
    ⟨w.raw.nextObject, ⟨.allocation, destination⟩, mode.access, schema, false⟩ :: w.grants
  | .allocateResource destination schema =>
    ⟨w.raw.nextObject, ⟨.allocation, destination⟩, .mut, schema, true⟩ :: w.grants
  | .allocateScoped destination _ schema resource =>
    ⟨w.raw.nextObject, ⟨.allocation, destination⟩, .mut, schema, resource⟩ :: w.grants
  | _ => w.grants

/-- Representation checks only: history snapshots need not remain live. -/
def ledgerValid (w : World) : Bool :=
  decide ((w.tokens.map Token.id).Nodup) &&
  w.tokens.all (fun token =>
    (decide (token.id < w.nextToken) && !(token.scopedHold && token.retained)) &&
    token.dependencies.all (fun id => decide (id < token.id) && (lookupToken w id).isSome)) &&
  w.bindings.all (fun binding => binding.dependencies.all (fun id =>
    (lookupToken w id).any (fun token => token.dependencies.all (fun parent => decide (parent ∈ binding.dependencies))))) &&
  w.holds.all (fun hold => (lookupToken w hold.token).any (fun token => decide (hold.scope = token.scope)))

def checkAtom (atom : Atom) (w : World) : Except Error World :=
  match transfer w atom with
  | none => .error (.rejected atom)
  | some next =>
    if certified next && decide (rawStep (eraseAtom atom) w.raw = some next.raw) &&
        decide (next.grants = expectedGrants w atom) && (ledgerValid w && ledgerValid next) then
      .ok next else .error .invalidCertificate

inductive Code where
  | atom (operation : Atom)
  | sequence (first second : Code)
  | choice (left right : Code)
  deriving Repr, DecidableEq

inductive Erased where
  | atom (operation : RawAtom)
  | sequence (first second : Erased)
  | choice (left right : Erased)
  deriving Repr, DecidableEq

def erase : Code → Erased
  | .atom operation => .atom (eraseAtom operation)
  | .sequence first second => .sequence (erase first) (erase second)
  | .choice left right => .choice (erase left) (erase right)

def atomDeclarations : Atom → List (Source × Access × Schema)
  | .allocate destination mode schema => [(⟨.allocation, destination⟩, mode.access, schema)]
  | .allocateResource destination schema => [(⟨.allocation, destination⟩, .mut, schema)]
  | .allocateScoped destination _ schema _ =>
    [(⟨.allocation, destination⟩, .mut, schema)]
  | _ => []

def declarations : Code → List (Source × Access × Schema)
  | .atom operation => atomDeclarations operation
  | .sequence first second | .choice first second => declarations first ++ declarations second

def binders : Code → List Nat
  | .atom (.allocate destination _ _) | .atom (.allocateResource destination _) |
      .atom (.allocateScoped destination _ _ _) | .atom (.bind _ destination _) |
      .atom (.handoff _ destination) | .atom (.beginHold _ destination) |
      .atom (.parameter _ destination _) => [destination]
  | .atom _ => []
  | .sequence first second | .choice first second => binders first ++ binders second

def execute : Erased → RawState → List RawState
  | .atom operation, state => (rawStep operation state).toList
  | .sequence first second, state => (execute first state).flatMap (execute second)
  | .choice left right, state => execute left state ++ execute right state

def checkMany (check : World → Except Error (List World)) : List World → Except Error (List World)
  | [] => .ok []
  | first :: rest => do
    let front ← check first
    let tail ← checkMany check rest
    pure (front ++ tail)

def infer : Code → World → Except Error (List World)
  | .atom operation, state => do
    let next ← checkAtom operation state
    pure [next]
  | .sequence first second, state => do
    let front ← infer first state
    checkMany (infer second) front
  | .choice left right, state => do
    let l ← infer left state
    let r ← infer right state
    pure (l ++ r)

inductive Syntax where
  | command (operation : Atom)
  | sequence (first second : Syntax)
  | branch (left right : Syntax)
  | block (body : Syntax)
  | scopedStep (source : Path) (destination : Nat) (body : Syntax)
  deriving Repr, DecidableEq

def lower : Syntax → Code
  | .command operation => .atom operation
  | .sequence first second => .sequence (lower first) (lower second)
  | .branch left right => .choice (lower left) (lower right)
  | .block body => .sequence (.atom .enterScope) (.sequence (lower body) (.atom .leaveScope))
  | .scopedStep source destination body =>
    .sequence (.atom (.beginHold source destination)) (.sequence (lower body) (.atom .leaveScope))

/-- Source execution independently erases modes and lexical authority bookkeeping. -/
def sourceExecute : Syntax → RawState → List RawState
  | .command operation, state => (rawStep (eraseAtom operation) state).toList
  | .sequence first second, state => (sourceExecute first state).flatMap (sourceExecute second)
  | .branch left right, state => sourceExecute left state ++ sourceExecute right state
  | .block body, state => sourceExecute body state
  | .scopedStep source destination body, state =>
    (rawStep (.copy source destination) state).toList.flatMap (sourceExecute body)

def surfaceValid : Syntax → Bool
  | .command .enterScope | .command .leaveScope | .command (.beginHold _ _) |
      .command (.parameter _ _ _) | .command .activateParameters => false
  | .command _ => true
  | .sequence first second | .branch first second => surfaceValid first && surfaceValid second
  | .block body | .scopedStep _ _ body => surfaceValid body

def allUses (worlds : List World) : List Use := worlds.flatMap World.uses

def satisfiesUse (uses : List Use) (requirement : Requirement) : Bool :=
  (!requirement.mode.replaceable || decide (Use.mk requirement.register .replacement ∈ uses)) &&
    (!requirement.mode.access.writes || decide (Use.mk requirement.register .writable ∈ uses)) &&
    (decide (requirement.mode.access ≠ .shared) ||
      decide (Use.mk requirement.register .sharedReception ∈ uses))

structure Analysis where
  worlds : List World
  srcInsts : List Source
  deriving Repr, DecidableEq

def worldInstances (world : World) : List Source :=
  (world.raw.observations.map (fun observation => observation.pointer.source) ++
    world.raw.roots.map (fun root => root.2.source)) ++ world.grants.map Grant.source

def check (program : Syntax) : Except Error Analysis :=
  if !surfaceValid program || !decide (binders (lower program)).Nodup then
    .error .invalidSource else do
  let worlds ← infer (lower program) initialWorld
  if worlds.any (fun world => !world.frames.isEmpty) then .error .unclosedScope
  else
    let requirements := worlds.flatMap World.requirements
    match requirements.find? (fun requirement => !satisfiesUse (allUses worlds) requirement) with
    | some requirement => .error (.absentUse requirement)
    | none => .ok ⟨worlds, worlds.flatMap worldInstances⟩

end RilAccess.Integrated
