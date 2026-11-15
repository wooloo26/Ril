import RilAccess.Call.Proofs

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Calls.Examples

open Integrated

def fixed (access : Access) : MemberMode := ⟨false, access⟩
def slot (access : Access) : MemberMode := ⟨true, access⟩
def p (register : Nat) (fields : List Nat := []) : Path := ⟨register, fields⟩
def operations (atoms : List Atom) : Integrated.Syntax :=
  atoms.foldr (fun atom rest => .sequence (.command atom) rest) (.command .skip)
def access (atoms : List Atom) : Syntax := .access (operations atoms)
def arg (source formal : Nat) (mode : ParameterMode) : Argument := ⟨p source, formal, mode, mode⟩
def sequence (parts : List Syntax) : Syntax := parts.foldr Syntax.sequence (access [])
def accepted (program : Syntax) : Bool := (check program).isOk

/-- Evaluate provenance predicates (`formalMutated` / `formalRetained`) on a single call's frontier. -/
def inspectCall (setup : List Atom) (arguments : List Argument) (body : Syntax)
    (predicate : World → List World → Bool) : Bool :=
  match Integrated.infer (Integrated.lower (operations setup)) initialWorld with
  | .error _ => false
  | .ok [preWorld] =>
    match Integrated.infer (.sequence (.atom .enterScope) (prepare arguments)) preWorld with
    | .error _ => false
    | .ok [entry] =>
      match infer body entry with
      | .error _ => false
      | .ok frontier => predicate entry frontier
    | .ok _ => false
  | .ok _ => false

def mutate := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10)])]
def observeVariable := sequence [access [.allocate 0 (slot .mut) [], .write (p 0)],
  .invoke [arg 0 10 .observe] [] (access [.read (p 10)]),
  access [.allocate 1 (fixed .mut) [], .assign (p 1) 0, .write (p 0)]]
def readAliased := sequence [access [.allocate 0 (fixed .mut) [], .write (p 0)],
  .invoke [arg 0 10 .observe, arg 0 11 .observe] [] (access [.read (p 10), .read (p 11)])]
def disjointWriters := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 1 11 .mutable] [] (access [.pairWrite (p 10) (p 11)])]
def aliasedWriters := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 0 11 .mutable] [] (access [.pairWrite (p 10) (p 11)])]
def writeReadAlias := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 0 11 .observe] [] (access [.write (p 10), .read (p 11)])]
def ordinaryWriteCannotRetain := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.retain (p 10)])]
def retainedWriter := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] [] (access [.retain (p 10)])]
def upperBoundSharedWrite := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] [] (access [.write (p 10)])]
def retainedThroughAlias := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] []
    (access [.bind (p 10) 12 (fixed .shared), .retain (p 12)])]
def nestedMutation := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .mutable] [] (access [.write (p 20)]))]
def nestedRetention := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] []
    (.invoke [arg 10 20 .retained] [] (access [.retain (p 20)]))]
def nestedRetentionFromTemporary := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .retained] [] (access [.retain (p 20)]))]
def upperBoundMutRead := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .mutable] [] (access [.read (p 20)]))]
def possibleWrite := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.branch (access [.write (p 10)]) (access [.read (p 10)]))]
def wrongMarker := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [⟨p 0, 10, .mutable, .observe⟩] [] (access [.write (p 10)])]
def rebindFormal := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (access [.allocate 12 (fixed .mut) [], .assign (p 12) 10, .write (p 10)])]
def constructInput := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .construction] [] (access [.write (p 10)])]
def observedInputIsNotConstruction := sequence [access [.allocate 0 (fixed .mut) [],
  .bind (p 0) 1 (fixed .ref), .write (p 0)],
  .invoke [arg 1 10 .construction] [] (access [.write (p 10)])]
def formalCannotEscape := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10)]), access [.read (p 10)]]
def immutableInput := sequence [access [.allocate 0 (fixed .immutable) []],
  .invoke [arg 0 10 .immutable] [] (access [.read (p 10)])]
def mutablePlainInput := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .immutable] [] (access [.read (p 10)])]
def undeclaredCapture := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10), .write (p 1)])]
def declaredCapture := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [1] (access [.write (p 10), .write (p 1)])]
def independentCapture := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [0] (access [.write (p 10), .read (p 0)])]
def aliasedRetainedWriters := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 0 11 .retained] [] (access [.retain (p 10)])]
def selectiveSiblingRetention := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 1 11 .retained] [] (access [.retain (p 10)])]

def fixtures : List (String × Bool) :=
  [("call: mutable argument", accepted mutate),
   ("call: temporary observation pins current var target", accepted observeVariable),
   ("call: read/read aliasing", accepted readAliased),
   ("call: disjoint mutable participants", accepted disjointWriters),
   ("call: aliased writers rejected", !accepted aliasedWriters),
   ("call: write/read conflict rejected", !accepted writeReadAlias),
   ("call: ordinary mut cannot retain", !accepted ordinaryWriteCannotRetain),
   ("call: retained writer survives", accepted retainedWriter),
   ("call: upper-bound ^mut write-only call accepted while formalRetained stays false",
      accepted upperBoundSharedWrite &&
      inspectCall [.allocate 0 (fixed .mut) []] [arg 0 10 .retained] (access [.write (p 10)])
        (fun entry front => formalMutated entry front 10 && !formalRetained entry front 10)),
   ("call: local sharing inside call does not trigger outward formalRetained",
      inspectCall [.allocate 0 (fixed .mut) []] [arg 0 10 .retained]
        (access [.bind (p 10) 12 (fixed .shared), .write (p 12)])
        (fun entry front => !formalRetained entry front 10)),
   ("call: retained alias keeps formal authority origin",
      accepted retainedThroughAlias &&
      inspectCall [.allocate 0 (fixed .mut) []] [arg 0 10 .retained]
        (access [.bind (p 10) 12 (fixed .shared), .retain (p 12)])
        (fun entry front => formalRetained entry front 10)),
   ("call: nested mut forwarding", accepted nestedMutation),
   ("call: nested retained forwarding", accepted nestedRetention),
   ("call: temporary forwarding cannot retain", !accepted nestedRetentionFromTemporary),
   ("call: upper-bound mut forwarding without write accepted while formalMutated stays false",
      accepted upperBoundMutRead &&
      inspectCall [.allocate 0 (fixed .mut) []] [arg 0 10 .mutable]
        (.invoke [arg 10 20 .mutable] [] (access [.read (p 20)]))
        (fun entry front => !formalMutated entry front 10)),
   ("call: use on a retained alternative", accepted possibleWrite),
   ("call: argument markers match exactly", !accepted wrongMarker),
   ("call: formal slots are fixed", !accepted rebindFormal),
   ("call: construction input", accepted constructInput),
   ("call: observed input has no construction authority", !accepted observedInputIsNotConstruction),
   ("call: formal lifetime ends", !accepted formalCannotEscape),
   ("call: immutable input", accepted immutableInput),
   ("call: plain input cannot publish a live writer", !accepted mutablePlainInput),
   ("call: undeclared capture rejected", !accepted undeclaredCapture),
   ("call: declared independent capture", accepted declaredCapture),
   ("call: captured alias is a separate participant", !accepted independentCapture),
   ("call: aliased ^mut writers rejected at call boundary", !accepted aliasedRetainedWriters),
   ("call: upper-bound ^mut sibling formal stays unretained when only peer formal retains",
      accepted selectiveSiblingRetention &&
      inspectCall [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []]
        [arg 0 10 .retained, arg 1 11 .retained]
        (access [.retain (p 10)])
        (fun entry front => formalRetained entry front 10 && !formalRetained entry front 11)),
   ("call: overwritten publication is not surviving retention",
      inspectCall [.allocate 0 (fixed .mut) [], .bind (p 0) 1 (slot .shared), .allocate 2 (fixed .mut) []]
        [arg 2 10 .retained] (access [.assign (p 10) 1, .assign (p 0) 1])
        (fun entry front => !formalRetained entry front 10)),
   ("call: outer binding roots surviving publication",
      inspectCall [.allocate 0 (fixed .mut) [], .bind (p 0) 1 (slot .shared), .allocate 2 (fixed .mut) []]
        [arg 2 10 .retained] (access [.assign (p 10) 1])
        (fun entry front => formalRetained entry front 10))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Calls.Examples
