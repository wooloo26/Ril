import RilAccess.Effects.Resumption

namespace RilAccess.CoreResumption.Examples

def origin : Origin := ⟨⟨.module, 1⟩, 0, 1, 0, 0⟩
def start : State :=
  ⟨[⟨7, ⟨1, 2, 0⟩, [10]⟩, ⟨8, ⟨1, 2, 0⟩, [30]⟩], ⟨1, 2, 0⟩, [10, 20, 30],
    [⟨.write, origin, .handler⟩], []⟩
def afterFirst := (resume start 7).getD start
def afterOther := (resume afterFirst 8).getD start

def fixtures : List (String × Bool) :=
  [("core resume: first use accepted", (resume start 7).isSome),
   ("core resume: alias to consumed identity rejected", (resume afterFirst 7).isNone),
   ("core resume: another operation has independent affine identity", (resume afterFirst 8).isSome),
   ("core resume: intervening operation cannot revive old alias", (resume afterOther 7).isNone),
   ("core resume: operation temporary authority ends", decide (10 ∉ afterFirst.activeAuthority)),
   ("core resume: independent retained authority survives", decide (20 ∈ afterOther.activeAuthority)),
   ("core resume: previously committed write survives", decide (afterOther.committed = start.committed)),
   ("core resume: other arm cannot use escaped handle", (resume { start with current := ⟨9, 2, 0⟩ } 7).isNone),
   ("core resume: callable boundary rejects escaped handle", (resume { start with current := ⟨1, 9, 0⟩ } 7).isNone),
   ("core resume: task boundary rejects escaped handle", (resume { start with current := ⟨1, 2, 9⟩ } 7).isNone),
   ("core resume: unavailable identity rejected", (resume start 99).isNone)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreResumption.Examples
