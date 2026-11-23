import RilAccess.Effects.Results

namespace RilAccess.ResultInspection.Examples

def some (tag : String) : World :=
  ⟨[⟨[], "Some", none⟩, ⟨[0], tag, Option.some 1⟩], [1]⟩

def none (pending : List Nat := []) : World := ⟨[⟨[], "None", Option.none⟩], pending⟩

def outer : Arm := ⟨[([], "Some")], true⟩
def nested (tag : String) : Arm := ⟨[([], "Some"), ([0], tag)], true⟩
def fallback : Arm := ⟨[], true⟩
def handlers : List Arm := [nested "Ok", nested "Err", ⟨[([], "None")], true⟩]

def nestedResult : World :=
  ⟨[⟨[], "Ok", Option.some 0⟩, ⟨[0], "Ok", Option.some 1⟩], [0, 1]⟩

def cases : List (String × Bool × Bool) :=
  [("matching_only_the_outer_option_does_not_inspect_its_result",
    canExit (some "Ok") [outer, fallback], false),
   ("nested_constructor_test_inspects_a_result_on_match_and_miss",
    ["Ok", "Err"].all (fun tag => canExit (some tag) [nested "Ok", fallback]), true),
   ("a_wildcard_arm_cannot_skip_the_result_test",
    [true, false].all (fun flag => canExit (some "Ok") [{ outer with guard := flag }, nested "Ok", fallback]), false),
   ("a_missing_payload_has_no_inspection_obligation",
    [some "Ok", none []].all (canExit · handlers), true),
   ("a_missing_payload_does_not_inspect_an_existing_result",
    [some "Ok", none [1]].all (canExit · handlers), false),
   ("conditional_bindings_only_inspect_a_present_result",
    [some "Ok", none []].all (canExit · [nested "Ok", fallback]), true),
   ("matching_the_outer_result_does_not_inspect_its_payload",
    canExit nestedResult [⟨[([], "Ok")], true⟩, ⟨[([], "Err")], true⟩], false)]

def examples : List (String × Bool) :=
  cases.map fun (name, actual, expected) => (name, actual == expected)

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.ResultInspection.Examples
