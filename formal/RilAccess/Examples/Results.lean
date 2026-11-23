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

def fallibleExit (tag : String) : World :=
  ⟨[⟨[], tag, Option.some 0⟩], [0, 1]⟩

def errorWithResult : World :=
  ⟨[⟨[], "Err", Option.some 0⟩, ⟨[0], "Ok", Option.some 1⟩], [0, 1]⟩

def pair (second : Nat) : World :=
  receive [⟨[0], "Ok", Option.some 1⟩, ⟨[1], "Ok", Option.some second⟩]

def recordOption (tag : String) : World :=
  receive <| if tag == "None" then [⟨[0], "None", Option.none⟩] else
    [⟨[0], "Some", Option.none⟩, ⟨[0, 0], tag, Option.some 1⟩]

def array (size : Nat) : World :=
  receive ((List.range size).map fun index =>
    ⟨[index], if index % 2 == 0 then "Ok" else "Err", Option.some index⟩)

def twoArrays : World :=
  receive [⟨[0, 0], "Ok", Option.some 0⟩, ⟨[1, 0], "Err", Option.some 1⟩]

def overwrittenElement : World :=
  { (array 2) with
    constructors := [⟨[0], "Ok", Option.some 2⟩, ⟨[1], "Err", Option.some 1⟩]
    pending := [0, 1, 2] }

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
    canExit nestedResult [⟨[([], "Ok")], true⟩, ⟨[([], "Err")], true⟩], false),
   ("propagation_checks_pending_results_on_early_return",
    ["Ok", "Err"].all (canPropagate ∘ fallibleExit), false),
   ("a_propagating_pipeline_checks_pending_results_on_early_return",
    ["Ok", "Err"].all (canPropagate ∘ fallibleExit), false),
   ("successful_propagation_can_leave_an_existing_result_to_the_continuation",
    canPropagate (fallibleExit "Ok"), true),
   ("optional_propagation_checks_only_results_present_on_its_exit_path",
    [some "Ok", none []].all canPropagate, true),
   ("error_propagation_transfers_the_nested_error_result", canPropagate errorWithResult, true),
   ("returned_option_keeps_its_nested_result_obligation",
    [some "Ok", none []].all (canExit · [outer, fallback]), false),
   ("returned_nominal_field_keeps_its_result_obligation",
    canExit (receive [⟨[0], "Ok", Option.some 1⟩]) [fallback], false),
   ("specialized_nominal_layout_exposes_the_result_to_inner",
    canExit (receive [⟨[0], "Ok", Option.some 1⟩, ⟨[1, 0], "Ok", Option.some 2⟩])
      [⟨[([0], "Ok"), ([1, 0], "Ok")], true⟩], true),
   ("returned_option_can_be_inspected_in_both_variants",
    [some "Ok", some "Err", none []].all (canExit · handlers), true),
   ("returned_fields_can_contain_discriminated_results",
    ["Ok", "Err", "None"].all (fun tag => canExit (recordOption tag)
      [⟨[([0], "Some"), ([0, 0], "Ok")], true⟩,
       ⟨[([0], "Some"), ([0, 0], "Err")], true⟩, ⟨[([0], "None")], true⟩]), true),
   ("returned_array_keeps_each_result_obligation",
    canExitAfterTraversal (pair 2) [], false),
   ("exhaustive_array_iteration_inspects_all_returned_results",
    canExitAfterTraversal (pair 2) [0, 1], true),
   ("breaking_array_iteration_leaves_a_later_result_pending",
    canExitAfterTraversal (pair 2) [0], false),
   ("an_unknown_array_index_cannot_inspect_both_results",
    [0, 1].all (fun index => canExitAfterTraversal (pair 2) [index]), false),
   ("empty_returned_array_has_no_element_result_obligation",
    canExitAfterTraversal (receive []) [], true),
   ("variable_length_array_keeps_its_element_result_obligation",
    [0, 2].all (fun size => canExitAfterTraversal (array size) []), false),
   ("variable_length_array_can_be_inspected_by_exhaustive_iteration",
    [0, 2].all (fun size => canExitAfterTraversal (array size) (List.range size)), true),
   ("a_break_cannot_inspect_the_rest_of_a_variable_length_array",
    canExitAfterTraversal (array 2) [0], false),
   ("continuing_before_inspection_leaves_a_variable_array_pending",
    canExitAfterTraversal (array 2) [1], false),
   ("continuing_after_inspection_preserves_array_coverage",
    canExitAfterTraversal (array 2) [0, 1], true),
   ("returning_from_array_iteration_requires_the_unvisited_results",
    canExitAfterCoverage (array 2) [[0]] [], false),
   ("returning_the_array_transfers_its_unvisited_results",
    canExitAfterCoverage (array 2) [] [[]], true),
   ("nested_variable_arrays_can_be_inspected_by_nested_traversals",
    canExitAfterCoverage twoArrays [[0, 0], [1, 0]] [], true),
   ("traversing_one_selected_array_does_not_inspect_the_other_array",
    [0, 1].all (fun selected => canExitAfterCoverage twoArrays [[selected, 0]] []), false),
   ("returning_one_selected_array_does_not_transfer_the_other_array",
    [0, 1].all (fun selected => canExitAfterCoverage twoArrays [] [[selected]]), false),
   ("wrapping_one_selected_array_still_leaves_the_other_array_pending",
    [0, 1].all (fun selected => canExitAfterCoverage twoArrays [] [[selected]]), false),
   ("returning_both_arrays_in_either_order_transfers_both_obligations",
    [[[0], [1]], [[1], [0]]].all (canExitAfterCoverage twoArrays []), true),
   ("traversing_a_possible_empty_alternative_keeps_the_array_pending",
    [[], [0, 1]].all (canExitAfterTraversal (array 2)), false),
   ("every_created_array_is_inspected_on_its_own_path",
    [0, 2].all (fun size => canExitAfterTraversal (array size) (List.range size)), true),
   ("replacing_an_uninspected_array_element_cannot_be_hidden_by_iteration",
    canExitAfterTraversal overwrittenElement [0, 1], false),
   ("independent_results_in_returned_fields_require_separate_inspection",
    canExit (pair 2) [⟨[([0], "Ok")], true⟩], false),
   ("returned_fields_can_share_one_result_obligation",
    canExit (pair 1) [⟨[([0], "Ok")], true⟩], true),
   ("explicit_result_input_keeps_its_nested_result_obligation",
    canExit (receive nestedResult.constructors) [⟨[([], "Ok")], true⟩, fallback], false),
   ("returning_a_previously_inspected_result_creates_a_caller_obligation",
    let caller := receive [⟨[], "Ok", Option.some 0⟩]
    canExit caller [fallback], false)]

def examples : List (String × Bool) :=
  cases.map fun (name, actual, expected) => (name, actual == expected)

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.ResultInspection.Examples
