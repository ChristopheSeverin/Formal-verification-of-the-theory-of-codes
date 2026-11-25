module

meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command
meta import ThreeWordCodes.Example
meta import ThreeWordCodes.Tree
meta import Mathlib.Data.Fintype.Defs
meta import Mathlib.Data.Finset.Sort
meta import Mathlib.Data.String.Basic
import ThreeWordCodes
import Mathlib.Data.Finset.Sort
import Mathlib.Data.String.Basic

open ThreeWordCodes
open ThreeWordCodes.BinaryExample

-- Print the main statements and the axioms used by the proved theorems.
#check @three_word_positive_completion
#print ThreeWordTheorem
#print BinaryThreeWordTheorem
#check @binary_suffices
#check @certificate_completion
#check @tree_extension_certificate
#check @BinaryGaps.uniform_gaps_of_ambiguity
#check @border_and_crossed_suffice
#check @BinaryGaps.pure_power_iff_one_marker
#check @BinaryGaps.terminal_gaps_of_words
#check @BinaryGaps.binary_letter_normal_form
#check @three_word_pure_power_completion
#check @BinaryGaps.pure_power_completion
#print axioms ThreeWordCodes.three_word_pure_power_completion
#check @BinaryGaps.pure_power_iff_repeated_interior
#check @BinaryGaps.unique_minimum_completion
#check @BinaryGaps.equal_minimum_blocks_completion
#check @Palindromic.alternating_third_completion
#check @Palindromic.final_a_completion
#check @Palindromic.residual_word
#check @crossed_obstruction_conditions
#check @Palindromic.palindromic_completion
#print axioms ThreeWordCodes.Palindromic.proposition_seven
#print axioms ThreeWordCodes.Border.forbidden_identity
#check @Border.all_cuts_ambiguous
#print axioms ThreeWordCodes.Border.border_completion
#check @four_crossed_rows_suffice
#print axioms ThreeWordCodes.CrossedCase.disjoint_impossible
#check @CrossedCase.three_crossed_rows_suffice
#print axioms ThreeWordCodes.CrossedCase.shared_impossible
#print axioms ThreeWordCodes.CrossedCase.overlap_suffices
#print axioms ThreeWordCodes.CrossedCase.overlap_impossible
#print axioms ThreeWordCodes.three_word_theorem
#print axioms ThreeWordCodes.three_word_positive_completion
#check @Palindromic.proposition_seven_iff_common_gaps
#check @Palindromic.single_code_iff
#check @Palindromic.graft_completion
#check @Palindromic.two_proper_readings
#check @BinaryGaps.pure_power_iff_interior_minimum
#check @border_and_four_rows_suffice
#check @both_crossed_shortenings_ambiguous
#check @BinaryGaps.initial_short_gap_completion
#check @BinaryGaps.single_marker_lengthening
#check @finite_prefix_positive_completion
#print axioms ThreeWordCodes.finite_prefix_positive_completion
#print axioms ThreeWordCodes.BinaryExample.binary_completion

-- Fail if any audited theorem uses a nonstandard axiom.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``ThreeWordCodes.prefix_completion_explicit,
      ``ThreeWordCodes.finite_prefix_positive_completion,
      ``ThreeWordCodes.BinaryExample.binary_completion,
      ``ThreeWordCodes.WordSeries.certificate_series,
      ``ThreeWordCodes.certificate_coefficients,
      ``ThreeWordCodes.certificate_completion,
      ``ThreeWordCodes.maximal_of_finite_flanks,
      ``ThreeWordCodes.HasPositiveCompletion.reverse,
      ``ThreeWordCodes.suffix_case,
      ``ThreeWordCodes.ParsingModel.compose,
      ``ThreeWordCodes.PositiveFactorization.liftLetters,
      ``ThreeWordCodes.completion_substitution,
      ``ThreeWordCodes.Completable.padLeft,
      ``ThreeWordCodes.Completable.padRight,
      ``ThreeWordCodes.noncommuting_pair_completion,
      ``ThreeWordCodes.commuting_iff_common_power,
      ``ThreeWordCodes.greedy_completion,
      ``ThreeWordCodes.binary_suffices,
      ``ThreeWordCodes.border_and_crossed_suffice,
      ``ThreeWordCodes.BinaryGaps.uniform_coordinate_change,
      ``ThreeWordCodes.BinaryGaps.uniform_lengthening_bound,
      ``ThreeWordCodes.BinaryGaps.large_gap_locates_bodies,
      ``ThreeWordCodes.threeWordTheorem_iff_binary,
      ``ThreeWordCodes.BinaryGaps.ambiguity_left_margin,
      ``ThreeWordCodes.BinaryGaps.gap_list_comparison,
      ``ThreeWordCodes.BinaryGaps.uniform_gaps_of_ambiguity,
      ``ThreeWordCodes.BinaryGaps.uniform_gaps_of_no_completion,
      ``ThreeWordCodes.BinaryGaps.uniform_gaps_of_words,
      ``ThreeWordCodes.BinaryGaps.uniform_gaps_of_terminal_reductions,
      ``ThreeWordCodes.BinaryGaps.terminal_gaps_of_words,
      ``ThreeWordCodes.BinaryGaps.maximum_block_completion,
      ``ThreeWordCodes.BinaryGaps.different_endpoint_blocks_completion,
      ``ThreeWordCodes.BinaryGaps.pure_power_iff_common_maximum,
      ``ThreeWordCodes.BinaryGaps.initial_pattern_certificate,
      ``ThreeWordCodes.BinaryGaps.locate_block_pattern,
      ``ThreeWordCodes.BlockRuns.initial_run,
      ``ThreeWordCodes.BinaryGaps.maximum_run_certificate,
      ``ThreeWordCodes.BinaryGaps.maximum_run_completion,
      ``ThreeWordCodes.BinaryGaps.common_maximum_construction,
      ``ThreeWordCodes.BinaryGaps.pure_power_completion,
      ``ThreeWordCodes.BinaryGaps.one_marker_construction,
      ``ThreeWordCodes.three_word_pure_power_completion,
      ``ThreeWordCodes.pure_reading_completion,
      ``ThreeWordCodes.BinaryGaps.selected_gap_certificate,
      ``ThreeWordCodes.BinaryGaps.maximum_dominated,
      ``ThreeWordCodes.BinaryGaps.dominated_run,
      ``ThreeWordCodes.Palindromic.record_gap_completion,
      ``ThreeWordCodes.Palindromic.minimum_initial_completion,
      ``ThreeWordCodes.Palindromic.selected_completion,
      ``ThreeWordCodes.Palindromic.raw_selection,
      ``ThreeWordCodes.Palindromic.absent_block_completion,
      ``ThreeWordCodes.Palindromic.first_maximum_completion,
      ``ThreeWordCodes.Palindromic.pattern_completion,
      ``ThreeWordCodes.Palindromic.equal_blocks_completion,
      ``ThreeWordCodes.Palindromic.block_run_completion,
      ``ThreeWordCodes.Palindromic.unequal_blocks_completion,
      ``ThreeWordCodes.Palindromic.common_gap_construction,
      ``ThreeWordCodes.Border.solve_conjugacy,
      ``ThreeWordCodes.Border.normal_form,
      ``ThreeWordCodes.Border.border_has_form,
      ``ThreeWordCodes.Border.Form.marked_ends,
      ``ThreeWordCodes.Border.letter_family,
      ``ThreeWordCodes.Border.third_on_pieces,
      ``ThreeWordCodes.Border.second_on_others,
      ``ThreeWordCodes.Border.commuting_second_third,
      ``ThreeWordCodes.Border.of_completable_pieces,
      ``ThreeWordCodes.Border.read_at_branch,
      ``ThreeWordCodes.Border.family_reverse,
      ``ThreeWordCodes.Border.forbidden_identity,
      ``ThreeWordCodes.Border.end_cuts_ambiguous,
      ``ThreeWordCodes.Border.transfer_family,
      ``ThreeWordCodes.Border.transfer_endCut,
      ``ThreeWordCodes.Border.transfer_commuting,
      ``ThreeWordCodes.Border.Form.to_model,
      ``ThreeWordCodes.Border.Model.unique_letter,
      ``ThreeWordCodes.Border.no_third_letter,
      ``ThreeWordCodes.Border.first_letter_zero,
      ``ThreeWordCodes.Border.first_large_gap,
      ``ThreeWordCodes.Border.no_first_letter,
      ``ThreeWordCodes.Border.one_marker_blocks,
      ``ThreeWordCodes.Border.no_second_letter,
      ``ThreeWordCodes.Border.no_model,
      ``ThreeWordCodes.Border.border_completion,
      ``ThreeWordCodes.four_crossed_rows_suffice,
      ``ThreeWordCodes.CrossedCase.to_model,
      ``ThreeWordCodes.CrossedCase.crossed_models_suffice,
      ``ThreeWordCodes.CrossedCase.Model.reverse,
      ``ThreeWordCodes.CrossedCase.shared_central,
      ``ThreeWordCodes.CrossedCase.intermediate_central,
      ``ThreeWordCodes.CrossedCase.disjoint_left,
      ``ThreeWordCodes.CrossedCase.disjoint_right,
      ``ThreeWordCodes.CrossedCase.disjoint_central,
      ``ThreeWordCodes.CrossedCase.disjoint_impossible,
      ``ThreeWordCodes.CrossedCase.three_crossed_rows_suffice,
      ``ThreeWordCodes.CrossedCase.joined_uniform,
      ``ThreeWordCodes.CrossedCase.residue_triple,
      ``ThreeWordCodes.CrossedCase.joined_one,
      ``ThreeWordCodes.CrossedCase.finish_at_b,
      ``ThreeWordCodes.CrossedCase.read_before_b,
      ``ThreeWordCodes.CrossedCase.shared_impossible,
      ``ThreeWordCodes.CrossedCase.two_crossed_rows_suffice,
      ``ThreeWordCodes.CrossedCase.intermediate_margins,
      ``ThreeWordCodes.CrossedCase.unit_gaps_of_reading,
      ``ThreeWordCodes.CrossedCase.alternating_intermediate_test,
      ``ThreeWordCodes.CrossedCase.joined_test_two,
      ``ThreeWordCodes.CrossedCase.intermediate_left,
      ``ThreeWordCodes.CrossedCase.intermediate_right,
      ``ThreeWordCodes.CrossedCase.intermediate_impossible,
      ``ThreeWordCodes.CrossedCase.overlap_suffices,
      ``ThreeWordCodes.CrossedCase.alternating_auxiliary,
      ``ThreeWordCodes.CrossedCase.overlap_central,
      ``ThreeWordCodes.CrossedCase.overlap_margins,
      ``ThreeWordCodes.CrossedCase.overlap_unit,
      ``ThreeWordCodes.CrossedCase.overlap_two,
      ``ThreeWordCodes.CrossedCase.overlap_many,
      ``ThreeWordCodes.CrossedCase.bounded_long_block,
      ``ThreeWordCodes.Border.blocks_from_prefix_bound,
      ``ThreeWordCodes.CrossedCase.overlap_ba,
      ``ThreeWordCodes.CrossedCase.overlap_impossible,
      ``ThreeWordCodes.three_word_theorem,
      ``ThreeWordCodes.three_word_positive_completion,
      ``ThreeWordCodes.Border.lift_cut,
      ``ThreeWordCodes.Border.all_cuts_ambiguous,
      ``ThreeWordCodes.Palindromic.proposition_seven,
      ``ThreeWordCodes.Palindromic.palindromic_completion,
      ``ThreeWordCodes.Palindromic.power_graft_completion,
      ``ThreeWordCodes.Palindromic.initial_bab_completion,
      ``ThreeWordCodes.Palindromic.final_bab_completion,
      ``ThreeWordCodes.Palindromic.middle_reading,
      ``ThreeWordCodes.Palindromic.basis_injective,
      ``ThreeWordCodes.Palindromic.signed_equations,
      ``ThreeWordCodes.Palindromic.single_gap_completion,
      ``ThreeWordCodes.Palindromic.single_code_iff,
      ``ThreeWordCodes.Palindromic.initial_rise_completion,
      ``ThreeWordCodes.Palindromic.Reading.unique,
      ``ThreeWordCodes.Palindromic.Reading.reverse,
      ``ThreeWordCodes.Palindromic.Reading.equations,
      ``ThreeWordCodes.Palindromic.all_gap_bounds,
      ``ThreeWordCodes.Palindromic.two_gap_completion,
      ``ThreeWordCodes.Palindromic.proposition_seven_iff_common_gaps,
      ``ThreeWordCodes.Palindromic.complete_on_x_c,
      ``ThreeWordCodes.Palindromic.alternating_third_completion,
      ``ThreeWordCodes.Palindromic.final_a_completion,
      ``ThreeWordCodes.Palindromic.initial_a_completion,
      ``ThreeWordCodes.Palindromic.forbidden_factor_completion,
      ``ThreeWordCodes.Palindromic.residual_word,
      ``ThreeWordCodes.crossed_commuting_completion,
      ``ThreeWordCodes.crossed_obstruction_conditions,
      ``ThreeWordCodes.SelectedGraft.certificate,
      ``ThreeWordCodes.BinaryGaps.gap_selection_certificate,
      ``ThreeWordCodes.BinaryGaps.record_gap_certificate,
      ``ThreeWordCodes.BinaryGaps.repeated_endpoint_certificate,
      ``ThreeWordCodes.BinaryGaps.at_most_three_gaps,
      ``ThreeWordCodes.BinaryGaps.fresh_block_certificate,
      ``ThreeWordCodes.BinaryGaps.unequal_blocks_completion,
      ``ThreeWordCodes.BinaryGaps.repeated_block_certificate,
      ``ThreeWordCodes.BinaryGaps.new_separator_certificate,
      ``ThreeWordCodes.BinaryGaps.equal_minimum_blocks_completion,
      ``ThreeWordCodes.BinaryGaps.unique_minimum_completion,
      ``ThreeWordCodes.BinaryGaps.pure_power_iff_repeated_interior,
      ``ThreeWordCodes.Palindromic.complete_reading,
      ``ThreeWordCodes.Palindromic.two_proper_readings,
      ``ThreeWordCodes.Palindromic.graft_certificate,
      ``ThreeWordCodes.Palindromic.graft_completion,
      ``ThreeWordCodes.crossed_of_completable_pieces,
      ``ThreeWordCodes.crossed_pieces_ambiguous,
      ``ThreeWordCodes.BinaryGaps.first_long_gap_certificate,
      ``ThreeWordCodes.BinaryGaps.minimum_first_gap_completion,
      ``ThreeWordCodes.BinaryGaps.minimum_last_gap_completion,
      ``ThreeWordCodes.BinaryGaps.pure_power_iff_interior_minimum,
      ``ThreeWordCodes.crossed_table_exhaustive,
      ``ThreeWordCodes.border_and_four_rows_suffice,
      ``ThreeWordCodes.both_crossed_shortenings_ambiguous,
      ``ThreeWordCodes.BinaryGaps.first_short_gap_certificate,
      ``ThreeWordCodes.BinaryGaps.initial_short_gap_completion,
      ``ThreeWordCodes.BinaryGaps.final_short_gap_completion,
      ``ThreeWordCodes.BinaryGaps.short_gap_blocks,
      ``ThreeWordCodes.BinaryGaps.residue_completion,
      ``ThreeWordCodes.reduction_of_noncompletion,
      ``ThreeWordCodes.pure_decoding,
      ``ThreeWordCodes.shortest_pure_invariants,
      ``ThreeWordCodes.BinaryGaps.pure_to_letter_layout,
      ``ThreeWordCodes.BinaryGaps.one_marker_suffices,
      ``ThreeWordCodes.BinaryGaps.pure_power_iff_one_marker,
      ``ThreeWordCodes.BinaryGaps.left_marker_completion,
      ``ThreeWordCodes.BinaryGaps.right_marker_completion,
      ``ThreeWordCodes.BinaryGaps.one_marker_gaps,
      ``ThreeWordCodes.BinaryGaps.one_marker_ambiguity_iff,
      ``ThreeWordCodes.BinaryGaps.common_block_ambiguity,
      ``ThreeWordCodes.BinaryGaps.single_marker_lengthening,
      ``ThreeWordCodes.BinaryGaps.bar_letter_realization,
      ``ThreeWordCodes.BinaryGaps.one_marker_lengthening,
      ``ThreeWordCodes.BinaryGaps.normalized_lengthening_margins,
      ``ThreeWordCodes.binary_realization,
      ``ThreeWordCodes.traced_binary_realization,
      ``ThreeWordCodes.normalize_letter_realization,
      ``ThreeWordCodes.letter_realization_of_lengthening,
      ``ThreeWordCodes.letter_lengthening_case,
      ``ThreeWordCodes.letter_realization,
      ``ThreeWordCodes.BinaryGaps.normalized_binary_lengthening,
      ``ThreeWordCodes.BinaryGaps.gap_coordinate_change,
      ``ThreeWordCodes.BinaryGaps.binary_letter_normal_form,
      ``ThreeWordCodes.GraftExample.family_certificate,
      ``ThreeWordCodes.letter_model_of_commuting_pair,
      ``ThreeWordCodes.same_initial_pairs,
      ``ThreeWordCodes.same_final_pairs,
      ``ThreeWordCodes.sameEquations_of_group_change,
      ``ThreeWordCodes.GroupCoordinates.change_involutive,
      ``ThreeWordCodes.GroupCoordinates.aba_coordinates,
      ``ThreeWordCodes.BinaryGaps.two_mixed_completion,
      ``ThreeWordCodes.tree_extension_certificate,
      ``ThreeWordCodes.tree_extension,
      ``ThreeWordCodes.GraftExample.completion,
      ``ThreeWordCodes.GraftExample.not_prefix,
      ``ThreeWordCodes.GraftExample.not_suffix,
      ``ThreeWordCodes.comparison_table_first,
      ``ThreeWordCodes.comparison_table_second,
      ``ThreeWordCodes.alternating_ambiguity] do
    let deps ← Lean.collectAxioms decl
    for ax in deps do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"

-- For x = aba and z = baab, the gap is 2. With positive outside
-- exponents (1,1) the list is ambiguous. With (1,3) it is a code.
example : ¬ NamedCode (Palindromic.triple 0 0 0 (Palindromic.single 0 0)) := by
  rw [Palindromic.single_code_iff]; decide
example : Completable (Palindromic.triple 0 0 2 (Palindromic.single 0 0)) := by
  apply Palindromic.proposition_seven
  rw [Palindromic.single_code_iff]; decide

-- The border aba of ababa overlaps itself in a single letter.
example : Border.Form [a,b,a] [a,b,a,b,a] where
  p := [a]
  q := [b]
  n := 1
  i := 0
  j := 0
  p_nonempty := by decide
  q_nonempty := by decide
  short_word := rfl
  long_word := rfl
  left_stop := by decide
  right_stop := by decide

-- The successive b-gaps of (aba)^3 are both 2.
example : wordPow [a,b,a] 3 = [a] ++ Border.body 2 2 ++ [a] := Border.aba_body 2

-- Check the three-word binary example.
example : prescribed.card = 3 := by decide
example : prescribed ⊂ completed := by decide
example : leaves (internalNodes prescribed) = insert [b, b, b] prescribed := by decide
example : internalNodes prescribed = {[], [b], [b, b]} := by decide

-- Both cuts (ε,a) and (a,ε) contribute to the coefficient of a.
example : productCoeff ({[], [a]} : Finset (Word Bool)) id {[], [a]} [a] = 2 := by decide

-- The word bbbbabb is (bbb)(ba) followed by bb.
example : assemble completed remainders {[]}
    (⟨[], by decide⟩,
      [⟨[b, b, b], by decide⟩, ⟨[b, a], by decide⟩],
      ⟨[b, b], by decide⟩) = [b, b, b, b, a, b, b] := rfl

-- For the empty alphabet and empty input, only the root remains.
example : leaves (internalNodes (∅ : Finset (Word (Fin 0)))) = ∅ := by decide

-- Print the computed sets. The empty string denotes the empty word.
private def showWord (w : Word Bool) : String :=
  String.ofList (w.map fun c => if c then 'b' else 'a')

#eval ((leaves (internalNodes prescribed)).image showWord).sort
#eval ((internalNodes prescribed).image showWord).sort

-- The graft example is genuinely a three-word input.
example : GraftExample.input.card = 3 := by decide

-- The second leaf covers the proper suffix C in the two-leaf interior cut.
example : SelectedGraft.Valid (pair [a] [b,a,a]) [[a],[a,a,b],[b,a,b],[b,a,b,b]]
    [b,a,b] [b,a,a,a,b] := by decide

-- A repeated interior minimum with unequal blocks on its two sides.
example : Completable (BinaryGaps.oneMarker 2 2 (BinaryGaps.mixed 0 [3,2,3,2,4] 0)) := by
  apply BinaryGaps.raise_left_margin (l:=2) (by decide) (by decide)
  exact BinaryGaps.repeated_endpoint_certificate 2 1 0 [0,2] (by decide) (by decide)
