module

meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command
import SubalgebraFreeness

open SubalgebraFreeness Turing

-- The main statements, the input format and the generated subalgebra.
#check @freeness_undecidable
#check @ring_freeness_undecidable
#check @polynomial_freeness_undecidable
#check @computation_free_iff
#check @Rules.free_iff_forest
#print Rules.OnCycle
#print WordSpec
#print WordSpec.eval
#print word
#print generated
#print axioms SubalgebraFreeness.freeness_undecidable

-- The specification `(ab, ba)` denotes the commutator of the two letters.
example (K : Type) [Field K] :
    WordSpec.eval K (.inr ([false, true], [true, false])) =
      FreeAlgebra.ι K false * FreeAlgebra.ι K true - FreeAlgebra.ι K true * FreeAlgebra.ι K false := by
  simp [WordSpec.eval, word]

-- A machine that halts at once closes a cycle through the initial word, so its algebra is free
-- on no alphabet.
example (K : Type) [Field K] (B : Type) :
    IsEmpty (((Machine.rules (fun (_ : Unit) (_ : Bool) => none) []).pres K).range ≃ₐ[K]
      FreeAlgebra K B) :=
  (computation_free_iff _ _).2 ⟨TM0.init [], Relation.ReflTransGen.refl, rfl⟩ B

-- A machine that always moves right never halts, so its algebra is free on the tape letters,
-- the delimiters and one letter per rule.
example (K : Type) [Field K] :
    Nonempty (((Machine.rules (fun (q : Unit) (_ : Bool) => some (q, TM0.Stmt.move Dir.right))
      []).pres K).range ≃ₐ[K] FreeAlgebra K (Cell Bool ⊕ Rule Bool Unit)) := by
  refine (computation_free_iff.{0} _ _).1.2 ?_
  rintro ⟨cfg, -, h⟩
  simp [TM0.step] at h

-- Reject any new axiom in the transitive dependencies of the public results.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``SubalgebraFreeness.injective_of_letters,
      ``SubalgebraFreeness.injective_of_free,
      ``SubalgebraFreeness.Rules.pres_injective,
      ``SubalgebraFreeness.Rules.highOrder_of_pres_eq_zero,
      ``SubalgebraFreeness.Rules.incidence_kernel_periodic,
      ``SubalgebraFreeness.Rules.incidence_not_injective,
      ``SubalgebraFreeness.Rules.exists_kernel_of_onCycle,
      ``SubalgebraFreeness.Rules.kernel_eq_zero_of_not_onCycle,
      ``SubalgebraFreeness.Rules.free_iff_forest,
      ``SubalgebraFreeness.Rules.free_of_no_periodic,
      ``SubalgebraFreeness.Rules.not_free_of_periodic,
      ``SubalgebraFreeness.Machine.functional,
      ``SubalgebraFreeness.Machine.step_sim,
      ``SubalgebraFreeness.Machine.periodic_of_halts,
      ``SubalgebraFreeness.Machine.halts_of_cleanup,
      ``SubalgebraFreeness.Machine.reset_in_cycle,
      ``SubalgebraFreeness.Machine.periodic_iff_halts,
      ``SubalgebraFreeness.Machine.lhs_not_periodic,
      ``SubalgebraFreeness.Universal.halts_iff,
      ``SubalgebraFreeness.embed_injective,
      ``SubalgebraFreeness.eq_algebraMap_of_mul_eq_one,
      ``SubalgebraFreeness.nonempty_algEquiv_of_ringEquiv,
      ``SubalgebraFreeness.Reduction.free_iff_not_halts,
      ``SubalgebraFreeness.Reduction.resetSpec_primrec,
      ``SubalgebraFreeness.computation_free_iff,
      ``SubalgebraFreeness.halts_iff_not_free,
      ``SubalgebraFreeness.freeness_undecidable,
      ``SubalgebraFreeness.ringEquiv_iff_algEquiv,
      ``SubalgebraFreeness.ring_freeness_undecidable,
      ``SubalgebraFreeness.polynomial_freeness_undecidable] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
