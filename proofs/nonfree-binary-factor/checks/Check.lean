module

meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command
import NonfreeBinaryFactor

open NonfreeBinaryFactor

#check @exists_nonfree_factor
#print assemble
#print axioms NonfreeBinaryFactor.exists_nonfree_factor

-- The empty word and a word with all five factors nonempty.
example (d : ℕ × ℕ × middleSubmonoid × ℕ × ℕ) :
    assemble middleSubmonoid d = 1 ↔ d = (0,0,1,0,0) :=
  ⟨fun h => assemble_bijective.injective (h.trans (show 1 = assemble _ (0,0,1,0,0) by rfl)),
    fun h => by rw [h]; rfl⟩

example (d : ℕ × ℕ × middleSubmonoid × ℕ × ℕ)
    (h : assemble middleSubmonoid d = FreeMonoid.ofList [a,b,a,b,b,a,a,b,a,a,a,b,b]) :
    d = (2,1,Witness.aab,1,1) := by
  apply assemble_bijective.injective
  exact h.trans (by rfl)

example : Witness.aab * Witness.babab = Witness.aabba * Witness.bab := Witness.relation

-- Reject any new axiom in the transitive dependencies of the public results.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``NonfreeBinaryFactor.middle_append, ``NonfreeBinaryFactor.assemble_bijective,
      ``NonfreeBinaryFactor.Witness.irreducibles, ``NonfreeBinaryFactor.Witness.relation,
      ``NonfreeBinaryFactor.middle_not_free, ``NonfreeBinaryFactor.exists_nonfree_factor] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
