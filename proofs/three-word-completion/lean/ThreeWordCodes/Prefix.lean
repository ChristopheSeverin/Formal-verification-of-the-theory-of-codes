module

public import ThreeWordCodes.Maximal
public import ThreeWordCodes.Parsing

/-! # Positive finite completion of prefix codes -/

@[expose] public section

namespace ThreeWordCodes

variable {A : Type*}

open Classical in
/-- With Q = {ε}, an injective spelling gives at most one cut of each word. -/
private theorem productCoeff_epsilon {ι : Type*} [DecidableEq A] (S : Finset ι)
    (spell : ι → Word A) (inj : Function.Injective spell) (w : Word A) :
    productCoeff S spell {[]} w = (if ∃ i ∈ S, spell i = w then 1 else 0) := by
  classical
  let cuts := (S ×ˢ ({[]} : Finset (Word A))).filter fun t => spell t.1 ++ t.2 = w
  change cuts.card = _
  by_cases hw : ∃ i ∈ S, spell i = w
  · rw [ite_eq_left hw]
    obtain ⟨i, hi, hiw⟩ := hw
    have one : cuts = {(i, [])} := by
      ext ⟨j, q⟩
      constructor
      · intro hj
        obtain ⟨hprod, he⟩ := Finset.mem_filter.mp hj
        obtain rfl : q = [] := Finset.mem_singleton.mp (Finset.mem_product.mp hprod).2
        have hjw : spell j = w := by simpa using he
        exact Finset.mem_singleton.mpr (Prod.ext (inj (hjw.trans hiw.symm)) rfl)
      · intro h
        rw [Finset.mem_singleton.mp h]
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, by simp⟩, by simpa using hiw⟩
    simp [one]
  · have empty : cuts = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨j,q⟩ hj
      obtain ⟨hprod, he⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjS, hq⟩ := Finset.mem_product.mp hprod
      obtain rfl : q = [] := Finset.mem_singleton.mp hq
      exact hw ⟨j, hjS, by simpa using he⟩
    simp [empty, hw]

theorem leaves_polynomial [Fintype A] [DecidableEq A]
    {I : Finset (Word A)} (hI : RootedPrefixClosed I) :
    PolynomialIdentity (leaves I) I {[]} := by
  classical
  have hinj : Function.Injective (fun pa : Word A × A => pa.1 ++ [pa.2]) := by
    rintro ⟨p,a⟩ ⟨v,b⟩ h
    obtain ⟨hp, hab⟩ := List.append_inj' h (by simp)
    exact Prod.ext hp (by simpa using hab)
  intro w
  rw [@productCoeff_epsilon A _ (Classical.decEq A) I id Function.injective_id w,
      @productCoeff_epsilon A _ (Classical.decEq A) _ _ hinj w]
  have hleft : (∃ p ∈ I, id p = w) ↔ w ∈ I := by simp
  have hchildren : (∃ pa ∈ I ×ˢ (Finset.univ : Finset A), pa.1 ++ [pa.2] = w)
      ↔ IsChild I w := by simp [IsChild]
  simp only [hleft, hchildren]
  by_cases hn : w = []
  · subst w
    simp [mem_leaves, hI.root, nil_not_child]
  · by_cases hw : w ∈ I
    · have hc := child_of_internal hI hw hn
      simp [mem_leaves, hw, hn, hc]
    · by_cases hc : IsChild I w <;> simp [mem_leaves, hw, hn, hc]

/-- Explicit witnesses, computable for a finite alphabet with decidable equality. -/
theorem prefix_completion_explicit [Fintype A] [DecidableEq A] (X : Finset (Word A))
    (hpre : InformationTheory.IsPrefixFree (X : Set (Word A))) (hne : [] ∉ X) :
    PositiveCompletion X (leaves (internalNodes X)) (internalNodes X) {[]} := by
  let I := internalNodes X
  have hI : RootedPrefixClosed I := internalNodes_closed X
  have hempty : [] ∉ leaves I := fun h => (mem_leaves.mp h).2 hI.root
  have hcode := (leaves_prefixFree hI).isUniquelyDecodable hempty
  exact ⟨subset_leaves hpre hne,
    maximal_of_finite_right_remainders (leaves I) I hcode (parse_exists hI),
    leaves_polynomial hI, leaves_factorization hI⟩

/-- Every finite uniquely decodable prefix code has a positive finite completion. -/
theorem finite_prefix_positive_completion [Fintype A] (X : Finset (Word A))
    (hcode : InformationTheory.IsUniquelyDecodable (X : Set (Word A)))
    (hpre : InformationTheory.IsPrefixFree (X : Set (Word A))) :
    ∃ M P Q : Finset (Word A), PositiveCompletion X M P Q := by
  classical
  exact ⟨leaves (internalNodes X), internalNodes X, {[]},
    prefix_completion_explicit X hpre hcode.epsilon_notMem⟩

end ThreeWordCodes
