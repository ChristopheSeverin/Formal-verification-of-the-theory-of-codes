module

public import SmallestNoncompletable.TotalLength
public import SmallestNoncompletable.XCode
public import SmallestNoncompletable.NoCompletion

/-! # The simultaneous minimality theorem -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

universe u

/-- **Theorem 1 (a).** A finite code on a finite alphabet with at most three words, or with
words of length at most three, or with total length at most ten, has a positively factorizing
finite maximal completion on the same alphabet. -/
theorem completion_of_small {A : Type u} [Fintype A] [DecidableEq A] (Y : Finset (Word A))
    (hY : IsUniquelyDecodable (Y : Set (Word A)))
    (h : Y.card ≤ 3 ∨ maxLength Y ≤ 3 ∨ totalLength Y ≤ 10) :
    HasPositiveCompletion (Y : Set (Word A)) := by
  rcases h with h | h | h
  · exact small_code_completion Y h hY
  · exact prop5 Y hY fun w hw => (le_maxLength hw).trans h
  · exact completion_of_totalLength_le_ten Y hY h

theorem Xfinset_coe {A : Type*} [DecidableEq A] (a b : A) :
    ((Xfinset a b : Finset (Word A)) : Set (Word A)) = Xwords a b := by
  ext w; simp [Xfinset, Xwords]

/-- **Theorem 1 (b).** `X = {aa, abab, baaa, b}` is contained in no finite maximal code. -/
theorem X_no_finite_maximal_completion {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b)
    (M : Finset (Word A)) (hX : Xfinset a b ⊆ M) : ¬ IsMaximalCode (M : Set (Word A)) :=
  no_finite_maximal_completion hab M.finite_toSet (by
    rw [← Xfinset_coe]; exact_mod_cast hX)

/-- **Theorem 1 (c).** The invariants of `X`. -/
theorem X_invariants {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    (Xfinset a b).card = 4 ∧ maxLength (Xfinset a b) = 4 ∧ totalLength (Xfinset a b) = 11 := by
  have h1 : [a, a] ∉ ({[a, b, a, b], [b, a, a, a], [b]} : Finset (Word A)) := by
    simp
  have h2 : [a, b, a, b] ∉ ({[b, a, a, a], [b]} : Finset (Word A)) := by
    simp [hab]
  have h3 : [b, a, a, a] ∉ ({[b]} : Finset (Word A)) := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Xfinset, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  · simp [maxLength, Xfinset]
  · rw [totalLength, Xfinset, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
      Finset.sum_singleton]
    simp

/-- **Theorem 1 (simultaneous minimality).** -/
theorem simultaneous_minimality : SimultaneousMinimality.{u} :=
  ⟨fun _ _ _ Y hY h => completion_of_small Y hY h, fun _ _ _ _ hab =>
    ⟨Xfinset_uniquelyDecodable hab, X_no_finite_maximal_completion hab, X_invariants hab⟩⟩

end SmallestNoncompletable
