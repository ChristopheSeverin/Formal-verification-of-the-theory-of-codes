module

public import SmallestNoncompletable.Lemma7
public import SmallestNoncompletable.Prop5

/-! # Codes of total length at most ten

Strong induction on the total length, simultaneously over all finite alphabets of a universe.
Codes with at most three words, or with words of length at most three, are completed directly.
Otherwise Lemma 7 gives a reduction, which leads to a code of smaller total length. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

universe u

theorem le_maxLength {A : Type*} {W : Finset (Word A)} {w : Word A} (hw : w ∈ W) :
    w.length ≤ maxLength W := Finset.le_sup (f := List.length) hw

/-- **Total length at most ten.** -/
theorem completion_of_totalLength_le_ten {A : Type u} [Fintype A] [DecidableEq A]
    (W : Finset (Word A)) (hW : IsUniquelyDecodable (W : Set (Word A)))
    (hτ : totalLength W ≤ 10) : HasPositiveCompletion (W : Set (Word A)) := by
  induction h : totalLength W using Nat.strong_induction_on generalizing A W with
  | _ n ih =>
    by_cases hc : W.card ≤ 3
    · exact small_code_completion W hc hW
    by_cases hl : maxLength W ≤ 3
    · exact prop5 W hW fun w hw => (le_maxLength hw).trans hl
    exact completion_of_reducible hW (lemma7 W hW hτ (by omega) (by omega))
      fun B _ _ Z hZ hlt => ih (totalLength Z) (by omega) Z hZ (by omega) rfl

end SmallestNoncompletable
