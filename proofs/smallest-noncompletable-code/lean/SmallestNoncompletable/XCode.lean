module

public import SmallestNoncompletable.Facts
public import SmallestNoncompletable.Transfer

/-! # `X = {aa, abab, baaa, b}` is a code

Two different parsings start with `b` and `baaa`. The dangling suffixes then stay in
`{a, aaa, ab, bab}` and never vanish. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

/-- The dangling suffixes. -/
def Dangling (r : List Bool) : Prop :=
  r = [false] ∨ r = [false, false, false] ∨ r = [false, true] ∨ r = [true, false, true]

theorem mem_Xcode {w : List Bool} :
    w ∈ Xcode ↔ w = [false, false] ∨ w = [false, true, false, true] ∨
      w = [true, false, false, false] ∨ w = [true] := by
  simp [Xcode]

/-- A dangling suffix never closes. -/
theorem no_dangling : ∀ (n : ℕ) (L L' : List (List Bool)), (∀ w ∈ L, w ∈ Xcode) →
    (∀ w ∈ L', w ∈ Xcode) → L.flatten.length + L'.flatten.length ≤ n →
    ∀ r, Dangling r → L.flatten ≠ r ++ L'.flatten := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L L' hL hL' hn r hr e
    match L, hL, hn, e with
    | [], _, _, e =>
      rcases hr with rfl | rfl | rfl | rfl <;> simp at e
    | w :: L₀, hL, hn, e =>
      have hw := hL w (by simp)
      have hL₀ : ∀ v ∈ L₀, v ∈ Xcode := fun v hv => hL v (by simp [hv])
      simp only [List.flatten_cons, List.length_append] at e hn
      rw [mem_Xcode] at hw
      rcases hr with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
        simp only [List.cons_append, List.nil_append, List.cons.injEq, Bool.false_eq_true,
          Bool.true_eq_false, false_and, and_false, true_and] at e
      -- r = a, w = aa
      · exact ih _ (by simp at hn ⊢; omega) L' L₀ hL' hL₀ le_rfl [false] (Or.inl rfl) e.symm
      -- r = a, w = abab
      · exact ih _ (by simp at hn ⊢; omega) L' L₀ hL' hL₀ le_rfl [true, false, true]
          (Or.inr (Or.inr (Or.inr rfl))) e.symm
      -- r = aaa, w = aa
      · exact ih _ (by simp at hn ⊢; omega) L₀ L' hL₀ hL' le_rfl [false] (Or.inl rfl) e
      -- r = ab, w = abab
      · exact ih _ (by simp at hn ⊢; omega) L' L₀ hL' hL₀ le_rfl [false, true]
          (Or.inr (Or.inr (Or.inl rfl))) e.symm
      -- r = bab, w = b
      · exact ih _ (by simp at hn ⊢; omega) L₀ L' hL₀ hL' le_rfl [false, true]
          (Or.inr (Or.inr (Or.inl rfl))) e

/-- **The binary set is a code.** -/
theorem Xcode_uniquelyDecodable : IsUniquelyDecodable Xcode := by
  intro L₁ L₂ h₁ h₂ e
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons w L₂ =>
      exfalso
      have hw := h₂ w (by simp)
      rw [mem_Xcode] at hw
      simp only [List.flatten_nil, List.flatten_cons] at e
      rcases hw with rfl | rfl | rfl | rfl <;> simp at e
  | cons w L₁ ih =>
    cases L₂ with
    | nil =>
      exfalso
      have hw := h₁ w (by simp)
      rw [mem_Xcode] at hw
      simp only [List.flatten_nil, List.flatten_cons] at e
      rcases hw with rfl | rfl | rfl | rfl <;> simp at e
    | cons v L₂ =>
      have hw := h₁ w (by simp)
      have hv := h₂ v (by simp)
      have h₁' : ∀ u ∈ L₁, u ∈ Xcode := fun u hu => h₁ u (by simp [hu])
      have h₂' : ∀ u ∈ L₂, u ∈ Xcode := fun u hu => h₂ u (by simp [hu])
      simp only [List.flatten_cons] at e
      by_cases hwv : w = v
      · subst hwv
        rw [ih L₂ h₁' h₂' (List.append_cancel_left e)]
      · exfalso
        rw [mem_Xcode] at hw hv
        rcases hw with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
          simp only [List.cons_append, List.nil_append, List.cons.injEq, Bool.false_eq_true,
            Bool.true_eq_false, false_and, and_false, true_and, not_true_eq_false] at e hwv
        · exact no_dangling _ L₂ L₁ h₂' h₁' le_rfl _ (Or.inr (Or.inl rfl)) e.symm
        · exact no_dangling _ L₁ L₂ h₁' h₂' le_rfl _ (Or.inr (Or.inl rfl)) e

/-- **`X` is a code** over any alphabet with two distinct letters. -/
theorem Xfinset_uniquelyDecodable {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    IsUniquelyDecodable ((Xfinset a b : Finset (Word A)) : Set (Word A)) := by
  classical
  let ι : Bool → A := fun c => if c then b else a
  have hι : Function.Injective ι := by
    intro c d h
    cases c <;> cases d <;> simp_all [ι, eq_comm]
  have hX : (Xfinset a b) = (({[false, false], [false, true, false, true],
      [true, false, false, false], [true]} : Finset (List Bool))).image (List.map ι) := by
    simp [Xfinset, ι, Finset.image_insert]
  rw [hX]
  apply uniquelyDecodable_image (fun x _ y _ h => hι h)
  have : ((({[false, false], [false, true, false, true], [true, false, false, false], [true]} :
      Finset (List Bool))) : Set (List Bool)) = Xcode := by
    ext w; simp [Xcode]
  rw [this]
  exact Xcode_uniquelyDecodable

end SmallestNoncompletable
