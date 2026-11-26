module

public import NonfreeBinaryFactor.Submonoid
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # Two factorizations into irreducibles inside the middle submonoid -/

@[expose] public section
namespace NonfreeBinaryFactor

theorem short_irreducible {w : middleSubmonoid}
    (hpos : 0 < w.val.toList.length) (hshort : w.val.toList.length < 6) : Irreducible w := by
  constructor
  · intro h
    have word := (h.map middleSubmonoid.subtype).eq_one
    have len : w.val.toList.length = 0 := congrArg (fun t : FreeMonoid Bool => t.toList.length) word
    omega
  · intro x y eq
    by_cases ex : x = 1
    · simp [ex]
    by_cases ey : y = 1
    · simp [ey]
    have bound (t : middleSubmonoid) (ht : t ≠ 1) : 3 ≤ t.val.toList.length :=
      length_ge_three t.property (fun e => ht (Subtype.ext (FreeMonoid.ext e)))
    have hx := bound x ex
    have hy := bound y ey
    have len := congrArg (fun t : middleSubmonoid => t.val.toList.length) eq
    change w.val.toList.length = (x.val.toList ++ y.val.toList).length at len
    rw [List.length_append] at len
    omega

namespace Witness

def aab : middleSubmonoid := ⟨FreeMonoid.ofList [a,a,b], by
  change Middle [a,a,b]
  simp [Middle, LeftNormal, RightNormal, Reduced, a, b]⟩

def babab : middleSubmonoid := ⟨FreeMonoid.ofList [b,a,b,a,b], by
  change Middle [b,a,b,a,b]
  simp [Middle, LeftNormal, RightNormal, Reduced, a, b]⟩

def aabba : middleSubmonoid := ⟨FreeMonoid.ofList [a,a,b,b,a], by
  change Middle [a,a,b,b,a]
  simp [Middle, LeftNormal, RightNormal, Reduced, a, b]⟩

def bab : middleSubmonoid := ⟨FreeMonoid.ofList [b,a,b], by
  change Middle [b,a,b]
  simp [Middle, LeftNormal, RightNormal, Reduced, a, b]⟩

theorem relation : aab * babab = aabba * bab := rfl

theorem irreducibles : Irreducible aab ∧ Irreducible babab ∧ Irreducible aabba ∧ Irreducible bab :=
  ⟨short_irreducible (by decide) (by decide), short_irreducible (by decide) (by decide),
   short_irreducible (by decide) (by decide), short_irreducible (by decide) (by decide)⟩

end Witness

private theorem letter_of_irreducible {X : Type*} {w : FreeMonoid X} (hw : Irreducible w) :
    ∃ x : X, w = FreeMonoid.of x := by
  obtain ⟨w⟩ := w
  cases w with
  | nil => exact (hw.ne_one rfl).elim
  | cons x t =>
    cases t with
    | nil => exact ⟨x, rfl⟩
    | cons y t =>
      -- A list with at least two letters splits after its first letter.
      have cut := hw.isUnit_or_isUnit (a := FreeMonoid.of x) (b := FreeMonoid.ofList (y :: t)) rfl
      rcases cut with first | rest
      · exact (List.cons_ne_nil x [] (congrArg FreeMonoid.toList first.eq_one)).elim
      · exact (List.cons_ne_nil y t (congrArg FreeMonoid.toList rest.eq_one)).elim

/-- No choice of generating alphabet, finite or infinite, makes the middle
submonoid isomorphic to a free monoid. -/
theorem middle_not_free (X : Type*) : ¬ Nonempty (middleSubmonoid ≃* FreeMonoid X) := by
  rintro ⟨e⟩
  obtain ⟨x, hx⟩ := letter_of_irreducible ((MulEquiv.irreducible_iff e).mpr Witness.irreducibles.1)
  obtain ⟨z, hz⟩ := letter_of_irreducible ((MulEquiv.irreducible_iff e).mpr Witness.irreducibles.2.2.1)
  have same := congrArg (fun t : middleSubmonoid => (e t).toList) Witness.relation
  simp only [map_mul, hx, hz, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append] at same
  obtain ⟨rfl, _⟩ := List.cons.inj same
  have first := e.injective (hx.trans hz.symm)
  have bad : (3 : ℕ) = 5 := congrArg (fun t : middleSubmonoid => t.val.toList.length) first
  exact (by decide : (3 : ℕ) ≠ 5) bad

end NonfreeBinaryFactor
