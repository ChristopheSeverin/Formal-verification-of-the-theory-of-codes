module

public import SubalgebraFreeness.Poly
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Ring and algebra freeness agree

Choose a word of maximal length in each of two nonzero polynomials `f`, `g`. Their concatenation
arises from this pair only, since the split after `deg f` letters is forced. Thus degrees add,
and the units of every unital `K`-subalgebra of a free algebra are the nonzero scalars.

A ring isomorphism from `K⟨B⟩` onto such a subalgebra therefore restricts to an automorphism of
`K`. Precomposing with its inverse on coefficients gives a `K`-algebra isomorphism. -/

@[expose] public noncomputable section
namespace SubalgebraFreeness

open MonoidAlgebra

variable {K : Type*} [Field K] {X : Type*}

/-- The length of the longest word of a polynomial. -/
def degree (p : Poly K X) : ℕ := p.coeff.support.sup fun w => w.toList.length

theorem exists_top_word {p : Poly K X} (hp : p ≠ 0) :
    ∃ w ∈ p.coeff.support, ∀ v ∈ p.coeff.support, v.toList.length ≤ w.toList.length := by
  have hne : p.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa using hp
  obtain ⟨w, hw, hmax⟩ := p.coeff.support.exists_max_image (fun w => w.toList.length) hne
  exact ⟨w, hw, hmax⟩

/-- **Degrees add.** The product of two top-degree words has a nonzero coefficient. -/
theorem coeff_mul_top {p q : Poly K X} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ wp ∈ p.coeff.support, ∃ wq ∈ q.coeff.support,
      (∀ v ∈ p.coeff.support, v.toList.length ≤ wp.toList.length) ∧ (p * q).coeff (wp * wq) ≠ 0 := by
  obtain ⟨wp, hwp, hmaxp⟩ := exists_top_word hp
  obtain ⟨wq, hwq, hmaxq⟩ := exists_top_word hq
  have huniq : UniqueMul p.coeff.support q.coeff.support wp wq := by
    intro a b ha hb hab
    have hlen := congrArg (fun w : FreeMonoid X => w.toList.length) hab
    simp only [FreeMonoid.toList_mul, List.length_append] at hlen
    have ha' := hmaxp a ha
    have hb' := hmaxq b hb
    have hl : a.toList.length = wp.toList.length := by omega
    have := congrArg FreeMonoid.toList hab
    simp only [FreeMonoid.toList_mul] at this
    obtain ⟨h₁, h₂⟩ := List.append_inj this hl
    exact ⟨FreeMonoid.ext h₁, FreeMonoid.ext h₂⟩
  refine ⟨wp, hwp, wq, hwq, hmaxp, ?_⟩
  rw [coeff_mul_mul_of_uniqueMul huniq]
  exact mul_ne_zero (Finsupp.mem_support_iff.mp hwp) (Finsupp.mem_support_iff.mp hwq)

/-- **Units are scalars** in a free algebra. -/
theorem eq_algebraMap_of_mul_eq_one {p q : Poly K X} (h : p * q = 1) :
    p = algebraMap K (Poly K X) (p.coeff 1) := by
  classical
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have hq : q ≠ 0 := by rintro rfl; simp at h
  obtain ⟨wp, hwp, wq, hwq, hmax, hne⟩ := coeff_mul_top hp hq
  rw [h] at hne
  have h1 : wp * wq = 1 := by
    by_contra h1
    apply hne
    rw [one_def, coeff_single, Finsupp.single_eq_of_ne h1]
  have hwp1 : wp = 1 := by
    have := congrArg (fun w : FreeMonoid X => w.toList.length) h1
    simp only [FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_one,
      List.length_nil] at this
    exact FreeMonoid.ext (List.length_eq_zero_iff.mp (by omega))
  ext w
  rw [MonoidAlgebra.coe_algebraMap]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, coeff_single]
  by_cases hw : w = 1
  · subst hw; simp
  · rw [Finsupp.single_eq_of_ne hw]
    by_contra hcoeff
    have := hmax w (Finsupp.mem_support_iff.mpr hcoeff)
    rw [hwp1] at this
    simp only [FreeMonoid.toList_one, List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at this
    exact hw (FreeMonoid.ext this)

/-- Units of a free algebra are scalars. -/
theorem FreeAlgebra.mem_range_of_isUnit {u : FreeAlgebra K X} (hu : IsUnit u) :
    u ∈ Set.range (algebraMap K (FreeAlgebra K X)) := by
  obtain ⟨⟨u, v, huv, -⟩, rfl⟩ := hu
  let e := FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := X)
  have h : e u * e v = 1 := by rw [← map_mul, huv, map_one]
  refine ⟨(e u).coeff 1, ?_⟩
  apply e.injective
  rw [AlgEquiv.commutes]
  exact (eq_algebraMap_of_mul_eq_one h).symm

/-- **Ring isomorphisms give algebra isomorphisms.** If the units of `A` are scalars, a ring
isomorphism `K⟨B⟩ ≃ A` can be corrected by an automorphism of the coefficients to a
`K`-algebra isomorphism. -/
theorem nonempty_algEquiv_of_ringEquiv {A : Type*} [Ring A] [Algebra K A] [Nontrivial A]
    (hA : ∀ u : A, IsUnit u → u ∈ Set.range (algebraMap K A)) {B : Type*}
    (σ : FreeAlgebra K B ≃+* A) : Nonempty (FreeAlgebra K B ≃ₐ[K] A) := by
  classical
  have hinj : Function.Injective (algebraMap K A) := (algebraMap K A).injective
  have hscalar : ∀ k : K, σ (algebraMap K _ k) ∈ Set.range (algebraMap K A) := by
    intro k
    by_cases hk : k = 0
    · exact ⟨0, by simp [hk]⟩
    · exact hA _ (((Ne.isUnit hk).map (algebraMap K (FreeAlgebra K B))).map σ)
  choose τ hτ using hscalar
  -- `τ` is a ring automorphism of `K`.
  let τh : K →+* K :=
    { toFun := τ
      map_one' := hinj (by rw [hτ, map_one, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hτ, map_mul, map_mul, map_mul, hτ, hτ])
      map_zero' := hinj (by rw [hτ, map_zero, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hτ, map_add, map_add, map_add, hτ, hτ]) }
  have hsurj : Function.Surjective τ := by
    intro k'
    by_cases hk : k' = 0
    · exact ⟨0, hinj (by rw [hτ, map_zero, map_zero, hk, map_zero])⟩
    · have hu : IsUnit (σ.symm (algebraMap K A k')) :=
        ((Ne.isUnit hk).map (algebraMap K A)).map σ.symm
      obtain ⟨k, hk⟩ := FreeAlgebra.mem_range_of_isUnit hu
      refine ⟨k, hinj ?_⟩
      rw [hτ, hk, RingEquiv.apply_symm_apply]
  let τe : K ≃+* K := RingEquiv.ofBijective τh ⟨τh.injective, hsurj⟩
  -- Twist the coefficients of `K⟨B⟩` by the inverse of `τ`.
  let e := FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := B)
  let T : FreeAlgebra K B ≃+* FreeAlgebra K B :=
    e.toRingEquiv.trans ((mapRingEquiv (FreeMonoid B) τe.symm).trans e.symm.toRingEquiv)
  have hT : ∀ k, T (algebraMap K _ k) = algebraMap K _ (τe.symm k) := by
    intro k
    change e.symm (mapRingEquiv (FreeMonoid B) τe.symm (e (algebraMap K _ k))) = _
    rw [AlgEquiv.commutes, ← AlgEquiv.commutes e.symm]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, mapRingEquiv_single]
  refine ⟨AlgEquiv.ofRingEquiv (f := T.trans σ) fun k => ?_⟩
  rw [RingEquiv.trans_apply, hT, ← hτ]
  exact congrArg _ (τe.apply_symm_apply k)

end SubalgebraFreeness
