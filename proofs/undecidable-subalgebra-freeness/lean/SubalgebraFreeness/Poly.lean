module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Noncommutative polynomials as linear combinations of words

`Poly K X` is the monoid algebra of the free monoid on `X`. Mathlib identifies it with the
free algebra `K⟨X⟩` through `FreeAlgebra.equivMonoidAlgebraFreeMonoid`. The words form a basis
and multiplication concatenates them.

`HighOrder n p` states that every word of length less than `n` has coefficient zero in `p`.
Thus `HighOrder 1` describes the zero-constant-term ideal `I`, and `HighOrder 2` describes `I²`.
The last theorem is the manuscript's remark that the lowest nonzero homogeneous component of a
polynomial survives an endomorphism that fixes each letter modulo `I²`. -/

@[expose] public section
namespace SubalgebraFreeness

open MonoidAlgebra

/-- Noncommutative polynomials with coefficients in `K` and letters in `X`. -/
abbrev Poly (K X : Type*) [CommRing K] := MonoidAlgebra K (FreeMonoid X)

variable {K X : Type*} [CommRing K]

/-- The monomial of a word. -/
noncomputable def mono (w : FreeMonoid X) : Poly K X := single w 1

/-- The monomial of a single letter. -/
noncomputable def letter (x : X) : Poly K X := mono (FreeMonoid.of x)

theorem mono_mul (u v : FreeMonoid X) : (mono (u * v) : Poly K X) = mono u * mono v := by
  simp [mono]

theorem mono_one : (mono 1 : Poly K X) = 1 := rfl

/-- The constant coefficient, as a `K`-algebra homomorphism. -/
noncomputable def constCoeff : Poly K X →ₐ[K] K :=
  MonoidAlgebra.lift K K (FreeMonoid X) (FreeMonoid.lift fun _ => (0 : K))

theorem constCoeff_apply (p : Poly K X) : constCoeff p = p.coeff 1 := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single w c =>
    rw [constCoeff, MonoidAlgebra.lift_single, coeff_single, Finsupp.single_apply]
    cases w using FreeMonoid.mulCasesOn with
    | one => simp
    | of_mul x w =>
      have hne : ¬ FreeMonoid.of x * w = 1 := fun h => by
        simpa using congrArg FreeMonoid.toList h
      simp [hne]

/-- Every word shorter than `n` has coefficient zero. -/
def HighOrder (n : ℕ) (p : Poly K X) : Prop :=
  ∀ w : FreeMonoid X, w.toList.length < n → p.coeff w = 0

namespace HighOrder

variable {m n : ℕ} {p q : Poly K X}

theorem zero : HighOrder n (0 : Poly K X) := fun _ _ => by simp

theorem add (hp : HighOrder n p) (hq : HighOrder n q) : HighOrder n (p + q) :=
  fun w hw => by simp [hp w hw, hq w hw]

theorem smul (c : K) (hp : HighOrder n p) : HighOrder n (c • p) :=
  fun w hw => by simp [hp w hw]

theorem mono' (h : m ≤ n) (hp : HighOrder n p) : HighOrder m p :=
  fun w hw => hp w (lt_of_lt_of_le hw h)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → Poly K X} (hf : ∀ i ∈ s, HighOrder n (f i)) :
    HighOrder n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HighOrder n (0 : Poly K X))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mul (hp : HighOrder m p) (hq : HighOrder n q) : HighOrder (m + n) (p * q) := by
  classical
  intro w hw
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
  dsimp only
  split_ifs with h
  · subst h
    rw [FreeMonoid.toList_mul, List.length_append] at hw
    by_cases hu : u.toList.length < m
    · simp [hp u hu]
    · simp [hq v (by omega)]
  · rfl

end HighOrder

theorem highOrder_single (w : FreeMonoid X) (c : K) : HighOrder w.toList.length (single w c) := by
  classical
  intro v hv
  rw [coeff_single, Finsupp.single_apply, ite_eq_right_iff]
  rintro rfl
  exact absurd hv (lt_irrefl _)

theorem highOrder_zero (p : Poly K X) : HighOrder 0 p := fun _ h => absurd h (Nat.not_lt_zero _)

theorem highOrder_one_iff {p : Poly K X} : HighOrder 1 p ↔ constCoeff p = 0 := by
  rw [constCoeff_apply]
  constructor
  · intro h
    exact h 1 (by simp)
  · intro h w hw
    have hw' : w = 1 := FreeMonoid.ext (List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hw))
    rw [hw', h]

/-- Every polynomial is the sum of its monomials. -/
theorem sum_single (p : Poly K X) :
    p = ∑ w ∈ p.coeff.support, p.coeff w • mono w := by
  conv_lhs => rw [← sum_coeff_single p]
  simp [Finsupp.sum, mono]

/-- An algebra homomorphism sending every letter into `HighOrder 1` preserves each `HighOrder n`. -/
theorem HighOrder.map {Y : Type*} (φ : Poly K X →ₐ[K] Poly K Y)
    (hφ : ∀ x, HighOrder 1 (φ (letter x))) {n : ℕ} {p : Poly K X} (hp : HighOrder n p) :
    HighOrder n (φ p) := by
  have word : ∀ w : FreeMonoid X, HighOrder w.toList.length (φ (mono w)) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => exact highOrder_zero _
    | of_mul x w ih =>
      rw [mono_mul, map_mul, FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of,
        List.length_singleton]
      exact (hφ x).mul ih
  rw [sum_single p, map_sum]
  refine HighOrder.sum _ fun w hw => ?_
  rw [map_smul]
  refine HighOrder.smul _ (HighOrder.mono' ?_ (word w))
  by_contra hlt
  exact (Finsupp.mem_support_iff.mp hw) (hp w (not_le.mp hlt))

/-- An endomorphism fixing every letter modulo `I²` is injective: the lowest nonzero homogeneous
component of a polynomial survives evaluation in its own degree. -/
theorem injective_of_letters (ψ : Poly K X →ₐ[K] Poly K X)
    (h : ∀ x, HighOrder 2 (ψ (letter x) - letter x)) : Function.Injective ψ := by
  classical
  have hletter : ∀ x, HighOrder 1 (ψ (letter x)) := by
    intro x
    have hx : HighOrder 1 (letter x : Poly K X) := by
      simpa [letter, mono] using highOrder_single (FreeMonoid.of x) (1 : K)
    simpa using hx.add ((h x).mono' (by norm_num))
  -- Each word is fixed modulo words of greater length.
  have word : ∀ w : FreeMonoid X, HighOrder (w.toList.length + 1) (ψ (mono w) - mono w) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => simpa [mono_one] using HighOrder.zero (K := K) (X := X) (n := 1)
    | of_mul x w ih =>
      have hw : HighOrder w.toList.length (ψ (mono w)) :=
        HighOrder.map ψ hletter (highOrder_single w 1)
      have split : ψ (mono (FreeMonoid.of x * w)) - mono (FreeMonoid.of x * w) =
          (ψ (letter x) - letter x) * ψ (mono w) + letter x * (ψ (mono w) - mono w) := by
        rw [mono_mul, map_mul, sub_mul, mul_sub]
        simp only [letter]
        exact (sub_add_sub_cancel _ _ _).symm
      rw [split, FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of,
        List.length_singleton]
      refine HighOrder.add ?_ ?_
      · exact ((h x).mul hw).mono' (by omega)
      · have hx : HighOrder 1 (letter x : Poly K X) := by
          simpa [letter, mono] using highOrder_single (FreeMonoid.of x) (1 : K)
        exact (hx.mul ih).mono' (by omega)
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  have hsupp : p.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa using hne
  obtain ⟨w₀, hw₀, hmin⟩ := p.coeff.support.exists_min_image (fun w => w.toList.length) hsupp
  have key : (ψ p).coeff w₀ = p.coeff w₀ := by
    have expand := congrArg (fun q => (ψ q).coeff w₀) (sum_single p)
    rw [expand, map_sum, coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single w₀]
    · rw [map_smul, coeff_smul_apply, smul_eq_mul]
      have := word w₀ w₀ (by omega)
      rw [coeff_sub, Finsupp.sub_apply, sub_eq_zero] at this
      rw [this]
      simp [mono]
    · intro w hw hne'
      rw [map_smul, coeff_smul_apply, smul_eq_mul]
      have := word w w₀ (by have := hmin w hw; omega)
      rw [coeff_sub, Finsupp.sub_apply, sub_eq_zero] at this
      rw [this]
      simp [mono, hne']
    · intro h0
      exact absurd hw₀ h0
  rw [hp] at key
  exact (Finsupp.mem_support_iff.mp hw₀) (by simpa using key.symm)

end SubalgebraFreeness
