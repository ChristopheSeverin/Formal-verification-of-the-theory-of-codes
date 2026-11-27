module

public import SmallestNoncompletable.CommonFactor
public import SmallestNoncompletable.WeakDivision
import Mathlib.Tactic.Abel

/-! # From a weak factorization to a factorization through `1 - a - b`

This is the part of the proof of Theorem 14.2.1 of Berstel–Perrin–Reutenauer that gives
Corollary 14.2.3. Let `M` be a polynomial and `M*` an inverse of `1 - M`. Suppose that the
series of all words is `R₁ + S₁ M* P` for polynomials with `R₁` without constant term and
`P` with constant term one. Then `1 - M = P Q⁻¹ B S₁` with `Q = 1 - B R₁`, and a common
factorization of `P`, `Q` and `B S₁` followed by a weak division by `B` gives polynomials with
`1 - M = J B N`. -/

@[expose] public section

namespace SmallestNoncompletable

namespace Ser

variable {α K : Type*} [Field K]

/-- The series of all words, with every coefficient one. -/
def allWords : Ser α K := ⟨fun _ => 1⟩

@[simp] theorem coeff_allWords (w : List α) : (allWords : Ser α K).coeff w = 1 := rfl

theorem shift_B (x : Bool) : shift x (B : Ser Bool K) = -1 := by
  ext w
  rw [coeff_shift, coeff_B]
  cases w with
  | nil => cases x <;> simp
  | cons y w => simp

theorem B_mul_allWords : (B : Ser Bool K) * allWords = 1 := by
  ext w
  cases w with
  | nil => simp [coeff_B]
  | cons x w =>
    rw [coeff_mul_cons, shift_B, neg_mul, one_mul, coeff_neg, coeff_allWords, coeff_allWords]
    simp [coeff_B]

theorem allWords_mul_B : (allWords : Ser Bool K) * B = 1 := by
  ext w
  induction w with
  | nil => simp [coeff_B]
  | cons a w ih =>
    rw [coeff_mul_cons, show shift a (allWords : Ser Bool K) = allWords from rfl, ih]
    cases w <;> cases a <;> simp [coeff_B]

theorem not_isPoly_allWords : ¬ IsPoly (allWords : Ser Bool K) := by
  rintro ⟨d, hd⟩
  have := hd (List.replicate (d + 1) false) (by simp)
  simp at this

/-- **The factorization step.** A weak factorization of the series of all words yields
`1 - M = J B N` with polynomials `J`, `N`. -/
theorem factorization_of_weak {M R₁ S₁ P Mstar : Ser Bool K} (hM : IsPoly M) (hR : IsPoly R₁)
    (hS : IsPoly S₁) (hP : IsPoly P) (hR0 : R₁.coeff [] = 0)
    (hP0 : P.coeff [] = 1) (hstar : Mstar * (1 - M) = 1)
    (hweak : allWords = R₁ + S₁ * Mstar * P) :
    ∃ J N : Ser Bool K, IsPoly J ∧ IsPoly N ∧ 1 - M = J * B * N := by
  set Q : Ser Bool K := 1 - B * R₁ with hQ
  have hQp : IsPoly Q := IsPoly.one.sub (IsPoly.B.mul hR)
  have hQ0 : Q.coeff [] = 1 := by simp [hQ, coeff_B, hR0]
  have hPu : IsUnit P := isUnit_of_coeff_nil_ne_zero (by rw [hP0]; exact one_ne_zero)
  have hQu : IsUnit Q := isUnit_of_coeff_nil_ne_zero (by rw [hQ0]; exact one_ne_zero)
  -- `B S₁ M* P = Q`.
  have key : B * S₁ * Mstar * P = Q := by
    have e := congrArg (B * ·) hweak
    simp only [B_mul_allWords, mul_add] at e
    rw [hQ, e]
    simp only [mul_assoc]
    abel
  -- `P Q⁻¹ B S₁ = 1 - M`.
  have hX : P * Ring.inverse Q * (B * S₁) = 1 - M := by
    have h1 : P * Ring.inverse Q * (B * S₁) * Mstar = 1 := by
      have this : B * S₁ * Mstar = Q * Ring.inverse P := by
        calc B * S₁ * Mstar = B * S₁ * Mstar * (P * Ring.inverse P) := by
              rw [Ring.mul_inverse_cancel _ hPu, mul_one]
          _ = B * S₁ * Mstar * P * Ring.inverse P := by simp only [mul_assoc]
          _ = Q * Ring.inverse P := by rw [key]
      calc P * Ring.inverse Q * (B * S₁) * Mstar
          = P * Ring.inverse Q * (B * S₁ * Mstar) := by simp only [mul_assoc]
        _ = P * Ring.inverse Q * (Q * Ring.inverse P) := by rw [this]
        _ = P * (Ring.inverse Q * Q) * Ring.inverse P := by simp only [mul_assoc]
        _ = 1 := by rw [Ring.inverse_mul_cancel _ hQu, mul_one, Ring.mul_inverse_cancel _ hPu]
    calc P * Ring.inverse Q * (B * S₁) = P * Ring.inverse Q * (B * S₁) * (Mstar * (1 - M)) := by
          rw [hstar, mul_one]
      _ = 1 - M := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨J, K', L, N, hJ, hK, hL, hN, eP, eQ, eR, eF⟩ :=
    common_factor hP hQp (IsPoly.B.mul hS) (IsPoly.one.sub hM)
      (by rw [hQ0]; exact one_ne_zero) hX
  -- Divide `L` by `B`.
  have hK0 : K' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at eQ
    have := congrArg (fun f : Ser Bool K => f.coeff []) eQ
    simp [hQ0] at this
  obtain ⟨T, β, hT, eL⟩ := weak_division hL hK hK0 hR.neg (r := 1) (by
    rw [← eQ, hQ, C_one, mul_neg]
    abel)
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [C_zero, add_zero] at eL
    apply not_isPoly_allWords (K := K)
    have e : B * (T * K' + R₁) = 1 := by
      rw [mul_add, ← mul_assoc, ← eL, ← eQ, hQ]
      abel
    have : (allWords : Ser Bool K) = T * K' + R₁ := by
      calc (allWords : Ser Bool K) = allWords * (B * (T * K' + R₁)) := by rw [e, mul_one]
        _ = T * K' + R₁ := by rw [← mul_assoc, allWords_mul_B, one_mul]
    rw [this]
    exact (hT.mul hK).add hR
  -- `N` is a multiple of `B` on the left.
  have eN : N = B * (β⁻¹ • (S₁ - T * N)) := by
    have e : β • N = B * (S₁ - T * N) := by
      rw [mul_sub, eR, eL, add_mul, C_mul, mul_assoc]
      abel
    rw [mul_smul', ← e, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  refine ⟨J, β⁻¹ • (S₁ - T * N), hJ, (hS.sub (hT.mul hN)).smul _, ?_⟩
  calc 1 - M = J * N := eF
    _ = J * (B * (β⁻¹ • (S₁ - T * N))) := by rw [← eN]
    _ = J * B * (β⁻¹ • (S₁ - T * N)) := by rw [mul_assoc]

/-- The constant terms of a factorization can be normalized to one. -/
theorem normalize_factorization {M J N : Ser Bool K} (hM0 : M.coeff [] = 0)
    (h : 1 - M = J * B * N) :
    J.coeff [] ≠ 0 ∧ 1 - M = ((J.coeff [])⁻¹ • J) * B * (J.coeff [] • N) ∧
      ((J.coeff [])⁻¹ • J).coeff [] = 1 ∧ (J.coeff [] • N).coeff [] = 1 := by
  have h0 := congrArg (fun f : Ser Bool K => f.coeff []) h
  simp only [coeff_sub, coeff_one_nil, hM0, sub_zero, coeff_mul_nil, coeff_B] at h0
  simp only [ite_true, List.nil_eq, reduceCtorEq, ite_false, sub_zero, mul_one] at h0
  have hJ : J.coeff [] ≠ 0 := fun e => by rw [e, zero_mul] at h0; exact one_ne_zero h0
  refine ⟨hJ, ?_, ?_, ?_⟩
  · rw [h]
    simp only [smul_mul', mul_smul', smul_smul, mul_inv_cancel₀ hJ, one_smul]
  · simp [inv_mul_cancel₀ hJ]
  · simp only [coeff_smul]
    rw [h0]
