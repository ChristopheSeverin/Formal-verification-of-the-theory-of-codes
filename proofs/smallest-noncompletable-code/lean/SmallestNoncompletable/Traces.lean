module

public import SmallestNoncompletable.Representations
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # Linear coefficients of determinants and a trace identity

If a matrix of polynomials reduces to the identity at `X = 0`, the coefficient of `X` in its
determinant is the trace of the matrix of coefficients of `X`. For the representations `ψ` and
`ρ` the weight of a word is `X` to the number of letters `b`. On the words with one `b`, the
traces of `ψ` and `ρ` add up to one, which is the coefficient read by `χL` at `X = 1`. -/

@[expose] public section

namespace SmallestNoncompletable

open Polynomial Matrix Ser

/-- The coefficient of `X` in a product. -/
theorem coeff_one_mul (p q : ℚ[X]) : (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

/-- The coefficient of `X` in a `2 × 2` determinant whose constant part is the identity. -/
theorem coeff_one_det_two (P : Matrix (Fin 2) (Fin 2) ℚ[X])
    (h0 : ∀ i j, (P i j).coeff 0 = if i = j then 1 else 0) :
    P.det.coeff 1 = (P 0 0).coeff 1 + (P 1 1).coeff 1 := by
  rw [Matrix.det_fin_two, Polynomial.coeff_sub, coeff_one_mul, coeff_one_mul]
  simp [h0]
  ring

/-- The coefficient of `X` in a `3 × 3` determinant whose constant part is the identity. -/
theorem coeff_one_det_three (P : Matrix (Fin 3) (Fin 3) ℚ[X])
    (h0 : ∀ i j, (P i j).coeff 0 = if i = j then 1 else 0) :
    P.det.coeff 1 = (P 0 0).coeff 1 + (P 1 1).coeff 1 + (P 2 2).coeff 1 := by
  rw [Matrix.det_fin_three]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, coeff_one_mul, Polynomial.mul_coeff_zero,
    h0]
  simp
  ring

/-- The rational matrices of the two letters in the automaton avoiding `bab`. -/
def A₀q : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 0, 1; 1, 0, 0]
def B₀q : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 1, 0; 0, 0, 0]
def Uq : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def Vq : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

/-- The unweighted letters. -/
def ψq : Bool → Matrix (Fin 3) (Fin 3) ℚ := fun c => if c then B₀q else A₀q
def ρq : Bool → Matrix (Fin 2) (Fin 2) ℚ := fun c => if c then Vq else Uq

theorem A₀_eq : A₀ = A₀q.map Polynomial.C := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [A₀, A₀q]

theorem B₀_eq : B₀ = B₀q.map Polynomial.C := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [B₀, B₀q]

/-- The weight of a word for `ψ` is `X` to the number of letters `b`. -/
theorem wordProd_ψ (w : List Bool) :
    wordProd ψ w = (X : ℚ[X]) ^ w.count true • (wordProd ψq w).map Polynomial.C := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [wordProd_cons, wordProd_cons, ih, Matrix.mul_smul, Matrix.map_mul]
    cases c
    · simp [ψ, ψq, A₀_eq]
    · simp only [ψ, ψq, ite_true, B₀_eq, List.count_cons, beq_self_eq_true, Matrix.smul_mul,
        smul_smul, pow_succ]

theorem ρ_false_eq : ρ false = Uq.map Polynomial.C := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ρ, Uq]

theorem ρ_true_eq : ρ true = (X : ℚ[X]) • Vq.map Polynomial.C := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ρ, Vq]

/-- The weight of a word for `ρ` is `X` to the number of letters `b`. -/
theorem wordProd_ρ (w : List Bool) :
    wordProd ρ w = (X : ℚ[X]) ^ w.count true • (wordProd ρq w).map Polynomial.C := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [wordProd_cons, wordProd_cons, ih, Matrix.mul_smul, Matrix.map_mul]
    cases c
    · simp [ρq, ρ_false_eq]
    · simp only [ρq, ite_true, ρ_true_eq, List.count_cons, beq_self_eq_true, Matrix.smul_mul,
        smul_smul, pow_succ]

/-- Coefficients of a weighted constant matrix. -/
theorem coeff_smul_map {n : ℕ} (k : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) (m : ℕ) :
    (((X : ℚ[X]) ^ k • Q.map Polynomial.C) i j).coeff m = if m = k then Q i j else 0 := by
  simp

/-- A word with one letter `b`. -/
theorem eq_of_count_one : ∀ {w : List Bool}, w.count true = 1 →
    ∃ i j, w = List.replicate i false ++ true :: List.replicate j false
  | [], h => by simp at h
  | false :: w, h => by
    obtain ⟨i, j, rfl⟩ := eq_of_count_one (w := w) (by simpa using h)
    exact ⟨i + 1, j, by simp [List.replicate_succ]⟩
  | true :: w, h => by
    have h0 : w.count true = 0 := by simpa using h
    refine ⟨0, w.length, ?_⟩
    simp only [List.replicate_zero, List.nil_append, List.cons.injEq, true_and]
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, fun b hb => ?_⟩
    cases b
    · rfl
    · simp [List.count_eq_zero.mp h0] at hb

theorem A₀q_pow : ∀ k, 2 ≤ k → A₀q ^ k = A₀q ^ 2
  | 2, _ => rfl
  | k + 3, _ => by
    rw [pow_succ, A₀q_pow (k + 2) (by omega)]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [A₀q, sq, Matrix.mul_apply, Fin.sum_univ_three]

theorem Uq_pow : ∀ k, 2 ≤ k → Uq ^ k = 0
  | 2, _ => by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Uq, sq, Matrix.mul_apply, Fin.sum_univ_two]
  | k + 3, _ => by rw [pow_succ, Uq_pow (k + 2) (by omega), zero_mul]

/-- The two cycle traces of a word with one `b` add up to one. -/
theorem trace_sum (k : ℕ) : (B₀q * A₀q ^ k).trace + (Vq * Uq ^ k).trace = 1 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp [B₀q, Vq, Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two]
    · simp [B₀q, A₀q, Vq, Uq, Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two,
        ]
  · rw [A₀q_pow k hk, Uq_pow k hk]
    simp [B₀q, A₀q, Matrix.trace, Fin.sum_univ_three, sq]

theorem wordProd_replicate_false_ψ (i : ℕ) :
    wordProd ψq (List.replicate i false) = A₀q ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [List.replicate_succ, wordProd_cons, ih, pow_succ']; rfl

theorem wordProd_replicate_false_ρ (i : ℕ) :
    wordProd ρq (List.replicate i false) = Uq ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [List.replicate_succ, wordProd_cons, ih, pow_succ']; rfl

theorem trace_one_b (i j : ℕ) :
    (wordProd ψq (List.replicate i false ++ true :: List.replicate j false)).trace +
      (wordProd ρq (List.replicate i false ++ true :: List.replicate j false)).trace = 1 := by
  rw [wordProd_append, wordProd_append, wordProd_cons, wordProd_cons,
    wordProd_replicate_false_ψ, wordProd_replicate_false_ρ, wordProd_replicate_false_ψ,
    wordProd_replicate_false_ρ]
  simp only [ψq, ρq, ite_true]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_add, Matrix.trace_mul_comm (Uq ^ i),
    Matrix.mul_assoc, ← pow_add, add_comm j i]
  exact trace_sum (i + j)

/-- The letter `b` read at `X = 1` by `χL`. -/
theorem wordProd_χL_eval_one (w : List Bool) :
    ((wordProd χL w) 0 1).eval 1 = if w.count true = 1 then 1 else 0 := by
  have hmap : ∀ w : List Bool, (wordProd χL w).map (Polynomial.evalRingHom 1) =
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ^ w.count true := by
    intro w
    induction w with
    | nil => simp
    | cons c w ih =>
      rw [wordProd_cons, Matrix.map_mul, ih]
      cases c
      · have : (χL false).map (Polynomial.eval 1) = 1 := by
          refine Matrix.ext fun i j => ?_
          fin_cases i <;> fin_cases j <;> simp [χL]
        rw [Polynomial.coe_evalRingHom, this, one_mul]
        simp
      · have : (χL true).map (Polynomial.eval 1) = !![0, 1; 0, 0] := by
          refine Matrix.ext fun i j => ?_
          fin_cases i <;> fin_cases j <;> simp [χL]
        rw [Polynomial.coe_evalRingHom, this]
        simp [pow_succ']
  have := congrArg (fun P => P 0 1) (hmap w)
  simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
  rw [this]
  rcases Nat.lt_trichotomy (w.count true) 1 with h | h | h
  · have h0 : w.count true = 0 := by omega
    rw [h0]
    simp
  · simp [h]
  · have hz : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ^ w.count true = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, w.count true = k + 2 := ⟨w.count true - 2, by omega⟩
      rw [hk, pow_add, sq]
      have : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 1; 0, 0] = 0 := by
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, mul_zero]
    rw [hz, ite_eq_right (by omega)]
    rfl

/-- **The word identity.** For every word, the linear coefficients of the traces of `ψ` and `ρ`
add up to the coefficient read by `χL` at `X = 1`. -/
theorem word_identity (w : List Bool) :
    ((wordProd ψ w).map (fun p => p.coeff 1)).trace + ((wordProd ρ w).map (fun p => p.coeff 1)).trace =
      ((wordProd χL w) 0 1).eval 1 := by
  rw [wordProd_χL_eval_one]
  have hψ : (wordProd ψ w).map (fun p => p.coeff 1) =
      if w.count true = 1 then wordProd ψq w else 0 := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, wordProd_ψ, coeff_smul_map]
    by_cases h : w.count true = 1
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (fun e => h e.symm), ite_eq_right h]
      rfl
  have hρ : (wordProd ρ w).map (fun p => p.coeff 1) =
      if w.count true = 1 then wordProd ρq w else 0 := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, wordProd_ρ, coeff_smul_map]
    by_cases h : w.count true = 1
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (fun e => h e.symm), ite_eq_right h]
      rfl
  rw [hψ, hρ]
  split_ifs with h
  · obtain ⟨i, j, rfl⟩ := eq_of_count_one h
    exact trace_one_b i j
  · simp

end SmallestNoncompletable
