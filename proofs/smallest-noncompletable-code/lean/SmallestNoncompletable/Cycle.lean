module

public import SmallestNoncompletable.Traces
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # The cycle of `ab`

The words readable on the cycle of `ab` are the factors of `(ab)^ℤ`. From vertex `0` (before
`a`) to vertex `0` with `n` letters `b` the word is `(ab)ⁿ`, to vertex `1` it is `(ab)ⁿ a`; from
vertex `1` to vertex `0` it is `b (ab)ⁿ⁻¹`, and to vertex `1` it is `(ba)ⁿ`.

For a series `G` the four generating functions `c₀₀ G`, … record its coefficients on these
words. The first column is multiplicative: the cycle words cut at even and odd positions. For a
polynomial, the generating functions are the entries of the evaluation `ρ`. -/

@[expose] public section

namespace SmallestNoncompletable

open Polynomial PowerSeries Ser

/-- `(ba)ⁿ`. -/
def baPow (n : ℕ) : List Bool := (List.replicate n [true, false]).flatten

theorem abPow_add (p q : ℕ) : abPow (p + q) = abPow p ++ abPow q := by
  induction p with
  | zero => simp [abPow]
  | succ p ih => rw [show p + 1 + q = (p + q) + 1 by omega, abPow_succ, abPow_succ, ih]; rfl

@[simp] theorem abPow_zero : abPow 0 = [] := rfl

@[simp] theorem length_abPow (n : ℕ) : (abPow n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [abPow_succ]; simp [ih]; ring

@[simp] theorem count_abPow (n : ℕ) : (abPow n).count true = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [abPow_succ]; simp [ih]

@[simp] theorem baPow_zero : baPow 0 = [] := rfl

theorem baPow_succ (n : ℕ) : baPow (n + 1) = true :: false :: baPow n := by
  simp [baPow, List.replicate_succ]

@[simp] theorem length_baPow (n : ℕ) : (baPow n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [baPow_succ]; simp [ih]; ring

@[simp] theorem count_baPow (n : ℕ) : (baPow n).count true = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [baPow_succ]; simp [ih]

theorem false_cons_baPow (n : ℕ) : false :: baPow n = abPow n ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [baPow_succ, abPow_succ, List.cons_append, List.cons_append, ← ih]

theorem true_cons_abPow (n : ℕ) : true :: abPow n = baPow n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [abPow_succ, baPow_succ, List.cons_append, List.cons_append, ← ih]

/-! ## Words of the cycle -/

theorem Uq_mul (P : Matrix (Fin 2) (Fin 2) ℚ) : Uq * P = !![P 1 0, P 1 1; 0, 0] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Uq, Matrix.mul_apply, Fin.sum_univ_two]

theorem Vq_mul (P : Matrix (Fin 2) (Fin 2) ℚ) : Vq * P = !![0, 0; P 0 0, P 0 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Vq, Matrix.mul_apply, Fin.sum_univ_two]

theorem iff00 (w : List Bool) : false :: w = abPow (w.count true) ↔
    (1 ≤ w.count true ∧ w = true :: abPow (w.count true - 1)) := by
  rcases Nat.eq_zero_or_pos (w.count true) with h | h
  · rw [h]; simp
  · obtain ⟨k, hk⟩ : ∃ k, w.count true = k + 1 := ⟨w.count true - 1, by omega⟩
    rw [hk, abPow_succ]
    simp

theorem iff01 (w : List Bool) : false :: w = abPow (w.count true) ++ [false] ↔
    w = baPow (w.count true) := by
  rw [← false_cons_baPow]
  simp

theorem false_ne_baPow (w : List Bool) (n : ℕ) : false :: w ≠ baPow n := by
  cases n with
  | zero => simp
  | succ n => rw [baPow_succ]; simp

theorem true_ne_abPow (w : List Bool) (n : ℕ) : true :: w ≠ abPow n := by
  cases n with
  | zero => simp
  | succ n => rw [abPow_succ]; simp

theorem true_ne_abPow_false (w : List Bool) (n : ℕ) : true :: w ≠ abPow n ++ [false] := by
  cases n with
  | zero => simp
  | succ n => rw [abPow_succ]; simp

/-- The products of the unweighted cycle letters are the elementary matrices of the cycle
words. -/
theorem wordProd_ρq (w : List Bool) :
    wordProd ρq w 0 0 = (if w = abPow (w.count true) then 1 else 0) ∧
    wordProd ρq w 0 1 = (if w = abPow (w.count true) ++ [false] then 1 else 0) ∧
    wordProd ρq w 1 0 =
      (if 1 ≤ w.count true ∧ w = true :: abPow (w.count true - 1) then 1 else 0) ∧
    wordProd ρq w 1 1 = (if w = baPow (w.count true) then 1 else 0) := by
  induction w with
  | nil => simp [abPow, baPow]
  | cons c w ih =>
    obtain ⟨h00, h01, h10, h11⟩ := ih
    rw [wordProd_cons]
    cases c
    · have hc : (false :: w).count true = w.count true := by simp
      simp only [ρq, Bool.false_eq_true, ite_false, Uq_mul, hc]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h10]
        exact if_congr (iff00 w).symm rfl rfl
      · rw [h11]
        exact if_congr (iff01 w).symm rfl rfl
      · rw [ite_eq_right]
        rintro ⟨_, h⟩
        simp at h
      · rw [ite_eq_right]
        exact false_ne_baPow w _
    · have hc : (true :: w).count true = w.count true + 1 := by simp
      simp only [ρq, ite_true, Vq_mul, hc]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ite_eq_right]
        exact true_ne_abPow w _
      · rw [ite_eq_right]
        exact true_ne_abPow_false w _
      · rw [h00]
        exact if_congr (by simp) rfl rfl
      · rw [h01, baPow_succ, ← false_cons_baPow]
        exact if_congr (by simp) rfl rfl

/-! ## Generating functions on the cycle -/

/-- Coefficients on `(ab)ⁿ`. -/
noncomputable def c00 (G : Ser Bool ℚ) : ℚ⟦X⟧ := PowerSeries.mk fun n => G.coeff (abPow n)

/-- Coefficients on `(ab)ⁿ a`. -/
noncomputable def c01 (G : Ser Bool ℚ) : ℚ⟦X⟧ := PowerSeries.mk fun n => G.coeff (abPow n ++ [false])

/-- Coefficients on `b (ab)ⁿ⁻¹`. -/
noncomputable def c10 (G : Ser Bool ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else G.coeff (true :: abPow (n - 1))

/-- Coefficients on `(ba)ⁿ`. -/
noncomputable def c11 (G : Ser Bool ℚ) : ℚ⟦X⟧ := PowerSeries.mk fun n => G.coeff (baPow n)

/-- A sum over an even range splits into even and odd indices. -/
theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ p ∈ Finset.range n, (f (2 * p) + f (2 * p + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

theorem take_drop_abPow {n p : ℕ} (hp : p ≤ n) :
    (abPow n).take (2 * p) = abPow p ∧ (abPow n).drop (2 * p) = abPow (n - p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [abPow_add]
  constructor
  · rw [List.take_left' (by simp)]
  · rw [List.drop_left' (by simp)]
    congr 1
    omega

theorem take_drop_abPow_odd {n p : ℕ} (hp : p < n) :
    (abPow n).take (2 * p + 1) = abPow p ++ [false] ∧
      (abPow n).drop (2 * p + 1) = true :: abPow (n - p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = p + (q + 1) := ⟨n - p - 1, by omega⟩
  rw [abPow_add, abPow_succ]
  constructor
  · rw [show abPow p ++ false :: true :: abPow q = (abPow p ++ [false]) ++ true :: abPow q by
      simp, List.take_left' (by simp)]
  · rw [show abPow p ++ false :: true :: abPow q = (abPow p ++ [false]) ++ true :: abPow q by
      simp, List.drop_left' (by simp)]
    congr 2
    omega

/-- The coefficient of `(ab)ⁿ` in a product. -/
theorem c00_mul (G F : Ser Bool ℚ) : c00 (G * F) = c00 G * c00 F + c01 G * c10 F := by
  ext n
  rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [c00, c01, c10, PowerSeries.coeff_mk]
  rw [Ser.coeff_mul, length_abPow, Finset.sum_range_succ, sum_range_even_odd]
  have h1 : ∀ p ∈ Finset.range n, G.coeff ((abPow n).take (2 * p)) * F.coeff ((abPow n).drop
      (2 * p)) = G.coeff (abPow p) * F.coeff (abPow (n - p)) := by
    intro p hp
    obtain ⟨e1, e2⟩ := take_drop_abPow (n := n) (p := p) (by simp at hp; omega)
    rw [e1, e2]
  have h2 : ∀ p ∈ Finset.range n, G.coeff ((abPow n).take (2 * p + 1)) *
      F.coeff ((abPow n).drop (2 * p + 1)) =
      G.coeff (abPow p ++ [false]) * (if n - p = 0 then 0 else F.coeff (true :: abPow (n - p - 1))) := by
    intro p hp
    have hp' : p < n := by simpa using hp
    obtain ⟨e1, e2⟩ := take_drop_abPow_odd hp'
    rw [e1, e2, ite_eq_right (by omega)]
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [Finset.sum_range_succ (fun p => G.coeff (abPow p) * F.coeff (abPow (n - p))),
    Finset.sum_range_succ (fun p => G.coeff (abPow p ++ [false]) *
      (if n - p = 0 then 0 else F.coeff (true :: abPow (n - p - 1))))]
  have e3 : (abPow n).take (2 * n) = abPow n := List.take_of_length_le (by simp)
  have e4 : (abPow n).drop (2 * n) = [] := List.drop_of_length_le (by simp)
  rw [e3, e4]
  simp only [Nat.sub_self, ite_true, mul_zero, add_zero, abPow_zero]
  ring

theorem take_drop_ba {m p : ℕ} (hp : p ≤ m) :
    (true :: abPow m).take (2 * p) = baPow p ∧
      (true :: abPow m).drop (2 * p) = true :: abPow (m - p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have e : true :: abPow (p + q) = baPow p ++ true :: abPow q := by
    rw [abPow_add, ← List.cons_append, true_cons_abPow, List.append_assoc, List.singleton_append]
  rw [e]
  constructor
  · rw [List.take_left' (by simp)]
  · rw [List.drop_left' (by simp)]
    congr 2
    omega

theorem take_drop_ba_odd {m p : ℕ} (hp : p ≤ m) :
    (true :: abPow m).take (2 * p + 1) = true :: abPow p ∧
      (true :: abPow m).drop (2 * p + 1) = abPow (m - p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [abPow_add, ← List.cons_append]
  constructor
  · rw [List.take_left' (by simp)]
  · rw [List.drop_left' (by simp)]
    congr 1
    omega

/-- The coefficient of `b (ab)ⁿ⁻¹` in a product. -/
theorem c10_mul (G F : Ser Bool ℚ) : c10 (G * F) = c10 G * c00 F + c11 G * c10 F := by
  ext n
  rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [c00, c11, c10, PowerSeries.coeff_mk]
  rcases n with _ | m
  · simp
  simp only [add_eq_zero, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
  rw [Ser.coeff_mul, List.length_cons, length_abPow, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
    sum_range_even_odd, Finset.sum_add_distrib]
  -- Odd cuts: the left factor is `b (ab)ᵖ`.
  have h1 : ∀ p ∈ Finset.range (m + 1), G.coeff ((true :: abPow m).take (2 * p + 1)) *
      F.coeff ((true :: abPow m).drop (2 * p + 1)) =
      (if p + 1 = 0 then 0 else G.coeff (true :: abPow (p + 1 - 1))) * F.coeff (abPow (m + 1 - (p + 1))) := by
    intro p hp
    obtain ⟨e1, e2⟩ := take_drop_ba_odd (m := m) (p := p) (by simp at hp; omega)
    rw [e1, e2, ite_eq_right (by omega), Nat.add_sub_cancel, Nat.add_sub_add_right]
  -- Even cuts: the left factor is `(ba)ᵖ`.
  have h2 : ∀ p ∈ Finset.range (m + 1), G.coeff ((true :: abPow m).take (2 * p)) *
      F.coeff ((true :: abPow m).drop (2 * p)) =
      G.coeff (baPow p) * (if m + 1 - p = 0 then 0 else F.coeff (true :: abPow (m + 1 - p - 1))) := by
    intro p hp
    obtain ⟨e1, e2⟩ := take_drop_ba (m := m) (p := p) (by simp at hp; omega)
    rw [e1, e2, ite_eq_right (by simp at hp; omega), show m + 1 - p - 1 = m - p by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_range_succ' (fun p => (if p = 0 then 0 else G.coeff (true :: abPow (p - 1))) *
      F.coeff (abPow (m + 1 - p))) (m + 1)]
  rw [ite_eq_left rfl, zero_mul, add_zero]
  rw [Finset.sum_range_succ (fun p => G.coeff (baPow p) *
      (if m + 1 - p = 0 then 0 else F.coeff (true :: abPow (m + 1 - p - 1)))) (m + 1)]
  rw [Nat.sub_self, ite_eq_left rfl, mul_zero, add_zero, add_comm]

end SmallestNoncompletable
