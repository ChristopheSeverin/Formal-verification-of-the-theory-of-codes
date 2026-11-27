module

public import SmallestNoncompletable.Cycle
public import SmallestNoncompletable.Factorization
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # The side of the factorization that carries the period

Let `A* = N M* J` with `J` having no pure power of `b` except `1`. Put `F(w) = 1` when
`w bᴷ ∈ M*`, for `K` larger than the degree of `J`. Then `N F` and the series of all words agree
on long words. Along the cycle of `ab`, `F((ab)ⁿ)` is one exactly for even `n`, so its generating
function is `1/(1 - X²)`. The adjugate of the evaluation `ρ(N)` then shows that `1 + X` divides
its determinant. -/

@[expose] public section

namespace SmallestNoncompletable

open Polynomial PowerSeries Ser InformationTheory

/-- A sum over the words of bounded length that selects one word. -/
theorem sum_wordsUpTo_select {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) (t : List Bool) :
    ∑ w ∈ wordsUpTo d, N.coeff w * (if w = t then 1 else 0) = N.coeff t := by
  by_cases ht : t.length ≤ d
  · rw [Finset.sum_eq_single t]
    · simp
    · intro w _ hwt; simp [hwt]
    · intro h; exact absurd (mem_wordsUpTo.mpr ht) h
  · rw [hN t (by omega)]
    refine Finset.sum_eq_zero fun w hw => ?_
    have : w ≠ t := by rintro rfl; exact ht (mem_wordsUpTo.mp hw)
    simp [this]

theorem coeff_evalRec_ρ {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) (i j : Fin 2) (n : ℕ) :
    ((evalRec ρ d N) i j).coeff n = ∑ w ∈ wordsUpTo d,
      N.coeff w * (if n = w.count true then wordProd ρq w i j else 0) := by
  rw [evalRec_eq_sum ρ hN, Matrix.sum_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_apply, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]
  change N.coeff w * (wordProd ρ w i j).coeff n = _
  rw [wordProd_ρ, coeff_smul_map]

theorem c00_poly {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) :
    c00 N = (((evalRec ρ d N) 0 0 : ℚ[X]) : ℚ⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_evalRec_ρ hN, c00, PowerSeries.coeff_mk,
    ← sum_wordsUpTo_select hN (abPow n)]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [(wordProd_ρq w).1]
  by_cases h : w = abPow n
  · subst h; simp
  · rw [ite_eq_right h]
    split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h2 h)

theorem c01_poly {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) :
    c01 N = (((evalRec ρ d N) 0 1 : ℚ[X]) : ℚ⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_evalRec_ρ hN, c01, PowerSeries.coeff_mk,
    ← sum_wordsUpTo_select hN (abPow n ++ [false])]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [(wordProd_ρq w).2.1]
  by_cases h : w = abPow n ++ [false]
  · subst h; simp
  · rw [ite_eq_right h]
    split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h2 h)

theorem c10_poly {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) :
    c10 N = (((evalRec ρ d N) 1 0 : ℚ[X]) : ℚ⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_evalRec_ρ hN, c10, PowerSeries.coeff_mk]
  rcases n with _ | n
  · refine (Finset.sum_eq_zero fun w _ => ?_).symm
    rw [(wordProd_ρq w).2.2.1]
    by_cases h1 : 0 = w.count true
    · rw [ite_eq_left h1, ite_eq_right (fun h2 => by omega), mul_zero]
    · rw [ite_eq_right h1, mul_zero]
  · rw [ite_eq_right (by omega), Nat.add_sub_cancel,
      ← sum_wordsUpTo_select hN (true :: abPow n)]
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    rw [(wordProd_ρq w).2.2.1]
    by_cases h : w = true :: abPow n
    · subst h; simp
    · rw [ite_eq_right h]
      by_cases h1 : n + 1 = w.count true
      · rw [ite_eq_left h1, ite_eq_right]
        rintro ⟨-, h3⟩
        rw [← h1, Nat.add_sub_cancel] at h3
        exact h h3
      · rw [ite_eq_right h1]

theorem c11_poly {N : Ser Bool ℚ} {d : ℕ} (hN : DegLE N d) :
    c11 N = (((evalRec ρ d N) 1 1 : ℚ[X]) : ℚ⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_evalRec_ρ hN, c11, PowerSeries.coeff_mk,
    ← sum_wordsUpTo_select hN (baPow n)]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [(wordProd_ρq w).2.2.2]
  by_cases h : w = baPow n
  · subst h; simp
  · rw [ite_eq_right h]
    split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h2 h)

/-- An eventually constant power series becomes a polynomial after multiplication by `1 - X`. -/
theorem exists_poly_of_eventually_one {f : ℚ⟦X⟧} {n₀ : ℕ}
    (hf : ∀ n, n₀ ≤ n → PowerSeries.coeff n f = 1) :
    ∃ g : ℚ[X], (1 - PowerSeries.X) * f = (g : ℚ⟦X⟧) := by
  refine ⟨PowerSeries.trunc (n₀ + 1) ((1 - PowerSeries.X) * f), ?_⟩
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [sub_mul, one_mul, map_sub]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [PowerSeries.coeff_succ_X_mul, hf _ (by omega), hf _ (by omega), sub_self]

/-- `(ab)ⁿ bᴷ ∈ M*` for even `n`. -/
theorem abPow_even_mem {M : Set (List Bool)} (hX : Xcode ⊆ M) {n : ℕ} (hn : Even n) (K : ℕ) :
    abPow n ++ List.replicate K true ∈ Star M := by
  obtain ⟨q, rfl⟩ := hn
  rw [show q + q = 2 * q by ring, abPow_two_mul]
  exact append_mem_star (replicate_mem_star (hX (by simp [Xcode])) q)
    (replicate_letter_mem_star (hX (by simp [Xcode])) K)

/-- **The period argument.** -/
theorem one_add_X_dvd_det {M : Set (List Bool)} (hX : Xcode ⊆ M) {J N : Ser Bool ℚ}
    {dJ dN : ℕ} (hJ : DegLE J dJ) (hN : DegLE N dN)
    (hall : allWords = N * Ser.char (Star M) * J)
    (hJb : ∀ k, J.coeff (List.replicate k true) = if k = 0 then 1 else 0)
    (hpar : ∀ n K, abPow n ++ List.replicate K true ∈ Star M → Even n) :
    ∃ G : ℚ[X], (evalRec ρ dN N).det = (1 + Polynomial.X) * G := by
  classical
  set τ : Ser Bool ℚ := Ser.char (Star M)
  set K := dJ + 1
  set F : Ser Bool ℚ := ⟨fun w => τ.coeff (w ++ List.replicate K true)⟩ with hFdef
  have hJ0 : J.coeff [] = 1 := by simpa using hJb 0
  -- `N F` is one on long words.
  have hNF : ∀ w : List Bool, dN ≤ w.length → (N * F).coeff w = 1 := by
    intro w hw
    set u := w ++ List.replicate K true with hu
    have hulen : u.length = w.length + K := by simp [hu]
    have h1 : (N * τ * J).coeff u = 1 := by rw [← hall]; rfl
    have h2 : (N * τ * J).coeff u = (N * τ).coeff u := by
      rw [Ser.coeff_mul, Finset.sum_range_succ, List.take_length, List.drop_length, hJ0,
        mul_one, Finset.sum_eq_zero, zero_add]
      intro i hi
      have hi := Finset.mem_range.mp hi
      apply mul_eq_zero_of_right
      by_cases hiw : i ≤ w.length
      · apply hJ
        rw [List.length_drop, hulen]
        omega
      · rw [hu, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          List.drop_replicate, hJb, ite_eq_right (by omega)]
    have hsub : Finset.range (w.length + 1) ⊆ Finset.range (u.length + 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have h3 : (N * τ).coeff u = (N * F).coeff w := by
      rw [Ser.coeff_mul, Ser.coeff_mul]
      calc ∑ i ∈ Finset.range (u.length + 1), N.coeff (u.take i) * τ.coeff (u.drop i)
          = ∑ i ∈ Finset.range (w.length + 1), N.coeff (u.take i) * τ.coeff (u.drop i) := by
            refine (Finset.sum_subset hsub fun i hi hni => ?_).symm
            simp only [Finset.mem_range, not_lt] at hi hni
            apply mul_eq_zero_of_left
            apply hN
            rw [List.length_take]
            omega
        _ = ∑ i ∈ Finset.range (w.length + 1), N.coeff (w.take i) * F.coeff (w.drop i) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi := Finset.mem_range.mp hi
            rw [hu, List.take_append_of_le_length (by omega),
              List.drop_append_of_le_length (by omega)]
    rw [← h3, ← h2, h1]
  -- The generating function of `F` on `(ab)ⁿ`.
  set e : ℚ⟦X⟧ := PowerSeries.mk fun n => if Even n then (1 : ℚ) else 0 with he_def
  have hF0 : c00 F = e := by
    ext n
    simp only [c00, PowerSeries.coeff_mk, hFdef, he_def]
    by_cases hn : Even n
    · rw [ite_eq_left hn, coeff_char_of_mem (abPow_even_mem hX hn K)]
    · rw [ite_eq_right hn, coeff_char_of_notMem (fun h => hn (hpar n K h))]
  have he : (1 - PowerSeries.X ^ 2) * e = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one,
      he_def, PowerSeries.coeff_mk]
    rcases n with _ | _ | n
    · simp
    · simp
    · have h2 : 2 ≤ n + 1 + 1 := by omega
      have hev : Even (n + 1 + 1) ↔ Even n := by
        rw [Nat.even_add_one, Nat.even_add_one, not_not]
      simp only [PowerSeries.coeff_mk, h2, ite_true, show n + 1 + 1 - 2 = n by omega,
        add_eq_zero, one_ne_zero, and_false, ite_false]
      by_cases hn : Even n
      · rw [ite_eq_left (hev.mpr hn), ite_eq_left hn, sub_self]
      · rw [ite_eq_right (fun h => hn (hev.mp h)), ite_eq_right hn, sub_self]
  -- The two generating functions of `N F` are eventually one.
  obtain ⟨g0, hg0⟩ := exists_poly_of_eventually_one (f := c00 (N * F)) (n₀ := dN)
    fun n hn => by
      simp only [c00, PowerSeries.coeff_mk]
      exact hNF _ (by simp; omega)
  obtain ⟨g1, hg1⟩ := exists_poly_of_eventually_one (f := c10 (N * F)) (n₀ := dN + 1)
    fun n hn => by
      simp only [c10, PowerSeries.coeff_mk]
      rw [ite_eq_right (by omega)]
      exact hNF _ (by simp; omega)
  rw [c00_mul, c00_poly hN, c01_poly hN, hF0] at hg0
  rw [c10_mul, c10_poly hN, c11_poly hN, hF0] at hg1
  set P := evalRec ρ dN N
  refine ⟨P 1 1 * g0 - P 0 1 * g1, Polynomial.coe_inj.mp ?_⟩
  rw [Matrix.det_fin_two]
  simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X]
  rw [← hg0, ← hg1]
  calc (↑(P 0 0) * ↑(P 1 1) - ↑(P 0 1) * ↑(P 1 0) : ℚ⟦X⟧)
      = (↑(P 0 0) * ↑(P 1 1) - ↑(P 0 1) * ↑(P 1 0)) * ((1 - PowerSeries.X ^ 2) * e) := by
        rw [he, mul_one]
    _ = (1 + PowerSeries.X) * (↑(P 1 1) * ((1 - PowerSeries.X) * (↑(P 0 0) * e + ↑(P 0 1) * c10 F)) -
          ↑(P 0 1) * ((1 - PowerSeries.X) * (↑(P 1 0) * e + ↑(P 1 1) * c10 F))) := by ring

end SmallestNoncompletable
