module

public import SmallestNoncompletable.Period
public import SmallestNoncompletable.Complete
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! # No finite maximal code contains `{aa, abab, baaa, b}`

Over the binary alphabet, let `M` be a finite code containing `X = {aa, abab, baaa, b}` such
that `bᴺ w bᴺ ∈ M*` for every word `w`. The weak factorization and the factorization theorem
give `1 - M = J (1 - a - b) N` with polynomials normalized at the empty word. Then

* `a ↦ 0, b ↦ X` shows that the only power of `b` in `J` is the empty word;
* `χR` shows that the only power of `a` in `J` is the empty word, and `σa` gives the powers of
  `a` in `N`;
* `χL` shows that the coefficients of `J` on the words with one `b` add up to one;
* `ψ` shows that `det ψ(J) = 1`, and the period argument shows `det ρ(J) = 1`;
* the linear coefficients of these determinants add up to the sum read by `χL`, a
  contradiction.

A finite maximal code over any alphabet containing two letters `a ≠ b` and the four words
restricts to such a code. -/

@[expose] public section

namespace SmallestNoncompletable

open Polynomial Ser InformationTheory

section Binary

variable {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hfin : M.Finite) (hX : Xcode ⊆ M)
  {N₀ : ℕ} (hsync : ∀ w, List.replicate N₀ true ++ w ++ List.replicate N₀ true ∈ Star M)
include hM hfin hX hsync

/-- The normalized factorization `1 - M = J B N`. -/
theorem exists_factorization : ∃ J N : Ser Bool ℚ, IsPoly J ∧ IsPoly N ∧
    J.coeff [] = 1 ∧ N.coeff [] = 1 ∧ 1 - Ser.char M = J * B * N := by
  set τ : Ser Bool ℚ := Ser.char (Star M)
  set m : Ser Bool ℚ := Ser.char M
  have hm : IsPoly m := IsPoly.char hfin
  have hm0 : m.coeff [] = 0 := coeff_char_of_notMem hM.epsilon_notMem
  have h1 : τ = 1 + m * τ := star_eq_one_add_mul hM
  have h2 : τ = 1 + τ * m := star_eq_one_add_mul' hM
  have hb : [true] ∈ M := hX (by simp [Xcode])
  have hstarN : List.replicate N₀ true ∈ Star M := replicate_letter_mem_star hb N₀
  obtain ⟨R₁, S₁, P, hR, hS, hP, hweak, -, hP0, hR0⟩ :=
    weak_factorization hm hm0 h1 h2 (u := List.replicate N₀ true) (v := List.replicate N₀ true)
      fun w => coeff_char_of_mem (hsync w)
  rw [coeff_char_of_mem hstarN] at hP0 hR0
  have hstar : τ * (1 - m) = 1 := by
    rw [mul_sub, mul_one]
    nth_rw 1 [h2]
    abel
  obtain ⟨J, N, hJ, hN, e⟩ := factorization_of_weak hm hR hS hP (by rw [hR0]; ring) hP0 hstar
    hweak
  obtain ⟨-, e', hJ1, hN1⟩ := normalize_factorization hm0 e
  exact ⟨_, _, hJ.smul _, hN.smul _, hJ1, hN1, e'⟩

end Binary

/-- Evaluation of a factorization `1 - M = J B N`. -/
theorem evalRec_factorization {S : Type*} [Ring S] [Algebra ℚ S] (x : Bool → S)
    {m J N : Ser Bool ℚ} {dJ dN : ℕ} (hJ : DegLE J dJ) (hN : DegLE N dN)
    (h : 1 - m = J * (B : Ser Bool ℚ) * N) :
    1 - evalRec x (dJ + 1 + dN) m = evalRec x dJ J * evalRec x 1 (B : Ser Bool ℚ) * evalRec x dN N := by
  have hB : DegLE (B : Ser Bool ℚ) 1 := by
    intro w hw
    rw [coeff_B]
    have h1 : w ≠ [] := by rintro rfl; simp at hw
    have h2 : w ≠ [false] := by rintro rfl; simp at hw
    have h3 : w ≠ [true] := by rintro rfl; simp at hw
    simp [h1, h2, h3]
  rw [← evalRec_mul x hJ hB, ← evalRec_mul x (hJ.mul hB) hN, ← h, evalRec_sub, evalRec_one]

/-- A polynomial with an inverse is its constant coefficient. -/
theorem eq_C_of_mul_eq_one {p q : ℚ[X]} (h : p * q = 1) : p = Polynomial.C (p.coeff 0) := by
  obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp (IsUnit.of_mul_eq_one q h)
  simp

theorem one_sub_X_ne_zero : (1 - X : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp at this

theorem one_add_X_ne_zero : (1 + X : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp at this

theorem X_ne_zero' : (X : ℚ[X]) ≠ 0 := Polynomial.X_ne_zero

/-- The evaluation at `X = 0` of a representation whose letter `b` carries the weight `X`. -/
theorem evalRec_at_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Bool → Matrix (Fin n) (Fin n) ℚ[X])
    (hx : ∀ c, (x c).map (Polynomial.eval 0) = if c then 0 else A) (d : ℕ) (f : Ser Bool ℚ) :
    (evalRec x d f).map (Polynomial.eval 0) = Polynomial.aeval A (evalRec σa d f) := by
  have h1 := evalRec_map x (Polynomial.aeval (0 : ℚ)).mapMatrix d f
  have h2 := evalRec_map σa (Polynomial.aeval A) d f
  have e : (fun c => (Polynomial.aeval (0 : ℚ)).mapMatrix (x c)) =
      fun c => Polynomial.aeval A (σa c) := by
    funext c
    have := hx c
    cases c <;> simp_all [σa, AlgHom.mapMatrix_apply, Polynomial.coe_aeval_eq_eval]
  rw [h2, ← e, ← h1]
  simp [AlgHom.mapMatrix_apply, Polynomial.coe_aeval_eq_eval]

/-- If the series of `J` on the powers of `a` is `1`, its evaluation is the identity at `X = 0`. -/
theorem coeff_zero_of_pure_a {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (x : Bool → Matrix (Fin n) (Fin n) ℚ[X])
    (hx : ∀ c, (x c).map (Polynomial.eval 0) = if c then 0 else A) {d : ℕ} {J : Ser Bool ℚ}
    (hJa : evalRec σa d J = 1) :
    (∀ i j, ((evalRec x d J) i j).coeff 0 = if i = j then 1 else 0) ∧
      ((evalRec x d J).det).coeff 0 = 1 := by
  have h := evalRec_at_zero A x hx d J
  rw [hJa, map_one] at h
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    have := congrArg (fun P => P i j) h
    simp only [Matrix.map_apply] at this
    rw [this, Matrix.one_apply]
  · rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det,
      RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, h, Matrix.det_one]

/-- The coefficient of `X` in an entry of an evaluation. -/
theorem coeff_entry {n : ℕ} (x : Bool → Matrix (Fin n) (Fin n) ℚ[X]) {d : ℕ} {J : Ser Bool ℚ}
    (hJ : DegLE J d) (i j : Fin n) (k : ℕ) :
    ((evalRec x d J) i j).coeff k = ∑ w ∈ wordsUpTo d, J.coeff w * ((wordProd x w) i j).coeff k := by
  rw [evalRec_eq_sum x hJ, Matrix.sum_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_apply, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]
  rfl

/-- The value at `X = 1` of an entry of an evaluation. -/
theorem eval_entry {n : ℕ} (x : Bool → Matrix (Fin n) (Fin n) ℚ[X]) {d : ℕ} {J : Ser Bool ℚ}
    (hJ : DegLE J d) (i j : Fin n) :
    ((evalRec x d J) i j).eval 1 = ∑ w ∈ wordsUpTo d, J.coeff w * ((wordProd x w) i j).eval 1 := by
  rw [evalRec_eq_sum x hJ, Matrix.sum_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_apply, Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  rfl

theorem χR_diag : (fun c => χR c 0 0) = σa ∧ (fun c => χR c 1 1) = fun c => if c then 0 else 1 := by
  constructor <;> funext c <;> cases c <;> rfl

theorem χL_diag : (fun c => χL c 0 0) = (fun c => if c then 0 else 1) ∧ (fun c => χL c 1 1) = σa := by
  constructor <;> funext c <;> cases c <;> rfl

theorem χR_lower (c : Bool) : χR c 1 0 = 0 := by cases c <;> rfl
theorem χL_lower (c : Bool) : χL c 1 0 = 0 := by cases c <;> rfl

/-- `a ↦ 1, b ↦ 0` is the evaluation of `σa` at `1`. -/
theorem evalRec_a_one (d : ℕ) (J : Ser Bool ℚ) :
    evalRec (fun c => if c then (0 : ℚ[X]) else 1) d J = Polynomial.aeval (1 : ℚ[X]) (evalRec σa d J) := by
  rw [evalRec_map σa (Polynomial.aeval (1 : ℚ[X])) d J]
  congr 1
  funext c
  cases c <;> simp [σa]

theorem degLE_B : DegLE (B : Ser Bool ℚ) 1 := by
  intro w hw
  rw [coeff_B]
  have h1 : w ≠ [] := by rintro rfl; simp at hw
  have h2 : w ≠ [false] := by rintro rfl; simp at hw
  have h3 : w ≠ [true] := by rintro rfl; simp at hw
  simp [h1, h2, h3]

/-- A polynomial dividing a nonzero constant is constant. -/
theorem eq_C_of_mul_eq_C {p q : ℚ[X]} {c : ℚ} (hc : c ≠ 0) (h : p * q = Polynomial.C c) :
    p = Polynomial.C (p.coeff 0) := by
  refine eq_C_of_mul_eq_one (q := Polynomial.C c⁻¹ * q) ?_
  rw [mul_left_comm, h, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]

/-- Sum over the words of the linear coefficients of the traces. -/
theorem sum_trace_coeff {n : ℕ} (x : Bool → Matrix (Fin n) (Fin n) ℚ[X]) {d : ℕ}
    {J : Ser Bool ℚ} (hJ : DegLE J d) :
    ∑ w ∈ wordsUpTo d, J.coeff w * ((wordProd x w).map (fun p => p.coeff 1)).trace =
      ((evalRec x d J).map (fun p => p.coeff 1)).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (coeff_entry x hJ i i 1).symm

theorem ψ_at_zero (c : Bool) : (ψ c).map (Polynomial.eval 0) = if c then 0 else A₀q := by
  cases c <;> refine Matrix.ext fun i j => ?_ <;> fin_cases i <;> fin_cases j <;>
    simp [ψ, A₀, B₀, A₀q]

theorem ρ_at_zero (c : Bool) : (ρ c).map (Polynomial.eval 0) = if c then 0 else Uq := by
  cases c <;> refine Matrix.ext fun i j => ?_ <;> fin_cases i <;> fin_cases j <;>
    simp [ρ, Uq]

/-- **No finite binary code containing `{aa, abab, baaa, b}` is synchronized by a power of `b`.** -/
theorem no_binary_code {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hfin : M.Finite)
    (hX : Xcode ⊆ M) {N₀ : ℕ}
    (hsync : ∀ w, List.replicate N₀ true ++ w ++ List.replicate N₀ true ∈ Star M) : False := by
  classical
  obtain ⟨J, N, ⟨dJ, hJ⟩, ⟨dN, hN⟩, hJ0, hN0, e⟩ := exists_factorization hM hfin hX hsync
  have hD : ∀ w ∈ M, w.length ≤ dJ + 1 + dN := by
    intro w hw
    by_contra hlt
    push Not at hlt
    have hdeg : DegLE (1 - Ser.char M : Ser Bool ℚ) (dJ + 1 + dN) := by
      rw [e]; exact (hJ.mul degLE_B).mul hN
    have := hdeg w hlt
    rw [Ser.coeff_sub, coeff_one_of_ne_nil (by rintro rfl; simp at hlt),
      coeff_char_of_mem hw] at this
    norm_num at this
  -- (1) The only power of `b` in `J` is the empty word.
  have hσb : evalRec σb dJ J = 1 := by
    have h := evalRec_factorization σb hJ hN e
    rw [evalRec_σb_char hM hX hfin hD, evalRec_B σb le_rfl,
      show σb false = 0 from rfl, show σb true = X from rfl, sub_zero] at h
    have hprod : evalRec σb dJ J * evalRec σb dN N = 1 := by
      apply mul_left_cancel₀ one_sub_X_ne_zero
      linear_combination -h
    rw [eq_C_of_mul_eq_one hprod, coeff_evalRec_σb dJ J 0 (Nat.zero_le _)]
    simp [hJ0]
  have hJb : ∀ k, J.coeff (List.replicate k true) = if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k ≤ dJ
    · rw [← coeff_evalRec_σb dJ J k hk, hσb, Polynomial.coeff_one]
    · rw [hJ _ (by simp; omega), ite_eq_right (by omega)]
  -- (2) The only power of `a` in `J` is the empty word.
  have hσaJ : evalRec σa dJ J = 1 := by
    have h := evalRec_factorization χR hJ hN e
    rw [evalRec_χR_char hM hX hfin hD] at h
    have hB : evalRec χR 1 (B : Ser Bool ℚ) = !![1 - X, -1; 0, 0] := by
      rw [evalRec_B _ le_rfl]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [χR]
    have hJ00 : evalRec χR dJ J 0 0 = evalRec σa dJ J := by
      rw [(evalRec_upper χR χR_lower dJ J).2.1, χR_diag.1]
    have h01 := congrArg (fun P => P 0 1) h
    rw [hB] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two, hJ00] at h01
    have hprod : evalRec σa dJ J * ((1 - X) * evalRec χR dN N 0 1 - evalRec χR dN N 1 1) =
        Polynomial.C (-2) := by
      rw [Polynomial.C_neg, map_ofNat]
      linear_combination -h01
    rw [eq_C_of_mul_eq_C (by norm_num) hprod, coeff_zero_evalRec_σa, hJ0, map_one]
  -- (3) The powers of `a` in `N`.
  have hσaN : evalRec σa dN N = 1 + X := by
    have h := evalRec_factorization σa hJ hN e
    rw [evalRec_σa_char hM hX hfin hD, evalRec_B σa le_rfl, hσaJ,
      show σa false = X from rfl, show σa true = 0 from rfl] at h
    apply mul_left_cancel₀ one_sub_X_ne_zero
    linear_combination -h
  -- (4) The words of `J` with one `b`, read by `χL`.
  have hχL : evalRec χL dJ J 0 1 = X := by
    have h := evalRec_factorization χL hJ hN e
    rw [evalRec_χL_char hM hX hfin hD] at h
    have hB : evalRec χL 1 (B : Ser Bool ℚ) = !![0, -1; 0, 1 - X] := by
      rw [evalRec_B _ le_rfl]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [χL]
    have hJ00 : evalRec χL dJ J 0 0 = 1 := by
      rw [(evalRec_upper χL χL_lower dJ J).2.1, χL_diag.1, evalRec_a_one, hσaJ, map_one]
    have hN11 : evalRec χL dN N 1 1 = 1 + X := by
      rw [(evalRec_upper χL χL_lower dN N).2.2, χL_diag.2, hσaN]
    have h01 := congrArg (fun P => P 0 1) h
    rw [hB] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two, hJ00, hN11] at h01
    have hfactor : (evalRec χL dJ J 0 1 - X) * ((1 - X) * (1 + X)) = 0 := by
      linear_combination -h01
    rcases mul_eq_zero.mp hfactor with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (mul_ne_zero one_sub_X_ne_zero one_add_X_ne_zero)
  -- (5) The automaton avoiding `bab`.
  have hψ : (evalRec ψ dJ J).det = 1 := by
    have h := evalRec_factorization ψ hJ hN e
    rw [evalRec_ψ_char hM hX hfin hD, evalRec_B _ le_rfl] at h
    have hdet := congrArg Matrix.det h
    rw [det_ψ_one_sub_code, Matrix.det_mul, Matrix.det_mul, det_ψ_B] at hdet
    have hprod : (evalRec ψ dJ J).det * (evalRec ψ dN N).det = Polynomial.C 2 := by
      apply mul_left_cancel₀ X_ne_zero'
      rw [map_ofNat]
      linear_combination hdet
    rw [eq_C_of_mul_eq_C two_ne_zero hprod, (coeff_zero_of_pure_a A₀q ψ ψ_at_zero hσaJ).2,
      map_one]
  have hψ1 : ((evalRec ψ dJ J).map (fun p => p.coeff 1)).trace = 0 := by
    rw [Matrix.trace_fin_three]
    simp only [Matrix.map_apply]
    rw [← coeff_one_det_three _ (coeff_zero_of_pure_a A₀q ψ ψ_at_zero hσaJ).1, hψ]
    simp [Polynomial.coeff_one]
  -- (6) The cycle of `ab`.
  have hall : allWords = N * Ser.char (Star M) * J := by
    have h2 : (Ser.char (Star M) : Ser Bool ℚ) = 1 + Ser.char (Star M) * Ser.char M :=
      star_eq_one_add_mul' hM
    have hτ : (Ser.char (Star M) : Ser Bool ℚ) * (1 - Ser.char M) = 1 := by
      rw [mul_sub, mul_one]
      nth_rw 1 [h2]
      abel
    rw [e] at hτ
    obtain ⟨u, hu⟩ := isUnit_of_coeff_nil_ne_zero (f := N) (by rw [hN0]; exact one_ne_zero)
    have hB1 : N * Ser.char (Star M) * J * B = 1 := by
      have h0 : (N * Ser.char (Star M) * J * B - 1) * N = 0 := by
        rw [sub_mul, one_mul,
          show N * Ser.char (Star M) * J * B * N = N * (Ser.char (Star M) * (J * B * N)) by
            simp only [mul_assoc],
          hτ, mul_one, sub_self]
      have h1 := congrArg (· * (↑u⁻¹ : Ser Bool ℚ)) h0
      simp only [zero_mul] at h1
      rw [mul_assoc, show N * (↑u⁻¹ : Ser Bool ℚ) = 1 by rw [← hu, Units.mul_inv], mul_one,
        sub_eq_zero] at h1
      exact h1
    calc allWords = N * Ser.char (Star M) * J * B * allWords := by rw [hB1, one_mul]
      _ = N * Ser.char (Star M) * J := by rw [mul_assoc _ B, B_mul_allWords, mul_one]
  obtain ⟨G, hG⟩ := one_add_X_dvd_det hX hJ hN hall hJb fun _ _ h => even_of_abPow_mem hM hX h
  have hρ : (evalRec ρ dJ J).det = 1 := by
    have h := evalRec_factorization ρ hJ hN e
    rw [evalRec_ρ_char hM hX hfin hD, evalRec_B _ le_rfl] at h
    have hdet := congrArg Matrix.det h
    rw [det_ρ_one_sub_code, Matrix.det_mul, Matrix.det_mul, det_ρ_B, hG] at hdet
    have hprod : (evalRec ρ dJ J).det * G = Polynomial.C 1 := by
      apply mul_left_cancel₀ (mul_ne_zero one_sub_X_ne_zero one_add_X_ne_zero)
      rw [Polynomial.C_1]
      linear_combination -hdet
    rw [eq_C_of_mul_eq_C one_ne_zero hprod, (coeff_zero_of_pure_a Uq ρ ρ_at_zero hσaJ).2,
      map_one]
  have hρ1 : ((evalRec ρ dJ J).map (fun p => p.coeff 1)).trace = 0 := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.map_apply]
    rw [← coeff_one_det_two _ (coeff_zero_of_pure_a Uq ρ ρ_at_zero hσaJ).1, hρ]
    simp [Polynomial.coeff_one]
  -- (7) The word identity, summed over the words of `J`.
  have hsum : ∑ w ∈ wordsUpTo dJ, J.coeff w *
      (((wordProd ψ w).map (fun p => p.coeff 1)).trace +
        ((wordProd ρ w).map (fun p => p.coeff 1)).trace) =
      ∑ w ∈ wordsUpTo dJ, J.coeff w * ((wordProd χL w) 0 1).eval 1 :=
    Finset.sum_congr rfl fun w _ => by rw [word_identity]
  rw [← eval_entry χL hJ 0 1, hχL, Polynomial.eval_X] at hsum
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  rw [sum_trace_coeff ψ hJ, sum_trace_coeff ρ hJ, hψ1, hρ1] at hsum
  norm_num at hsum

/-- The four words `aa, abab, baaa, b` over an alphabet with letters `a` and `b`. -/
def Xwords {A : Type*} (a b : A) : Set (List A) := {[a, a], [a, b, a, b], [b, a, a, a], [b]}

/-- **Part (b).** No finite maximal code over an alphabet with two distinct letters `a` and `b`
contains `aa, abab, baaa, b`. -/
theorem no_finite_maximal_completion {A : Type*} {a b : A} (hab : a ≠ b) {M : Set (List A)}
    (hfin : M.Finite) (hX : Xwords a b ⊆ M) : ¬ ThreeWordCodes.IsMaximalCode M := by
  intro hmax
  classical
  let ι : Bool → A := fun c => if c then b else a
  have hι : Function.Injective ι := by
    intro c d h
    cases c <;> cases d <;> simp_all [ι, eq_comm]
  obtain ⟨N, hN⟩ := (hfin.image List.length).bddAbove
  have hlen : ∀ x ∈ M, x.length ≤ max 1 N := fun x hx =>
    (hN ⟨x, hx, rfl⟩).trans (le_max_right 1 N)
  have hsync := sync_of_maximal hmax hab (hX (by simp [Xwords])) (le_max_left 1 N) hlen
  refine no_binary_code (M := pullback ι M) (N₀ := max 1 N)
    (pullback_uniquelyDecodable hι hmax.1) (pullback_finite hι hfin) ?_ fun w => ?_
  · intro v hv
    simp only [Xcode, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    change v.map ι ∈ M
    rcases hv with rfl | rfl | rfl | rfl <;> exact hX (by simp [Xwords, ι])
  · apply mem_star_pullback
    simpa [ι] using hsync (w.map ι)

end SmallestNoncompletable
