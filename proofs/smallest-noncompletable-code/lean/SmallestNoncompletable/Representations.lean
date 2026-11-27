module

public import SmallestNoncompletable.Eval
public import SmallestNoncompletable.Facts
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # Matrix representations of the binary words

Letters are booleans, `a = false` and `b = true`. Each representation sends the two letters to
matrices with polynomial entries in one variable `X`.

* `σb`: `a ↦ 0`, `b ↦ X`, and `σa`: `a ↦ X`, `b ↦ 0`, on `ℚ[X]`.
* `χR`: `a ↦ diag(X, 1)`, `b ↦ E₀₁`, and `χL`: `a ↦ diag(1, X)`, `b ↦ E₀₁`. Products are upper
  triangular and vanish on words with two letters `b`.
* `ψ`: the automaton of the words avoiding `bab`, with weight `X` on `b`.
* `ρ`: the cycle of `ab`, with weight `X` on `b`.

For each of them we evaluate the characteristic polynomial of a code `M ⊇ {aa, abab, baaa, b}`
and compute the determinants used in the final argument. -/

@[expose] public section

namespace SmallestNoncompletable

open Polynomial Matrix Ser InformationTheory

/-- Products of letter images along a word. -/
noncomputable def wordProd {S : Type*} [Monoid S] (x : Bool → S) (w : List Bool) : S :=
  (w.map x).prod

@[simp] theorem wordProd_nil {S : Type*} [Monoid S] (x : Bool → S) : wordProd x [] = 1 := rfl
@[simp] theorem wordProd_cons {S : Type*} [Monoid S] (x : Bool → S) (c : Bool) (w : List Bool) :
    wordProd x (c :: w) = x c * wordProd x w := rfl
theorem wordProd_append {S : Type*} [Monoid S] (x : Bool → S) (u v : List Bool) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp [wordProd]

section CharEval

variable {S : Type*} [Ring S] [Algebra ℚ S] (x : Bool → S)

/-- The characteristic series of a finite set is the sum of its monomials. -/
theorem char_eq_sum {M : Set (List Bool)} (hM : M.Finite) :
    (char M : Ser Bool ℚ) = ∑ w ∈ hM.toFinset, ofWord w := by
  classical
  ext v
  rw [Ser.coeff_sum]
  by_cases hv : v ∈ M
  · rw [coeff_char_of_mem hv, Finset.sum_eq_single v]
    · simp
    · intro w _ hwv
      simp [coeff_ofWord, Ne.symm hwv]
    · intro h
      exact absurd (hM.mem_toFinset.mpr hv) h
  · rw [coeff_char_of_notMem hv]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    have : v ≠ w := by rintro rfl; exact hv (hM.mem_toFinset.mp hw)
    simp [coeff_ofWord, this]

/-- Only the visible words of a finite set contribute to an evaluation. -/
theorem evalRec_char {M : Set (List Bool)} (hM : M.Finite) {d : ℕ}
    (hd : ∀ w ∈ M, w.length ≤ d) (T : Finset (List Bool)) (hT : ∀ w ∈ T, w ∈ M)
    (h0 : ∀ w ∈ M, w ∉ T → wordProd x w = 0) :
    evalRec x d (char M : Ser Bool ℚ) = ∑ w ∈ T, wordProd x w := by
  classical
  rw [char_eq_sum hM, evalRec_sum]
  rw [Finset.sum_congr rfl fun w hw => evalRec_ofWord x w d (hd w (hM.mem_toFinset.mp hw))]
  symm
  apply Finset.sum_subset
  · intro w hw
    exact hM.mem_toFinset.mpr (hT w hw)
  · intro w hw hwT
    exact h0 w (hM.mem_toFinset.mp hw) hwT

end CharEval

/-! ## Words of `M` visible to each representation -/

section Visible

variable {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hX : Xcode ⊆ M)
include hM hX

theorem mem_Bcode_of_count_le {w : List Bool} (hw : w ∈ M) (h : w.count true ≤ 1) :
    w ∈ Bcode := by
  apply mem_Bcode_of_not_hasBab hM (Bcode_subset.trans hX) hw
  intro hb
  have := hb.count_le true
  simp at this
  omega

theorem eq_b_of_no_a {w : List Bool} (hw : w ∈ M) (h : false ∉ w) : w = [true] := by
  have hB : w ∈ Bcode := by
    apply mem_Bcode_of_not_hasBab hM (Bcode_subset.trans hX) hw
    intro hb
    exact h (hb.subset (by simp))
  simp only [Bcode, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hB with rfl | rfl | rfl <;> simp_all

theorem eq_aa_of_no_b {w : List Bool} (hw : w ∈ M) (h : true ∉ w) : w = [false, false] := by
  have hB : w ∈ Bcode := by
    apply mem_Bcode_of_not_hasBab hM (Bcode_subset.trans hX) hw
    intro hb
    exact h (hb.subset (by simp))
  simp only [Bcode, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hB with rfl | rfl | rfl <;> simp_all

end Visible

/-! ## The two scalar representations -/

/-- `a ↦ 0`, `b ↦ X`. -/
noncomputable def σb : Bool → ℚ[X] := fun c => if c then X else 0

/-- `a ↦ X`, `b ↦ 0`. -/
noncomputable def σa : Bool → ℚ[X] := fun c => if c then 0 else X

theorem wordProd_σb_of_mem {w : List Bool} (h : false ∈ w) : wordProd σb w = 0 := by
  induction w with
  | nil => simp at h
  | cons c w ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [σb]
    · simp [ih h]

theorem wordProd_σa_of_mem {w : List Bool} (h : true ∈ w) : wordProd σa w = 0 := by
  induction w with
  | nil => simp at h
  | cons c w ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [σa]
    · simp [ih h]

/-- The coefficients of the `b`-evaluation are the coefficients of the powers of `b`. -/
theorem coeff_evalRec_σb : ∀ (d : ℕ) (f : Ser Bool ℚ) (k : ℕ), k ≤ d →
    (evalRec σb d f).coeff k = f.coeff (List.replicate k true)
  | 0, f, k, hk => by
    obtain rfl : k = 0 := by omega
    simp [evalRec, Polynomial.coeff_C]
  | d + 1, f, k, hk => by
    simp only [evalRec, Fintype.sum_bool, σb, ite_true, Bool.false_eq_true, ite_false,
      zero_mul, add_zero, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    rcases k with _ | k
    · simp [Polynomial.coeff_C]
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, ite_eq_right (by omega), zero_add,
        Polynomial.coeff_X_mul, coeff_evalRec_σb d _ k (by omega)]
      rfl

/-- The constant coefficient of the `a`-evaluation is the constant term. -/
theorem coeff_zero_evalRec_σa : ∀ (d : ℕ) (f : Ser Bool ℚ), (evalRec σa d f).coeff 0 = f.coeff []
  | 0, f => by simp [evalRec]
  | d + 1, f => by
    simp [evalRec, σa]

/-! ## Upper triangular representations -/

/-- If all letters are upper triangular, so is every evaluation, and its diagonal entries are
the evaluations of the diagonal entries. -/
theorem evalRec_upper {R' : Type*} [CommRing R'] [Algebra ℚ R']
    (x : Bool → Matrix (Fin 2) (Fin 2) R') (hx : ∀ c, x c 1 0 = 0) :
    ∀ (d : ℕ) (f : Ser Bool ℚ), (evalRec x d f) 1 0 = 0 ∧
      (evalRec x d f) 0 0 = evalRec (fun c => x c 0 0) d f ∧
      (evalRec x d f) 1 1 = evalRec (fun c => x c 1 1) d f
  | 0, f => by
    simp [evalRec, Matrix.algebraMap_matrix_apply]
  | d + 1, f => by
    have ih := fun c => evalRec_upper x hx d (shift c f)
    simp only [evalRec, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.algebraMap_matrix_apply]
    simp only [Fin.isValue, one_ne_zero, ite_false, ite_true, hx, zero_mul,
      (ih _).1, mul_zero, add_zero, zero_add, Finset.sum_const_zero, (ih _).2.1, (ih _).2.2,
      and_self]

/-- `a ↦ diag(X, 1)`, `b ↦ E₀₁`. -/
noncomputable def χR : Bool → Matrix (Fin 2) (Fin 2) ℚ[X] :=
  fun c => if c then !![0, 1; 0, 0] else !![X, 0; 0, 1]

/-- `a ↦ diag(1, X)`, `b ↦ E₀₁`. -/
noncomputable def χL : Bool → Matrix (Fin 2) (Fin 2) ℚ[X] :=
  fun c => if c then !![0, 1; 0, 0] else !![1, 0; 0, X]

/-- Products for a diagonal `a` and `b ↦ E₀₁`: upper triangular, without diagonal after one
`b`, and zero after two letters `b`. -/
theorem wordProd_upper {R' : Type*} [CommRing R'] (x : Bool → Matrix (Fin 2) (Fin 2) R')
    (hf : x false = !![x false 0 0, 0; 0, x false 1 1]) (ht : x true = !![0, 1; 0, 0]) :
    ∀ w : List Bool, wordProd x w 1 0 = 0 ∧ (1 ≤ w.count true → wordProd x w 0 0 = 0) ∧
      (1 ≤ w.count true → wordProd x w 1 1 = 0) ∧ (w.count true = 0 → wordProd x w 0 1 = 0) ∧
      (2 ≤ w.count true → wordProd x w 0 1 = 0)
  | [] => by simp
  | c :: w => by
    obtain ⟨h10, h00, h11, h01a, h01b⟩ := wordProd_upper x hf ht w
    cases c
    · rw [wordProd_cons, hf]
      simp only [List.count_cons,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ]
      simp only [Fin.isValue, zero_mul, add_zero, zero_add, h10, mul_zero]
      refine ⟨trivial, fun h => by rw [h00 h, mul_zero], fun h => by rw [h11 h, mul_zero],
        fun h => by rw [h01a h, mul_zero], fun h => by rw [h01b h, mul_zero]⟩
    · rw [wordProd_cons, ht]
      simp only [List.count_cons, beq_self_eq_true, ite_true, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      simp only [Fin.isValue, zero_mul, one_mul, zero_add, add_zero, h10]
      refine ⟨trivial, fun _ => trivial, fun _ => trivial, fun h => by omega,
        fun h => h11 (by omega)⟩

theorem wordProd_upper_eq_zero {R' : Type*} [CommRing R'] (x : Bool → Matrix (Fin 2) (Fin 2) R')
    (hf : x false = !![x false 0 0, 0; 0, x false 1 1]) (ht : x true = !![0, 1; 0, 0])
    {w : List Bool} (h : 2 ≤ w.count true) : wordProd x w = 0 := by
  obtain ⟨h10, h00, h11, -, h01⟩ := wordProd_upper x hf ht w
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h00 (by omega)
  · exact h01 h
  · exact h10
  · exact h11 (by omega)

theorem χR_false : χR false = !![χR false 0 0, 0; 0, χR false 1 1] := by
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> rfl
theorem χR_true : χR true = !![0, 1; 0, 0] := rfl
theorem χL_false : χL false = !![χL false 0 0, 0; 0, χL false 1 1] := by
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> rfl
theorem χL_true : χL true = !![0, 1; 0, 0] := rfl

/-! ## The avoiding automaton and the cycle -/

/-- The letter `a` in the automaton of the words avoiding `bab`. -/
noncomputable def A₀ : Matrix (Fin 3) (Fin 3) ℚ[X] := !![1, 0, 0; 0, 0, 1; 1, 0, 0]

/-- The letter `b` in the automaton of the words avoiding `bab`, without its weight. -/
noncomputable def B₀ : Matrix (Fin 3) (Fin 3) ℚ[X] := !![0, 1, 0; 0, 1, 0; 0, 0, 0]

/-- The automaton of the words avoiding `bab`, with weight `X` on `b`. -/
noncomputable def ψ : Bool → Matrix (Fin 3) (Fin 3) ℚ[X] :=
  fun c => if c then (X : ℚ[X]) • B₀ else A₀

/-- The cycle of `ab`, with weight `X` on `b`. -/
noncomputable def ρ : Bool → Matrix (Fin 2) (Fin 2) ℚ[X] :=
  fun c => if c then !![0, 0; X, 0] else !![0, 1; 0, 0]

theorem wordProd_ψ_bab {w : List Bool} (h : HasBab w) : wordProd ψ w = 0 := by
  obtain ⟨u, v, rfl⟩ := h
  have hz : wordProd ψ [true, false, true] = 0 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [wordProd, ψ, A₀, B₀, Matrix.mul_apply, Fin.sum_univ_three]
  rw [wordProd_append, wordProd_append, hz, mul_zero, zero_mul]

theorem wordProd_ρ_of_not_alternating {w : List Bool} (h : ¬ Alternating w) : wordProd ρ w = 0 := by
  simp only [Alternating, not_and_or, not_not] at h
  have key : ∀ c : Bool, [c, c] <:+: w → wordProd ρ w = 0 := by
    rintro c ⟨u, v, rfl⟩
    have hz : wordProd ρ [c, c] = 0 := by
      refine Matrix.ext fun i j => ?_
      cases c <;> fin_cases i <;> fin_cases j <;>
        simp [wordProd, ρ, Matrix.mul_apply, Fin.sum_univ_two]
    rw [wordProd_append, wordProd_append, hz, mul_zero, zero_mul]
  rcases h with h | h
  exacts [key false h, key true h]

/-! ## Evaluations of the code -/

section Code

variable {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hX : Xcode ⊆ M) (hfin : M.Finite)
  {d : ℕ} (hd : ∀ w ∈ M, w.length ≤ d)
include hM hX hfin hd

theorem evalRec_σb_char : evalRec σb d (char M : Ser Bool ℚ) = X := by
  have hT : ∀ w ∈ ({[true]} : Finset (List Bool)), w ∈ M := by
    intro w hw
    rw [Finset.mem_singleton.mp hw]
    exact hX (by simp [Xcode])
  have h0 : ∀ w ∈ M, w ∉ ({[true]} : Finset (List Bool)) → wordProd σb w = 0 := by
    intro w hw hwT
    apply wordProd_σb_of_mem
    by_contra hf
    exact hwT (by simp [eq_b_of_no_a hM hX hw hf])
  rw [evalRec_char σb hfin hd _ hT h0]
  simp [wordProd, σb]

theorem evalRec_σa_char : evalRec σa d (char M : Ser Bool ℚ) = X ^ 2 := by
  have hT : ∀ w ∈ ({[false, false]} : Finset (List Bool)), w ∈ M := by
    intro w hw
    rw [Finset.mem_singleton.mp hw]
    exact hX (by simp [Xcode])
  have h0 : ∀ w ∈ M, w ∉ ({[false, false]} : Finset (List Bool)) → wordProd σa w = 0 := by
    intro w hw hwT
    apply wordProd_σa_of_mem
    by_contra hf
    exact hwT (by simp [eq_aa_of_no_b hM hX hw hf])
  rw [evalRec_char σa hfin hd _ hT h0]
  simp [wordProd, σa, pow_two]

/-- The words of the code with at most one `b`. -/
def BcodeFin : Finset (List Bool) := {[false, false], [true], [true, false, false, false]}

omit hM hfin hd in
theorem BcodeFin_sub : ∀ w ∈ BcodeFin, w ∈ M := by
  intro w hw
  apply hX
  simp only [BcodeFin, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;> simp [Xcode]

omit hfin hd in
theorem not_mem_BcodeFin {w : List Bool} (hw : w ∈ M) (hT : w ∉ BcodeFin) : 2 ≤ w.count true := by
  by_contra hlt
  apply hT
  have := mem_Bcode_of_count_le hM hX hw (by omega)
  simp only [Bcode, Set.mem_insert_iff, Set.mem_singleton_iff] at this
  simp only [BcodeFin, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem evalRec_χR_char :
    evalRec χR d (char M : Ser Bool ℚ) = !![X ^ 2, 2; 0, 1] := by
  rw [evalRec_char χR hfin hd BcodeFin (BcodeFin_sub hX) fun w hw hwT =>
    wordProd_upper_eq_zero χR χR_false χR_true (not_mem_BcodeFin hM hX hw hwT)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [BcodeFin, wordProd, χR, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem evalRec_χL_char :
    evalRec χL d (char M : Ser Bool ℚ) = !![1, 1 + X ^ 3; 0, X ^ 2] := by
  rw [evalRec_char χL hfin hd BcodeFin (BcodeFin_sub hX) fun w hw hwT =>
    wordProd_upper_eq_zero χL χL_false χL_true (not_mem_BcodeFin hM hX hw hwT)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [BcodeFin, wordProd, χL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem evalRec_ψ_char :
    evalRec ψ d (char M : Ser Bool ℚ) =
      wordProd ψ [false, false] + wordProd ψ [true] + wordProd ψ [true, false, false, false] := by
  rw [evalRec_char ψ hfin hd BcodeFin (BcodeFin_sub hX) fun w hw hwT =>
    wordProd_ψ_bab (by
      by_contra hb
      apply hwT
      have := mem_Bcode_of_not_hasBab hM (Bcode_subset.trans hX) hw hb
      simp only [Bcode, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      simp only [BcodeFin, Finset.mem_insert, Finset.mem_singleton]
      tauto)]
  simp [BcodeFin, add_assoc]

theorem evalRec_ρ_char : evalRec ρ d (char M : Ser Bool ℚ) = !![X ^ 2, 0; X, 0] := by
  rw [evalRec_char ρ hfin hd {[true], [false, true, false, true]} (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> exact hX (by simp [Xcode]))
    fun w hw hwT => wordProd_ρ_of_not_alternating (by
      intro halt
      apply hwT
      rcases mem_of_alternating hM hX hw halt with rfl | rfl <;> simp)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [wordProd, ρ, Matrix.mul_apply, Fin.sum_univ_two]; ring

end Code

/-! ## Evaluations of `B = 1 - a - b` -/

theorem evalRec_B {S : Type*} [Ring S] [Algebra ℚ S] (x : Bool → S) {d : ℕ} (hd : 1 ≤ d) :
    evalRec x d (B : Ser Bool ℚ) = 1 - x false - x true := by
  rw [B, evalRec_sub, evalRec_sub, evalRec_one, evalRec_ofWord x [false] d hd,
    evalRec_ofWord x [true] d hd]
  simp

theorem det_ψ_one_sub_code :
    (1 - (wordProd ψ [false, false] + wordProd ψ [true] +
      wordProd ψ [true, false, false, false])).det = -2 * X := by
  rw [Matrix.det_fin_three]
  simp [wordProd, ψ, A₀, B₀]
  ring

theorem det_ψ_B : (1 - ψ false - ψ true).det = -X := by
  rw [Matrix.det_fin_three]
  simp [ψ, A₀, B₀]

theorem det_ρ_one_sub_code : (1 - !![X ^ 2, 0; X, 0] : Matrix (Fin 2) (Fin 2) ℚ[X]).det =
    1 - X ^ 2 := by
  rw [Matrix.det_fin_two]
  simp

theorem det_ρ_B : (1 - ρ false - ρ true).det = 1 - X := by
  rw [Matrix.det_fin_two]
  simp [ρ]

end SmallestNoncompletable
