module

public import SmallestNoncompletable.Polynomials
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel

/-! # Evaluating polynomials at matrices

A polynomial of degree at most `d` is evaluated by replacing each letter `a` with an element
`x a` of an algebra. The definition reads the first letter, so multiplicativity is an induction
on the degree of the left factor using `shift (f g) = f(ε) shift g + (shift f) g`. -/

@[expose] public section

namespace SmallestNoncompletable

namespace Ser

variable {α : Type*} [Fintype α] {R : Type*} [CommRing R] {S : Type*} [Ring S] [Algebra R S]

/-- Evaluate the words of length at most `d`, replacing each letter `a` by `x a`. -/
def evalRec (x : α → S) : ℕ → Ser α R → S
  | 0, f => algebraMap R S (f.coeff [])
  | d + 1, f => algebraMap R S (f.coeff []) + ∑ a, x a * evalRec x d (shift a f)

variable (x : α → S)

theorem evalRec_add : ∀ (d : ℕ) (f g : Ser α R),
    evalRec x d (f + g) = evalRec x d f + evalRec x d g
  | 0, f, g => by simp [evalRec]
  | d + 1, f, g => by
    simp only [evalRec, coeff_add, map_add, shift_add, evalRec_add d, mul_add,
      Finset.sum_add_distrib]
    abel

theorem evalRec_smul : ∀ (d : ℕ) (c : R) (f : Ser α R),
    evalRec x d (c • f) = c • evalRec x d f
  | 0, c, f => by
    show algebraMap R S (c * f.coeff []) = c • algebraMap R S (f.coeff [])
    rw [map_mul, Algebra.smul_def]
  | d + 1, c, f => by
    have e1 : evalRec x (d + 1) (c • f) =
        algebraMap R S (c * f.coeff []) + ∑ a, x a * evalRec x d (c • shift a f) := rfl
    have e2 : ∀ a, x a * evalRec x d (c • shift a f) = c • (x a * evalRec x d (shift a f)) :=
      fun a => by rw [evalRec_smul d, mul_smul_comm]
    rw [e1, Finset.sum_congr rfl fun a _ => e2 a, ← Finset.smul_sum, map_mul,
      ← Algebra.smul_def, ← smul_add]
    rfl

theorem evalRec_zero : ∀ d : ℕ, evalRec x d (0 : Ser α R) = 0
  | 0 => by simp [evalRec]
  | d + 1 => by simp [evalRec, evalRec_zero d]

theorem evalRec_neg (d : ℕ) (f : Ser α R) : evalRec x d (-f) = -evalRec x d f := by
  have := evalRec_add x d f (-f)
  rw [add_neg_cancel, evalRec_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem evalRec_sub (d : ℕ) (f g : Ser α R) :
    evalRec x d (f - g) = evalRec x d f - evalRec x d g := by
  rw [sub_eq_add_neg, evalRec_add, evalRec_neg, ← sub_eq_add_neg]

theorem evalRec_sum (d : ℕ) {ι : Type*} (s : Finset ι) (F : ι → Ser α R) :
    evalRec x d (∑ i ∈ s, F i) = ∑ i ∈ s, evalRec x d (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalRec_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evalRec_add, ih]

omit [Fintype α] in
/-- A polynomial of degree zero is a constant. -/
theorem eq_C_of_degLE_zero {f : Ser α R} (hf : DegLE f 0) : f = C (f.coeff []) := by
  ext w
  cases w with
  | nil => simp
  | cons a w => rw [coeff_C_cons]; exact hf _ (by simp)

theorem evalRec_succ_of_degLE : ∀ {d : ℕ} {f : Ser α R}, DegLE f d →
    evalRec x (d + 1) f = evalRec x d f
  | 0, f, hf => by
    have hs : ∀ a, shift a f = 0 := fun a => by
      ext w
      exact hf _ (by simp)
    simp [evalRec, hs]
  | d + 1, f, hf => by
    have hs : ∀ a, DegLE (shift a f) d := fun a w hw => hf _ (by simp; omega)
    show algebraMap R S (f.coeff []) + ∑ a, x a * evalRec x (d + 1) (shift a f) =
      algebraMap R S (f.coeff []) + ∑ a, x a * evalRec x d (shift a f)
    congr 1
    exact Finset.sum_congr rfl fun a _ => by rw [evalRec_succ_of_degLE (hs a)]

theorem evalRec_stable {d e : ℕ} {f : Ser α R} (hf : DegLE f d) (h : d ≤ e) :
    evalRec x e f = evalRec x d f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, evalRec_succ_of_degLE x (hf.mono (by omega)), ih (by omega)]

/-- The first-letter decomposition of an evaluation, at any larger truncation. -/
theorem evalRec_eq_add_sum {e D : ℕ} {g : Ser α R} (hg : DegLE g e) (hD : e ≤ D + 1) :
    evalRec x e g = algebraMap R S (g.coeff []) + ∑ a, x a * evalRec x D (shift a g) := by
  rcases e with _ | e
  · have hs : ∀ a, shift a g = 0 := fun a => by
      ext w
      exact hg _ (by simp)
    simp [evalRec, hs, evalRec_zero]
  · simp only [evalRec]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs : DegLE (shift a g) e := fun w hw => hg _ (by simp; omega)
    rw [evalRec_stable x hs (show e ≤ D by omega)]

theorem evalRec_C (d : ℕ) (c : R) : evalRec x d (C c : Ser α R) = algebraMap R S c := by
  rw [evalRec_stable x (DegLE.C c 0) (Nat.zero_le d)]
  simp [evalRec]

theorem evalRec_one (d : ℕ) : evalRec x d (1 : Ser α R) = 1 := by
  rw [← C_one, evalRec_C, map_one]

/-- **Multiplicativity** of the evaluation. -/
theorem evalRec_mul : ∀ {d e : ℕ} {f g : Ser α R}, DegLE f d → DegLE g e →
    evalRec x (d + e) (f * g) = evalRec x d f * evalRec x e g
  | 0, e, f, g, hf, hg => by
    rw [eq_C_of_degLE_zero hf, C_mul, zero_add, evalRec_smul, evalRec, coeff_C_nil,
      Algebra.smul_def]
  | d + 1, e, f, g, hf, hg => by
    have hs : ∀ a, DegLE (shift a f) d := fun a w hw => hf _ (by simp; omega)
    have key : ∀ a, evalRec x (d + e) (shift a (f * g)) =
        f.coeff [] • evalRec x (d + e) (shift a g) + evalRec x d (shift a f) * evalRec x e g := by
      intro a
      rw [shift_mul, evalRec_add, evalRec_smul, evalRec_mul (hs a) hg]
    have hge := evalRec_eq_add_sum x hg (D := d + e) (by omega)
    have hAG : algebraMap R S (f.coeff []) * evalRec x e g =
        algebraMap R S (f.coeff []) * algebraMap R S (g.coeff []) +
          ∑ a, x a * (f.coeff [] • evalRec x (d + e) (shift a g)) := by
      rw [hge, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_assoc, Algebra.commutes, mul_assoc, ← Algebra.smul_def]
    calc evalRec x (d + 1 + e) (f * g)
        = algebraMap R S ((f * g).coeff []) +
            ∑ a, x a * evalRec x (d + e) (shift a (f * g)) := by
          rw [show d + 1 + e = d + e + 1 by omega]
          rfl
      _ = algebraMap R S (f.coeff []) * evalRec x e g +
            ∑ a, x a * evalRec x d (shift a f) * evalRec x e g := by
          rw [hAG, coeff_mul_nil, map_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [key, mul_add, mul_assoc]
      _ = evalRec x (d + 1) f * evalRec x e g := by
          rw [show evalRec x (d + 1) f = algebraMap R S (f.coeff []) +
            ∑ a, x a * evalRec x d (shift a f) from rfl, add_mul, Finset.sum_mul]

variable [DecidableEq α]

theorem evalRec_ofWord : ∀ (u : List α) (d : ℕ), u.length ≤ d →
    evalRec x d (ofWord u : Ser α R) = (u.map x).prod
  | [], d, _ => by rw [ofWord_nil, evalRec_one]; rfl
  | c :: u, d + 1, h => by
    have hs : ∀ a, shift a (ofWord (c :: u) : Ser α R) = if a = c then ofWord u else 0 := by
      intro a
      ext w
      split_ifs with hac
      · subst hac
        simp [coeff_ofWord]
      · simp [coeff_ofWord, hac]
    simp only [evalRec, coeff_ofWord, reduceCtorEq, ite_false, map_zero, zero_add, hs]
    rw [Finset.sum_eq_single c]
    · simp only [ite_true, List.map_cons, List.prod_cons]
      rw [evalRec_ofWord u d (by simpa using h)]
    · intro a _ hac
      simp [hac, evalRec_zero]
    · simp
  | _ :: _, 0, h => by simp at h

omit [DecidableEq α] in
/-- Evaluation commutes with algebra homomorphisms. -/
theorem evalRec_map {T : Type*} [Ring T] [Algebra R T] (φ : S →ₐ[R] T) :
    ∀ (d : ℕ) (f : Ser α R), φ (evalRec x d f) = evalRec (fun a => φ (x a)) d f
  | 0, f => by simp [evalRec]
  | d + 1, f => by
    simp only [evalRec, map_add, AlgHom.commutes, map_sum, map_mul, evalRec_map φ d]

/-- The words of length at most `d`. -/
def wordsUpTo (d : ℕ) : Finset (List α) :=
  (Finset.range (d + 1)).biUnion fun n => (Finset.univ : Finset (Fin n → α)).image List.ofFn

theorem mem_wordsUpTo {d : ℕ} {w : List α} : w ∈ wordsUpTo d ↔ w.length ≤ d := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, g, rfl⟩
    simp
    omega
  · intro h
    exact ⟨w.length, by omega, fun i => w[i], List.ofFn_getElem⟩

/-- A polynomial is the sum of its monomials. -/
theorem eq_sum_ofWord {f : Ser α R} {d : ℕ} (hf : DegLE f d) :
    f = ∑ w ∈ wordsUpTo d, f.coeff w • ofWord w := by
  ext v
  rw [coeff_sum]
  by_cases hv : v.length ≤ d
  · rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hwv
      simp [coeff_ofWord, Ne.symm hwv]
    · intro h
      exact absurd (mem_wordsUpTo.mpr hv) h
  · rw [hf v (by omega)]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    have hw := mem_wordsUpTo.mp hw
    have : v ≠ w := by rintro rfl; omega
    simp [coeff_ofWord, this]

/-- The evaluation as a finite sum over words. -/
theorem evalRec_eq_sum {f : Ser α R} {d : ℕ} (hf : DegLE f d) :
    evalRec x d f = ∑ w ∈ wordsUpTo d, f.coeff w • (w.map x).prod := by
  conv_lhs => rw [eq_sum_ofWord hf]
  rw [evalRec_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [evalRec_smul, evalRec_ofWord x w d (mem_wordsUpTo.mp hw)]

end Ser

end SmallestNoncompletable
