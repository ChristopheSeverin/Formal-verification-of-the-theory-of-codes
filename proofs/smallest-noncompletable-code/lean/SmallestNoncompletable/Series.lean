module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Ring

/-! # Formal series in noncommuting variables

A series assigns a coefficient to every word. Multiplication cuts a word in all possible ways.
The product is defined by recursion on the first letter, which makes associativity an
induction on the length of the word. A series whose constant coefficient is invertible is a
unit, by the geometric series. -/

@[expose] public section

namespace SmallestNoncompletable

/-- Formal series in the words over `α`, with coefficients in `R`. -/
@[ext] structure Ser (α : Type*) (R : Type*) where
  coeff : List α → R

namespace Ser

variable {α R : Type*}

section Additive

variable [CommRing R]

instance : Zero (Ser α R) := ⟨⟨fun _ => 0⟩⟩
instance : Add (Ser α R) := ⟨fun f g => ⟨fun w => f.coeff w + g.coeff w⟩⟩
instance : Neg (Ser α R) := ⟨fun f => ⟨fun w => -f.coeff w⟩⟩
instance : Sub (Ser α R) := ⟨fun f g => ⟨fun w => f.coeff w - g.coeff w⟩⟩
instance : SMul R (Ser α R) := ⟨fun c f => ⟨fun w => c * f.coeff w⟩⟩
instance : SMul ℕ (Ser α R) := ⟨fun n f => ⟨fun w => n • f.coeff w⟩⟩
instance : SMul ℤ (Ser α R) := ⟨fun n f => ⟨fun w => n • f.coeff w⟩⟩

@[simp] theorem coeff_zero (w : List α) : (0 : Ser α R).coeff w = 0 := rfl
@[simp] theorem coeff_add (f g : Ser α R) (w : List α) :
    (f + g).coeff w = f.coeff w + g.coeff w := rfl
@[simp] theorem coeff_neg (f : Ser α R) (w : List α) : (-f).coeff w = -f.coeff w := rfl
@[simp] theorem coeff_sub (f g : Ser α R) (w : List α) :
    (f - g).coeff w = f.coeff w - g.coeff w := rfl
@[simp] theorem coeff_smul (c : R) (f : Ser α R) (w : List α) :
    (c • f).coeff w = c * f.coeff w := rfl

omit [CommRing R] in
theorem coeff_injective : Function.Injective (Ser.coeff : Ser α R → List α → R) :=
  fun _ _ h => Ser.ext h

instance : AddCommGroup (Ser α R) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module R (Ser α R) :=
  coeff_injective.module R ⟨⟨Ser.coeff, rfl⟩, fun _ _ => rfl⟩ (fun _ _ => rfl)

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Ser α R) (w : List α) :
    (∑ i ∈ s, f i).coeff w = ∑ i ∈ s, (f i).coeff w := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coeff_add, ih]

end Additive

section Multiplicative

variable [CommRing R]

/-- Remove a first letter. -/
def shift (a : α) (f : Ser α R) : Ser α R := ⟨fun w => f.coeff (a :: w)⟩

/-- Cut the word after the empty prefix, or keep the first letter in the left factor. -/
def conv (f g : Ser α R) : List α → R
  | [] => f.coeff [] * g.coeff []
  | a :: w => f.coeff [] * g.coeff (a :: w) + conv (shift a f) g w

instance : Mul (Ser α R) := ⟨fun f g => ⟨conv f g⟩⟩

/-- The empty word with coefficient one. -/
instance : One (Ser α R) := ⟨⟨fun w => match w with | [] => 1 | _ :: _ => 0⟩⟩

@[simp] theorem coeff_one_nil : (1 : Ser α R).coeff [] = 1 := rfl
@[simp] theorem coeff_one_cons (a : α) (w : List α) : (1 : Ser α R).coeff (a :: w) = 0 := rfl

theorem coeff_one_of_ne_nil {w : List α} (hw : w ≠ []) : (1 : Ser α R).coeff w = 0 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w => rfl

@[simp] theorem coeff_mul_nil (f g : Ser α R) : (f * g).coeff [] = f.coeff [] * g.coeff [] := rfl

theorem coeff_mul_cons (f g : Ser α R) (a : α) (w : List α) :
    (f * g).coeff (a :: w) = f.coeff [] * g.coeff (a :: w) + (shift a f * g).coeff w := rfl

omit [CommRing R] in
@[simp] theorem coeff_shift (a : α) (f : Ser α R) (w : List α) :
    (shift a f).coeff w = f.coeff (a :: w) := rfl

@[simp] theorem shift_add (a : α) (f g : Ser α R) : shift a (f + g) = shift a f + shift a g := rfl
@[simp] theorem shift_smul (a : α) (c : R) (f : Ser α R) : shift a (c • f) = c • shift a f := rfl
@[simp] theorem shift_zero (a : α) : shift a (0 : Ser α R) = 0 := rfl
@[simp] theorem shift_one (a : α) : shift a (1 : Ser α R) = 0 := rfl

theorem add_mul' (f g h : Ser α R) : (f + g) * h = f * h + g * h := by
  ext w
  induction w generalizing f g with
  | nil => simp [add_mul]
  | cons a w ih =>
    simp only [coeff_mul_cons, coeff_add, shift_add, ih]
    ring

theorem mul_add' (f g h : Ser α R) : f * (g + h) = f * g + f * h := by
  ext w
  induction w generalizing f with
  | nil => simp [mul_add]
  | cons a w ih =>
    simp only [coeff_mul_cons, coeff_add, ih]
    ring

theorem smul_mul' (c : R) (f g : Ser α R) : (c • f) * g = c • (f * g) := by
  ext w
  induction w generalizing f with
  | nil => simp [mul_assoc]
  | cons a w ih =>
    simp only [coeff_mul_cons, coeff_smul, shift_smul, ih]
    ring

theorem mul_smul' (c : R) (f g : Ser α R) : f * (c • g) = c • (f * g) := by
  ext w
  induction w generalizing f with
  | nil => simp only [coeff_mul_nil, coeff_smul]; ring
  | cons a w ih =>
    simp only [coeff_mul_cons, coeff_smul, ih]
    ring

theorem zero_mul' (f : Ser α R) : 0 * f = 0 := by
  ext w
  induction w with
  | nil => simp
  | cons a w ih => simp [coeff_mul_cons, ih]

theorem mul_zero' (f : Ser α R) : f * 0 = 0 := by
  ext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => simp [coeff_mul_cons, ih]

theorem one_mul' (f : Ser α R) : 1 * f = f := by
  ext w
  cases w with
  | nil => simp
  | cons a w => simp [coeff_mul_cons, zero_mul']

theorem mul_one' (f : Ser α R) : f * 1 = f := by
  ext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => simp [coeff_mul_cons, ih]

/-- The first letter of a product comes from the left factor unless that factor is empty. -/
theorem shift_mul (a : α) (f g : Ser α R) :
    shift a (f * g) = f.coeff [] • shift a g + shift a f * g := by
  ext w
  simp [coeff_mul_cons]

theorem mul_assoc' (f g h : Ser α R) : f * g * h = f * (g * h) := by
  ext w
  induction w generalizing f g with
  | nil => simp [mul_assoc]
  | cons a w ih =>
    rw [coeff_mul_cons, coeff_mul_cons, coeff_mul_cons, shift_mul, add_mul', smul_mul',
      coeff_add, coeff_smul, ih, coeff_mul_nil]
    ring

instance : Ring (Ser α R) :=
  { (inferInstance : AddCommGroup (Ser α R)) with
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one'
    left_distrib := mul_add'
    right_distrib := add_mul'
    zero_mul := zero_mul'
    mul_zero := mul_zero' }

instance : Algebra R (Ser α R) :=
  Algebra.ofModule smul_mul' mul_smul'

/-- The constant series. -/
def C (c : R) : Ser α R := c • 1

@[simp] theorem coeff_C_nil (c : R) : (C c : Ser α R).coeff [] = c := by simp [C]
@[simp] theorem coeff_C_cons (c : R) (a : α) (w : List α) :
    (C c : Ser α R).coeff (a :: w) = 0 := by simp [C]

theorem C_mul (c : R) (f : Ser α R) : C c * f = c • f := by
  rw [C, smul_mul', one_mul]

theorem mul_C (c : R) (f : Ser α R) : f * C c = c • f := by
  rw [C, mul_smul', mul_one]

theorem C_add (c d : R) : (C (c + d) : Ser α R) = C c + C d := by
  simp [C, add_smul]

theorem C_mul_C (c d : R) : (C c * C d : Ser α R) = C (c * d) := by
  rw [C_mul, C, C, smul_smul]

@[simp] theorem C_one : (C 1 : Ser α R) = 1 := by simp [C]
@[simp] theorem C_zero : (C 0 : Ser α R) = 0 := by simp [C]

theorem C_commute (c : R) (f : Ser α R) : C c * f = f * C c := by
  rw [C_mul, mul_C]

/-- The constant coefficient is multiplicative. -/
def constCoeff : Ser α R →+* R where
  toFun f := f.coeff []
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem constCoeff_apply (f : Ser α R) : constCoeff f = f.coeff [] := rfl

/-- The product formula as a sum over all cuts of the word. -/
theorem coeff_mul (f g : Ser α R) (w : List α) :
    (f * g).coeff w = ∑ i ∈ Finset.range (w.length + 1),
      f.coeff (w.take i) * g.coeff (w.drop i) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [coeff_mul_cons, ih, List.length_cons]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.drop_succ_cons, coeff_shift, List.take_zero,
      List.drop_zero]
    ring

/-- Coefficients of a product only depend on coefficients of shorter or equal words. -/
theorem coeff_mul_congr_right {f g g' : Ser α R} {w : List α}
    (h : ∀ v : List α, v.length ≤ w.length → g.coeff v = g'.coeff v) :
    (f * g).coeff w = (f * g').coeff w := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h _ (by simp)]

theorem coeff_mul_congr_left {f f' g : Ser α R} {w : List α}
    (h : ∀ v : List α, v.length ≤ w.length → f.coeff v = f'.coeff v) :
    (f * g).coeff w = (f' * g).coeff w := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h _ (by simp)]

/-- A power of a series without constant term vanishes on shorter words. -/
theorem coeff_pow_eq_zero {h : Ser α R} (h0 : h.coeff [] = 0) :
    ∀ (n : ℕ) (w : List α), w.length < n → (h ^ n).coeff w = 0
  | 0, w, hw => absurd hw (Nat.not_lt_zero _)
  | n + 1, w, hw => by
    rw [pow_succ', coeff_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [h0]
    · have hlen : (w.drop i).length < n := by
        have := Finset.mem_range.mp hi
        rw [List.length_drop]
        omega
      rw [coeff_pow_eq_zero h0 n _ hlen, mul_zero]

/-- The geometric series of a series without constant term. -/
def geom (h : Ser α R) : Ser α R :=
  ⟨fun w => ∑ n ∈ Finset.range (w.length + 1), (h ^ n).coeff w⟩

theorem geom_agree {h : Ser α R} (h0 : h.coeff [] = 0) (N : ℕ) (w : List α)
    (hw : w.length ≤ N) : (geom h).coeff w = (∑ n ∈ Finset.range (N + 1), h ^ n).coeff w := by
  rw [coeff_sum, geom]
  dsimp only
  rw [← Finset.sum_range_add_sum_Ico _ (show w.length + 1 ≤ N + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (w.length + 1) (N + 1)), add_zero]
  intro n hn
  exact coeff_pow_eq_zero h0 n w (by simp at hn; omega)

theorem one_sub_mul_geom {h : Ser α R} (h0 : h.coeff [] = 0) : (1 - h) * geom h = 1 := by
  ext w
  rw [coeff_mul_congr_right (g' := ∑ n ∈ Finset.range (w.length + 1), h ^ n)
    (fun v hv => geom_agree h0 _ v hv)]
  have hg : (1 - h) * ∑ n ∈ Finset.range (w.length + 1), h ^ n = 1 - h ^ (w.length + 1) :=
    mul_neg_geom_sum h _
  rw [hg, coeff_sub, coeff_pow_eq_zero h0 _ w (Nat.lt_succ_self _), sub_zero]

theorem geom_mul_one_sub {h : Ser α R} (h0 : h.coeff [] = 0) : geom h * (1 - h) = 1 := by
  ext w
  rw [coeff_mul_congr_left (f' := ∑ n ∈ Finset.range (w.length + 1), h ^ n)
    (fun v hv => geom_agree h0 _ v hv)]
  have hg : (∑ n ∈ Finset.range (w.length + 1), h ^ n) * (1 - h) = 1 - h ^ (w.length + 1) :=
    geom_sum_mul_neg h _
  rw [hg, coeff_sub, coeff_pow_eq_zero h0 _ w (Nat.lt_succ_self _), sub_zero]

/-- A series with constant coefficient one is a unit. -/
theorem isUnit_of_coeff_nil_eq_one {f : Ser α R} (hf : f.coeff [] = 1) : IsUnit f := by
  have h0 : (1 - f).coeff [] = 0 := by simp [hf]
  have e : 1 - (1 - f) = f := sub_sub_cancel 1 f
  refine ⟨⟨f, geom (1 - f), ?_, ?_⟩, rfl⟩
  · simpa [e] using one_sub_mul_geom h0
  · simpa [e] using geom_mul_one_sub h0

end Multiplicative

section Field

variable {K : Type*} [Field K]

/-- Over a field, a series is a unit exactly when its constant coefficient is nonzero. -/
theorem isUnit_of_coeff_nil_ne_zero {f : Ser α K} (hf : f.coeff [] ≠ 0) : IsUnit f := by
  have hu : IsUnit (C (f.coeff [])⁻¹ * f) :=
    isUnit_of_coeff_nil_eq_one (by simp [inv_mul_cancel₀ hf])
  have hc : IsUnit (C (f.coeff []) : Ser α K) :=
    ⟨⟨C (f.coeff []), C (f.coeff [])⁻¹, by rw [C_mul_C, mul_inv_cancel₀ hf, C_one],
      by rw [C_mul_C, inv_mul_cancel₀ hf, C_one]⟩, rfl⟩
  have e : f = C (f.coeff []) * (C (f.coeff [])⁻¹ * f) := by
    rw [← mul_assoc, C_mul_C, mul_inv_cancel₀ hf, C_one, one_mul]
  rw [e]
  exact hc.mul hu

theorem isUnit_iff_coeff_nil_ne_zero {f : Ser α K} : IsUnit f ↔ f.coeff [] ≠ 0 := by
  refine ⟨fun ⟨u, hu⟩ h => ?_, isUnit_of_coeff_nil_ne_zero⟩
  have e := congrArg constCoeff u.mul_inv
  rw [map_mul, hu, constCoeff_apply, h, zero_mul, map_one] at e
  exact zero_ne_one e

end Field

end Ser

end SmallestNoncompletable
