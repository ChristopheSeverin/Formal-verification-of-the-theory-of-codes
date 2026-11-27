module

public import SmallestNoncompletable.Series
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring

/-! # Polynomials, monomials and residuals

A polynomial is a series whose coefficients vanish beyond some length. The monomial of a word
has coefficient one at that word. The right residual by a letter `a` reads the coefficient of
`w a` at `w`. A series without constant term is the sum of its residuals followed by the
corresponding letters. -/

@[expose] public section

namespace SmallestNoncompletable

namespace Ser

variable {α R : Type*} [CommRing R]

/-- All words longer than `d` have coefficient zero. -/
def DegLE (f : Ser α R) (d : ℕ) : Prop := ∀ w : List α, d < w.length → f.coeff w = 0

/-- A polynomial is a series of bounded degree. -/
def IsPoly (f : Ser α R) : Prop := ∃ d, DegLE f d

namespace DegLE

variable {f g : Ser α R} {d e : ℕ}

theorem mono (hf : DegLE f d) (h : d ≤ e) : DegLE f e := fun w hw => hf w (by omega)

theorem zero (d : ℕ) : DegLE (0 : Ser α R) d := fun _ _ => rfl

theorem one (d : ℕ) : DegLE (1 : Ser α R) d := fun w hw => by
  cases w with
  | nil => simp at hw
  | cons a w => rfl

theorem C (c : R) (d : ℕ) : DegLE (Ser.C c : Ser α R) d := fun w hw => by
  cases w with
  | nil => simp at hw
  | cons a w => simp

theorem add (hf : DegLE f d) (hg : DegLE g d) : DegLE (f + g) d := fun w hw => by
  simp [hf w hw, hg w hw]

theorem neg (hf : DegLE f d) : DegLE (-f) d := fun w hw => by simp [hf w hw]

theorem sub (hf : DegLE f d) (hg : DegLE g d) : DegLE (f - g) d := fun w hw => by
  simp [hf w hw, hg w hw]

theorem smul (c : R) (hf : DegLE f d) : DegLE (c • f) d := fun w hw => by simp [hf w hw]

theorem mul (hf : DegLE f d) (hg : DegLE g e) : DegLE (f * g) (d + e) := fun w hw => by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  by_cases hd : d < (w.take i).length
  · rw [hf _ hd, zero_mul]
  · have hlen : e < (w.drop i).length := by
      simp only [List.length_take, List.length_drop] at hd ⊢
      omega
    rw [hg _ hlen, mul_zero]

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Ser α R} (h : ∀ i ∈ s, DegLE (F i) d) :
    DegLE (∑ i ∈ s, F i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero d
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end DegLE

namespace IsPoly

variable {f g : Ser α R}

theorem zero : IsPoly (0 : Ser α R) := ⟨0, DegLE.zero 0⟩
theorem one : IsPoly (1 : Ser α R) := ⟨0, DegLE.one 0⟩
theorem C (c : R) : IsPoly (Ser.C c : Ser α R) := ⟨0, DegLE.C c 0⟩

theorem add (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  exact ⟨max d e, (hd.mono (le_max_left d e)).add (he.mono (le_max_right d e))⟩

theorem neg (hf : IsPoly f) : IsPoly (-f) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, hd.neg⟩

theorem sub (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem smul (c : R) (hf : IsPoly f) : IsPoly (c • f) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, hd.smul c⟩

theorem mul (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f * g) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  exact ⟨d + e, hd.mul he⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Ser α R} (h : ∀ i ∈ s, IsPoly (F i)) :
    IsPoly (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end IsPoly

section Monomials

variable [DecidableEq α]

/-- The monomial of a word. -/
def ofWord (u : List α) : Ser α R := ⟨fun w => if w = u then 1 else 0⟩

theorem coeff_ofWord (u w : List α) : (ofWord u : Ser α R).coeff w = if w = u then 1 else 0 :=
  rfl

@[simp] theorem coeff_ofWord_self (u : List α) : (ofWord u : Ser α R).coeff u = 1 := by
  simp [coeff_ofWord]

theorem ofWord_nil : (ofWord [] : Ser α R) = 1 := by
  ext w
  cases w <;> simp [coeff_ofWord]

theorem DegLE.ofWord (u : List α) : DegLE (ofWord u : Ser α R) u.length := fun w hw => by
  rw [coeff_ofWord, ite_eq_right]
  rintro rfl
  exact lt_irrefl _ hw

theorem IsPoly.ofWord (u : List α) : IsPoly (ofWord u : Ser α R) := ⟨u.length, DegLE.ofWord u⟩

/-- Multiplying by a monomial on the left reads the coefficient after the prefix. -/
theorem coeff_ofWord_mul (u : List α) (f : Ser α R) (w : List α) :
    (ofWord u * f).coeff w = if u <+: w then f.coeff (w.drop u.length) else 0 := by
  rw [coeff_mul]
  split_ifs with hp
  · obtain ⟨v, rfl⟩ := hp
    rw [Finset.sum_eq_single u.length]
    · simp
    · intro i hi hne
      rw [coeff_ofWord, ite_eq_right, zero_mul]
      intro h
      apply hne
      have := congrArg List.length h
      have hi := Finset.mem_range.mp hi
      simp only [List.length_take, List.length_append] at this hi
      omega
    · intro h
      simp at h
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [coeff_ofWord, ite_eq_right, zero_mul]
    intro h
    exact hp (h ▸ List.take_prefix i w)

/-- Multiplying by a monomial on the right reads the coefficient before the suffix. -/
theorem coeff_mul_ofWord (f : Ser α R) (u : List α) (w : List α) :
    (f * ofWord u).coeff w = if u <:+ w then f.coeff (w.take (w.length - u.length)) else 0 := by
  rw [coeff_mul]
  split_ifs with hs
  · obtain ⟨v, rfl⟩ := hs
    rw [Finset.sum_eq_single v.length]
    · simp
    · intro i hi hne
      rw [coeff_ofWord, ite_eq_right, mul_zero]
      intro h
      apply hne
      have := congrArg List.length h
      simp only [List.length_drop, List.length_append] at this
      have hi := Finset.mem_range.mp hi
      simp only [List.length_append] at hi
      omega
    · intro h
      simp at h
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [coeff_ofWord, ite_eq_right, mul_zero]
    intro h
    exact hs (h ▸ List.drop_suffix i w)

theorem ofWord_append (u v : List α) : (ofWord (u ++ v) : Ser α R) = ofWord u * ofWord v := by
  ext w
  rw [coeff_ofWord_mul, coeff_ofWord]
  by_cases hp : u <+: w
  · obtain ⟨t, rfl⟩ := hp
    simp [coeff_ofWord]
  · rw [ite_eq_right hp, ite_eq_right]
    rintro rfl
    exact hp (List.prefix_append u v)

end Monomials

section Residuals

/-- The right residual by a letter. -/
def rres (a : α) (f : Ser α R) : Ser α R := ⟨fun w => f.coeff (w ++ [a])⟩

omit [CommRing R] in
@[simp] theorem coeff_rres (a : α) (f : Ser α R) (w : List α) :
    (rres a f).coeff w = f.coeff (w ++ [a]) := rfl

@[simp] theorem rres_add (a : α) (f g : Ser α R) : rres a (f + g) = rres a f + rres a g := rfl
@[simp] theorem rres_sub (a : α) (f g : Ser α R) : rres a (f - g) = rres a f - rres a g := rfl
@[simp] theorem rres_smul (a : α) (c : R) (f : Ser α R) : rres a (c • f) = c • rres a f := rfl

theorem DegLE.rres {f : Ser α R} {d : ℕ} (hf : DegLE f (d + 1)) (a : α) :
    DegLE (Ser.rres a f) d := fun w hw => hf _ (by simp; omega)

theorem DegLE.rres_zero {f : Ser α R} (hf : DegLE f 0) (a : α) : Ser.rres a f = 0 := by
  ext w
  exact hf _ (by simp)

theorem IsPoly.rres {f : Ser α R} (hf : IsPoly f) (a : α) : IsPoly (Ser.rres a f) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, (hd.mono (Nat.le_succ d)).rres a⟩

/-- The residual of a product whose right factor has no constant term. -/
theorem rres_mul {F V : Ser α R} (hV : V.coeff [] = 0) (a : α) :
    rres a (F * V) = F * rres a V := by
  ext w
  rw [coeff_rres, coeff_mul, coeff_mul, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  have hlast : (w ++ [a]).drop (w.length + 1) = [] := by simp
  rw [hlast, hV, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  rfl

variable [DecidableEq α]

theorem coeff_mul_letter_nil (f : Ser α R) (a : α) : (f * ofWord [a]).coeff [] = 0 := by
  simp [coeff_ofWord]

theorem coeff_mul_letter (f : Ser α R) (a b : α) (v : List α) :
    (f * ofWord [a]).coeff (v ++ [b]) = if a = b then f.coeff v else 0 := by
  rw [coeff_mul_ofWord]
  by_cases h : a = b
  · subst h
    simp
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]

omit [DecidableEq α] in
theorem coeff_C_of_ne_nil (c : R) {w : List α} (hw : w ≠ []) : (C c : Ser α R).coeff w = 0 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w => simp

/-- A series is its constant term plus the sum of its residuals followed by their letters. -/
theorem eq_C_add_sum_rres [Fintype α] (f : Ser α R) :
    f = C (f.coeff []) + ∑ a : α, rres a f * ofWord [a] := by
  ext w
  rw [coeff_add, coeff_sum]
  rcases List.eq_nil_or_concat w with rfl | ⟨v, b, rfl⟩
  · simp [coeff_ofWord]
  · simp only [List.concat_eq_append]
    rw [coeff_C_of_ne_nil _ (by simp), zero_add]
    simp only [coeff_mul_letter]
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      simp [hab]
    · simp

end Residuals

section Characteristic

/-- The characteristic series of a set of words. -/
noncomputable def char (s : Set (List α)) : Ser α R :=
  ⟨fun w => by classical exact if w ∈ s then 1 else 0⟩

theorem coeff_char (s : Set (List α)) (w : List α) [Decidable (w ∈ s)] :
    (char s : Ser α R).coeff w = if w ∈ s then 1 else 0 := by
  simp only [char]
  congr

theorem coeff_char_of_mem {s : Set (List α)} {w : List α} (h : w ∈ s) :
    (char s : Ser α R).coeff w = 1 := by
  classical
  simp [coeff_char, h]

theorem coeff_char_of_notMem {s : Set (List α)} {w : List α} (h : w ∉ s) :
    (char s : Ser α R).coeff w = 0 := by
  classical
  simp [coeff_char, h]

/-- The characteristic series of a finite set is a polynomial. -/
theorem IsPoly.char {s : Set (List α)} (hs : s.Finite) : IsPoly (char s : Ser α R) := by
  refine ⟨(hs.toFinset.sup List.length), fun w hw => coeff_char_of_notMem fun hm => ?_⟩
  have := Finset.le_sup (f := List.length) (hs.mem_toFinset.mpr hm)
  omega

end Characteristic

end Ser

end SmallestNoncompletable
