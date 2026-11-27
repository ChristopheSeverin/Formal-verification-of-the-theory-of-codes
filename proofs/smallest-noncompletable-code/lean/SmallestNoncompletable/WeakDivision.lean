module

public import SmallestNoncompletable.Polynomials
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # Weak left division by `1 - a - b` (Theorem 14.3.1 of Berstel–Perrin–Reutenauer)

On the binary alphabet `a = false`, `b = true`, put `B = 1 - a - b`. If `f g` is congruent to
a constant modulo `B`, that is `f g = B q + r` with a scalar `r`, and `g ≠ 0`, then `f` is
congruent to a constant as well.

Words are ordered by their *rank*, the binary number `1w`. This is the radix order: shorter
words come first, and words of equal length are ordered lexicographically with `a < b`. The
rank is strictly monotone in each factor of a concatenation. Hence the maximal word of a
product of nonzero polynomials is the product of their maximal words, and its coefficient is
the product of their leading coefficients. The proof removes the leading word of `f`, which
must start with `b`, by a multiple of `B`. -/

@[expose] public section

namespace SmallestNoncompletable

/-- The binary number written `w`, with `a = 0` and `b = 1`. -/
def binVal : List Bool → ℕ
  | [] => 0
  | x :: w => (if x then 2 ^ w.length else 0) + binVal w

/-- The binary number written `1w`. -/
def rank (w : List Bool) : ℕ := 2 ^ w.length + binVal w

theorem binVal_lt (v : List Bool) : binVal v < 2 ^ v.length := by
  induction v with
  | nil => simp [binVal]
  | cons x v ih =>
    simp only [binVal, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem binVal_append (u v : List Bool) :
    binVal (u ++ v) = binVal u * 2 ^ v.length + binVal v := by
  induction u with
  | nil => simp [binVal]
  | cons x u ih =>
    simp only [List.cons_append, binVal, List.length_append, ih, pow_add]
    split_ifs <;> ring

theorem rank_append (u v : List Bool) : rank (u ++ v) = rank u * 2 ^ v.length + binVal v := by
  simp only [rank, binVal_append, List.length_append, pow_add]
  ring

theorem pow_le_rank (w : List Bool) : 2 ^ w.length ≤ rank w := by
  simp [rank]

theorem rank_lt_pow (w : List Bool) : rank w < 2 ^ (w.length + 1) := by
  have := binVal_lt w
  simp only [rank, pow_succ]
  omega

theorem one_le_rank (w : List Bool) : 1 ≤ rank w :=
  le_trans Nat.one_le_two_pow (pow_le_rank w)

theorem rank_nil : rank [] = 1 := rfl

theorem rank_cons (x : Bool) (w : List Bool) :
    rank (x :: w) = (if x then 3 else 2) * 2 ^ w.length + binVal w := by
  have := rank_append [x] w
  simp only [List.singleton_append] at this
  rw [this]
  cases x <;> simp [rank, binVal]

theorem length_le_of_rank_lt {u v : List Bool} (h : rank u < rank v) : u.length ≤ v.length := by
  by_contra hlt
  push Not at hlt
  have h1 := rank_lt_pow v
  have h2 := pow_le_rank u
  have h3 : 2 ^ (v.length + 1) ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem length_eq_of_rank_eq {u v : List Bool} (h : rank u = rank v) : u.length = v.length :=
  le_antisymm (length_le_of_rank_lt' h.le) (length_le_of_rank_lt' h.ge)
where
  length_le_of_rank_lt' {u v : List Bool} (h : rank u ≤ rank v) : u.length ≤ v.length := by
    by_contra hlt
    push Not at hlt
    have h1 := rank_lt_pow v
    have h2 := pow_le_rank u
    have h3 : 2 ^ (v.length + 1) ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hlt
    omega

theorem binVal_injective_of_length {u v : List Bool} (hl : u.length = v.length)
    (h : binVal u = binVal v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons y v => simp at hl
  | cons x u ih =>
    cases v with
    | nil => simp at hl
    | cons y v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hu := binVal_lt u
      have hv := binVal_lt v
      simp only [binVal] at h
      rw [hl] at h hu
      have hxy : x = y := by
        cases x <;> cases y <;> simp at h ⊢ <;> omega
      subst hxy
      have : binVal u = binVal v := by split_ifs at h <;> omega
      rw [ih hl this]

theorem rank_injective : Function.Injective rank := by
  intro u v h
  have hl := length_eq_of_rank_eq h
  apply binVal_injective_of_length hl
  simp only [rank, hl] at h
  omega

/-- Concatenation is strictly monotone on the left. -/
theorem rank_append_lt_left {u u' : List Bool} (v : List Bool) (h : rank u < rank u') :
    rank (u ++ v) < rank (u' ++ v) := by
  rw [rank_append, rank_append]
  have := binVal_lt v
  have h1 : (rank u + 1) * 2 ^ v.length ≤ rank u' * 2 ^ v.length := Nat.mul_le_mul_right _ h
  rw [add_mul, one_mul] at h1
  omega

/-- Concatenation is strictly monotone on the right. -/
theorem rank_append_lt_right (u : List Bool) {v v' : List Bool} (h : rank v < rank v') :
    rank (u ++ v) < rank (u ++ v') := by
  have hlen := length_le_of_rank_lt h
  rcases Nat.lt_or_eq_of_le hlen with hl | hl
  · have h1 := rank_lt_pow (u ++ v)
    have h2 := pow_le_rank (u ++ v')
    have h3 : 2 ^ ((u ++ v).length + 1) ≤ 2 ^ (u ++ v').length :=
      Nat.pow_le_pow_right (by norm_num) (by simp; omega)
    omega
  · rw [rank_append, rank_append, ← hl]
    simp only [rank, ← hl] at h
    omega

theorem rank_append_le {u u' v v' : List Bool} (hu : rank u ≤ rank u') (hv : rank v ≤ rank v') :
    rank (u ++ v) ≤ rank (u' ++ v') := by
  rcases Nat.lt_or_eq_of_le hu with hu | hu
  · rcases Nat.lt_or_eq_of_le hv with hv | hv
    · exact (rank_append_lt_left v hu).le.trans (rank_append_lt_right u' hv).le
    · rw [rank_injective hv]
      exact (rank_append_lt_left v' hu).le
  · rw [rank_injective hu]
    rcases Nat.lt_or_eq_of_le hv with hv | hv
    · exact (rank_append_lt_right u' hv).le
    · rw [rank_injective hv]

namespace Ser

variable {K : Type*} [Field K]

/-- `w` is a leading word of `f`: its coefficient is nonzero and every word of larger rank has
coefficient zero. -/
def IsLead (f : Ser Bool K) (w : List Bool) : Prop :=
  f.coeff w ≠ 0 ∧ ∀ v : List Bool, rank w < rank v → f.coeff v = 0

theorem IsLead.unique {f : Ser Bool K} {u v : List Bool} (hu : IsLead f u) (hv : IsLead f v) :
    u = v := by
  apply rank_injective
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hv.1 (hu.2 v h)
  · exact hu.1 (hv.2 u h)

/-- A nonzero polynomial has a leading word. -/
theorem exists_lead {f : Ser Bool K} (hf : IsPoly f) (hne : f ≠ 0) : ∃ w, IsLead f w := by
  classical
  obtain ⟨d, hd⟩ := hf
  have hex : ∃ N, ∀ v : List Bool, N < rank v → f.coeff v = 0 := by
    refine ⟨2 ^ (d + 1), fun v hv => hd v ?_⟩
    by_contra hle
    push Not at hle
    have := rank_lt_pow v
    have : 2 ^ (v.length + 1) ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set N := Nat.find hex with hN
  have hspec := Nat.find_spec hex
  by_contra hno
  push Not at hno
  have below : ∀ v : List Bool, N - 1 < rank v → f.coeff v = 0 := by
    intro v hv
    rcases Nat.lt_or_ge N (rank v) with hlt | hge
    · exact hspec v hlt
    · have hveq : rank v = N := by omega
      by_contra hc
      exact hno v ⟨hc, fun u hu => hspec u (by omega)⟩
  have hmin := Nat.find_min' hex below
  apply hne
  ext v
  have := one_le_rank v
  exact below v (by omega)

theorem IsLead.coeff_eq_zero {f : Ser Bool K} {w v : List Bool} (h : IsLead f w)
    (hv : f.coeff v ≠ 0) : rank v ≤ rank w := by
  by_contra hlt
  push Not at hlt
  exact hv (h.2 v hlt)

/-- The leading word of a product is the product of the leading words. -/
theorem IsLead.mul {f g : Ser Bool K} {u v : List Bool} (hf : IsLead f u) (hg : IsLead g v) :
    IsLead (f * g) (u ++ v) ∧ (f * g).coeff (u ++ v) = f.coeff u * g.coeff v := by
  have term_zero : ∀ x y : List Bool, (x, y) ≠ (u, v) → rank (u ++ v) ≤ rank (x ++ y) →
      f.coeff x * g.coeff y = 0 := by
    intro x y hne hge
    by_contra hprod
    have r1 := hf.coeff_eq_zero (left_ne_zero_of_mul hprod)
    have r2 := hg.coeff_eq_zero (right_ne_zero_of_mul hprod)
    rcases Nat.lt_or_eq_of_le r1 with r1 | r1
    · have := (rank_append_lt_left y r1).trans_le (rank_append_le le_rfl r2)
      omega
    · rcases Nat.lt_or_eq_of_le r2 with r2 | r2
      · have := rank_append_lt_right x r2
        rw [rank_injective r1] at this hge
        omega
      · exact hne (by rw [rank_injective r1, rank_injective r2])
  have hcoeff : (f * g).coeff (u ++ v) = f.coeff u * g.coeff v := by
    rw [coeff_mul, Finset.sum_eq_single u.length]
    · simp
    · intro i hi hne
      refine term_zero _ _ ?_ (by rw [List.take_append_drop])
      intro he
      apply hne
      have hi := Finset.mem_range.mp hi
      have := congrArg (fun p => p.1.length) he
      simp only [List.length_take, List.length_append] at this hi
      omega
    · intro h
      simp at h
  refine ⟨⟨by rw [hcoeff]; exact mul_ne_zero hf.1 hg.1, fun w hw => ?_⟩, hcoeff⟩
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun i _ => term_zero _ _ ?_ ?_
  · intro he
    have : w = u ++ v := by
      rw [← List.take_append_drop i w]
      simp only [Prod.mk.injEq] at he
      rw [he.1, he.2]
    rw [this] at hw
    exact lt_irrefl _ hw
  · rw [List.take_append_drop]
    exact hw.le

/-- The polynomial `1 - a - b`, with `a = false` and `b = true`. -/
def B : Ser Bool K := 1 - ofWord [false] - ofWord [true]

theorem IsPoly.B : IsPoly (B : Ser Bool K) :=
  (IsPoly.one.sub (IsPoly.ofWord _)).sub (IsPoly.ofWord _)

theorem coeff_B (w : List Bool) :
    (B : Ser Bool K).coeff w =
      (if w = [] then 1 else 0) - (if w = [false] then 1 else 0) - (if w = [true] then 1 else 0) := by
  simp only [B, coeff_sub, coeff_ofWord]
  congr 2
  cases w <;> simp

theorem B_mul_ofWord (u : List Bool) :
    (B : Ser Bool K) * ofWord u = ofWord u - ofWord (false :: u) - ofWord (true :: u) := by
  rw [B, sub_mul, sub_mul, one_mul, ← ofWord_append, ← ofWord_append]
  rfl

theorem isLead_B : IsLead (B : Ser Bool K) [true] := by
  refine ⟨by simp [coeff_B], fun v hv => ?_⟩
  rw [coeff_B]
  have h1 : v ≠ [] := by rintro rfl; simp [rank, binVal] at hv
  have h2 : v ≠ [false] := by rintro rfl; simp [rank, binVal] at hv
  have h3 : v ≠ [true] := by rintro rfl; exact lt_irrefl _ hv
  simp [h1, h2, h3]

theorem rank_lt_rank_true_cons (u : List Bool) :
    rank u < rank (true :: u) ∧ rank (false :: u) < rank (true :: u) := by
  rw [rank_cons, rank_cons]
  simp only [rank, Bool.false_eq_true, ite_false, ite_true]
  have := Nat.two_pow_pos u.length
  constructor <;> omega

/-- **Theorem 14.3.1** for `B = 1 - a - b`: if `f g ≡ r (mod B)` on the left with `g ≠ 0`,
then `f` is congruent to a scalar modulo `B`. -/
theorem weak_division {f g q : Ser Bool K} (hf : IsPoly f) (hg : IsPoly g) (hg0 : g ≠ 0)
    (hq : IsPoly q) {r : K} (h : f * g = B * q + C r) :
    ∃ t s, IsPoly t ∧ f = B * t + C s := by
  classical
  obtain ⟨mg, hmg⟩ := exists_lead hg hg0
  -- Induction on a bound for the ranks of the support of `f`.
  have main : ∀ N (f q : Ser Bool K), IsPoly f → (∀ w, N ≤ rank w → f.coeff w = 0) →
      IsPoly q → ∀ r : K, f * g = B * q + C r → ∃ t s, IsPoly t ∧ f = B * t + C s := by
    intro N
    induction N with
    | zero =>
      intro f q _ hsupp _ r _
      refine ⟨0, 0, IsPoly.zero, ?_⟩
      ext w
      simp [hsupp w (Nat.zero_le _)]
    | succ N ih =>
      intro f q hf hsupp hq r h
      by_cases hlead : ∃ w, rank w = N ∧ f.coeff w ≠ 0
      swap
      · push Not at hlead
        refine ih f q hf (fun w hw => ?_) hq r h
        rcases Nat.lt_or_eq_of_le hw with hw | hw
        · exact hsupp w hw
        · exact hlead w hw.symm
      obtain ⟨w₀, hw₀, hne⟩ := hlead
      have hL : IsLead f w₀ := ⟨hne, fun v hv => hsupp v (by omega)⟩
      rcases w₀ with _ | ⟨x, u⟩
      · -- A polynomial whose leading word is empty is a constant.
        refine ⟨0, f.coeff [], IsPoly.zero, ?_⟩
        ext w
        cases w with
        | nil => simp
        | cons y w =>
          rw [mul_zero, zero_add, coeff_C_cons]
          refine hL.2 _ ?_
          have h1 := pow_le_rank (y :: w)
          have h2 : 2 ≤ 2 ^ (y :: w).length := by
            rw [List.length_cons, pow_succ]
            have := Nat.one_le_two_pow (n := w.length)
            omega
          rw [rank_nil]
          omega
      · -- The leading word of `f` starts with `b`.
        obtain ⟨hfg, hfgc⟩ := hL.mul hmg
        have hBq : IsLead (B * q) (x :: u ++ mg) := by
          have e : B * q = f * g - C r := by rw [h, add_sub_cancel_right]
          rw [e]
          refine ⟨?_, fun v hv => ?_⟩
          · rw [coeff_sub, coeff_C_of_ne_nil _ (by simp), sub_zero]
            exact hfg.1
          · have hv0 : v ≠ [] := by
              rintro rfl
              have := one_le_rank (x :: u ++ mg)
              rw [rank_nil] at hv
              omega
            rw [coeff_sub, coeff_C_of_ne_nil _ hv0, sub_zero]
            exact hfg.2 v hv
        have hq0 : q ≠ 0 := by
          rintro rfl
          apply hBq.1
          simp
        obtain ⟨mq, hmq⟩ := exists_lead hq hq0
        have hx : x = true := by
          have e := hBq.unique (isLead_B.mul hmq).1
          simp only [List.cons_append, List.cons.injEq] at e
          exact e.1
        subst hx
        -- Remove the leading term with a multiple of `B`.
        set c := f.coeff (true :: u) with hc
        set f' := f + C c * (B * ofWord u) with hf'
        have hranks := rank_lt_rank_true_cons u
        have hsupp' : ∀ w, N ≤ rank w → f'.coeff w = 0 := by
          intro w hw
          rw [hf', coeff_add, C_mul, coeff_smul, B_mul_ofWord, coeff_sub, coeff_sub,
            coeff_ofWord, coeff_ofWord, coeff_ofWord]
          rcases Nat.lt_or_eq_of_le hw with hw | hw
          · have h1 : w ≠ u := by rintro rfl; omega
            have h2 : w ≠ false :: u := by rintro rfl; omega
            have h3 : w ≠ true :: u := by rintro rfl; omega
            simp [h1, h2, h3, hsupp w hw]
          · have hw' : w = true :: u := rank_injective (by omega)
            subst hw'
            have h1 : (true :: u) ≠ u := by
              intro e
              have := congrArg List.length e
              simp at this
            simp [h1, hc]
        have hfg' : f' * g = B * (q + C c * (ofWord u * g)) + C r := by
          rw [hf', add_mul, h, mul_add, mul_assoc, ← mul_assoc B, ← C_commute c B,
            mul_assoc, mul_assoc]
          abel
        obtain ⟨t, s, ht, e⟩ := ih f' _ (hf.add ((IsPoly.C c).mul (IsPoly.B.mul
          (IsPoly.ofWord u)))) hsupp' (hq.add ((IsPoly.C c).mul ((IsPoly.ofWord u).mul hg))) r hfg'
        refine ⟨t - C c * ofWord u, s, ht.sub ((IsPoly.C c).mul (IsPoly.ofWord u)), ?_⟩
        have : f = f' - C c * (B * ofWord u) := by rw [hf', add_sub_cancel_right]
        rw [this, e, mul_sub, ← mul_assoc B, ← C_commute c B, mul_assoc]
        abel
  obtain ⟨d, hd⟩ := hf
  refine main (2 ^ (d + 1)) f q ⟨d, hd⟩ (fun w hw => hd w ?_) hq r h
  by_contra hle
  push Not at hle
  have := rank_lt_pow w
  have : 2 ^ (w.length + 1) ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Ser

end SmallestNoncompletable
