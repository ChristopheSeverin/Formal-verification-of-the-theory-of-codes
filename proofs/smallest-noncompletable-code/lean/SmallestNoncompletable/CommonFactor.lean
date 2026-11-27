module

public import SmallestNoncompletable.Polynomials
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-! # A rational expression that is a polynomial (Theorem 14.3.7 of Berstel–Perrin–Reutenauer)

Let `P, Q, R` be polynomials over a field, with `Q` invertible as a series. If `P Q⁻¹ R` is a
polynomial, then there are polynomials with `P = P' S`, `Q = T S` and `R = T R'`.

The pairs `(V₁, V₂)` of polynomials with `V₁ = P Q⁻¹ V₂` form a right module over the
polynomials. It is stable under right residuals of pairs whose second component has no
constant term. A nonzero pair of minimal degree generates the module, and its second
component has a nonzero constant term. -/

@[expose] public section

namespace SmallestNoncompletable

namespace Ser

variable {α K : Type*} [Field K]

/-- A pair of polynomials whose first component is the product of `Φ` and the second. -/
structure Related (Φ : Ser α K) (V : Ser α K × Ser α K) : Prop where
  poly₁ : IsPoly V.1
  poly₂ : IsPoly V.2
  eq : V.1 = Φ * V.2

/-- Both components have degree at most `d`. -/
def DegLE₂ (V : Ser α K × Ser α K) (d : ℕ) : Prop := DegLE V.1 d ∧ DegLE V.2 d

namespace Related

variable {Φ : Ser α K} {V W : Ser α K × Ser α K}

theorem sub (hV : Related Φ V) (hW : Related Φ W) : Related Φ (V - W) :=
  ⟨hV.poly₁.sub hW.poly₁, hV.poly₂.sub hW.poly₂, by
    change V.1 - W.1 = Φ * (V.2 - W.2)
    rw [mul_sub, ← hV.eq, ← hW.eq]⟩

theorem smul (c : K) (hV : Related Φ V) : Related Φ (c • V) :=
  ⟨hV.poly₁.smul c, hV.poly₂.smul c, by
    change c • V.1 = Φ * (c • V.2)
    rw [mul_smul', ← hV.eq]⟩

theorem coeff_nil (hV : Related Φ V) : V.1.coeff [] = Φ.coeff [] * V.2.coeff [] := by
  rw [hV.eq, coeff_mul_nil]

theorem rres (hV : Related Φ V) (h0 : V.2.coeff [] = 0) (a : α) :
    Related Φ (Ser.rres a V.1, Ser.rres a V.2) :=
  ⟨hV.poly₁.rres a, hV.poly₂.rres a, by
    change Ser.rres a V.1 = Φ * Ser.rres a V.2
    rw [hV.eq, rres_mul h0]⟩

end Related

section Generation

variable [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- A pair with zero constant term of degree zero vanishes. -/
private theorem eq_zero_of_degLE_zero {V : Ser α K × Ser α K} (hd : DegLE₂ V 0)
    (h1 : V.1.coeff [] = 0) (h2 : V.2.coeff [] = 0) : V = 0 := by
  have key (f : Ser α K) (hf : DegLE f 0) (h0 : f.coeff [] = 0) : f = 0 := by
    ext w
    cases w with
    | nil => exact h0
    | cons a w => exact hf _ (by simp)
  exact Prod.ext (key _ hd.1 h1) (key _ hd.2 h2)

/-- The decomposition of a pair with zero constant terms along its residuals. -/
private theorem pair_eq_sum_rres {V : Ser α K × Ser α K} (h1 : V.1.coeff [] = 0)
    (h2 : V.2.coeff [] = 0) :
    V = (∑ a : α, Ser.rres a V.1 * ofWord [a], ∑ a : α, Ser.rres a V.2 * ofWord [a]) := by
  refine Prod.ext ?_ ?_
  · conv_lhs => rw [eq_C_add_sum_rres V.1, h1, C_zero, zero_add]
  · conv_lhs => rw [eq_C_add_sum_rres V.2, h2, C_zero, zero_add]

/-- A nonzero related pair of minimal degree generates all related pairs. -/
theorem related_generated {Φ : Ser α K} {V : Ser α K × Ser α K} (hV : Related Φ V)
    (hne : V ≠ 0) :
    ∃ V₀ : Ser α K × Ser α K, Related Φ V₀ ∧ ∀ W, Related Φ W →
      ∃ T, IsPoly T ∧ W.1 = V₀.1 * T ∧ W.2 = V₀.2 * T := by
  classical
  have hex : ∃ d, ∃ V : Ser α K × Ser α K, Related Φ V ∧ V ≠ 0 ∧ DegLE₂ V d := by
    obtain ⟨d₁, h₁⟩ := hV.poly₁
    obtain ⟨d₂, h₂⟩ := hV.poly₂
    exact ⟨max d₁ d₂, V, hV, hne, h₁.mono (le_max_left _ _), h₂.mono (le_max_right _ _)⟩
  obtain ⟨V₀, hV₀, hV₀ne, hV₀d⟩ := Nat.find_spec hex
  set d₀ := Nat.find hex with hd₀
  have minimal : ∀ n (W : Ser α K × Ser α K), Related Φ W → W ≠ 0 → DegLE₂ W n → d₀ ≤ n :=
    fun n W hW hWne hWd => Nat.find_min' hex ⟨W, hW, hWne, hWd⟩
  -- The second component of the generator has a nonzero constant term.
  have hc : V₀.2.coeff [] ≠ 0 := by
    intro h2
    have h1 : V₀.1.coeff [] = 0 := by rw [hV₀.coeff_nil, h2, mul_zero]
    rcases Nat.eq_zero_or_pos d₀ with hz | hpos
    · exact hV₀ne (eq_zero_of_degLE_zero (hz ▸ hV₀d) h1 h2)
    · obtain ⟨m, hm⟩ : ∃ m, d₀ = m + 1 := ⟨d₀ - 1, by omega⟩
      have hsum := pair_eq_sum_rres h1 h2
      have : ∃ a : α, (Ser.rres a V₀.1, Ser.rres a V₀.2) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hV₀ne
        rw [hsum]
        refine Prod.ext ?_ ?_ <;>
        · refine Finset.sum_eq_zero fun a _ => ?_
          have e := hall a
          simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at e
          simp [e.1, e.2]
      obtain ⟨a, ha⟩ := this
      have hle := minimal m _ (hV₀.rres h2 a) ha
        ⟨(hm ▸ hV₀d.1).rres a, (hm ▸ hV₀d.2).rres a⟩
      omega
  refine ⟨V₀, hV₀, ?_⟩
  -- Strong statement by induction on the degree.
  have main : ∀ n (W : Ser α K × Ser α K), Related Φ W → DegLE₂ W n →
      ∃ T, IsPoly T ∧ W.1 = V₀.1 * T ∧ W.2 = V₀.2 * T := by
    intro n
    induction n with
    | zero =>
      intro W hW hd
      have zeroCase : ∀ W' : Ser α K × Ser α K, Related Φ W' → DegLE₂ W' 0 →
          W'.2.coeff [] = 0 → W' = 0 := fun W' hW' hd' h2 =>
        eq_zero_of_degLE_zero hd' (by rw [hW'.coeff_nil, h2, mul_zero]) h2
      by_cases h2 : W.2.coeff [] = 0
      · refine ⟨0, IsPoly.zero, ?_, ?_⟩ <;> simp [zeroCase W hW hd h2]
      · have hle := minimal 0 W hW (fun h => h2 (by rw [h]; rfl)) hd
        set c := W.2.coeff [] / V₀.2.coeff [] with hcdef
        have hW' := hW.sub (hV₀.smul c)
        have hd' : DegLE₂ (W - c • V₀) 0 :=
          ⟨hd.1.sub ((hV₀d.1.mono (by omega)).smul c), hd.2.sub ((hV₀d.2.mono (by omega)).smul c)⟩
        have h2' : (W - c • V₀).2.coeff [] = 0 := by
          change W.2.coeff [] - c * V₀.2.coeff [] = 0
          rw [hcdef, div_mul_cancel₀ _ hc, sub_self]
        have e := zeroCase _ hW' hd' h2'
        refine ⟨C c, IsPoly.C c, ?_, ?_⟩
        · have := congrArg Prod.fst e
          change W.1 - c • V₀.1 = 0 at this
          rw [mul_C, ← sub_eq_zero, this]
        · have := congrArg Prod.snd e
          change W.2 - c • V₀.2 = 0 at this
          rw [mul_C, ← sub_eq_zero, this]
    | succ m ih =>
      -- Pairs with zero constant terms are sums of residual pairs followed by letters.
      have zeroCase : ∀ W : Ser α K × Ser α K, Related Φ W → DegLE₂ W (m + 1) →
          W.2.coeff [] = 0 → ∃ T, IsPoly T ∧ W.1 = V₀.1 * T ∧ W.2 = V₀.2 * T := by
        intro W hW hd h2
        have h1 : W.1.coeff [] = 0 := by rw [hW.coeff_nil, h2, mul_zero]
        have parts : ∀ a : α, ∃ T, IsPoly T ∧ Ser.rres a W.1 = V₀.1 * T ∧
            Ser.rres a W.2 = V₀.2 * T :=
          fun a => ih _ (hW.rres h2 a) ⟨hd.1.rres a, hd.2.rres a⟩
        choose T hT e1 e2 using parts
        refine ⟨∑ a : α, T a * ofWord [a], IsPoly.sum _ fun a _ => (hT a).mul (IsPoly.ofWord _),
          ?_, ?_⟩
        · conv_lhs => rw [eq_C_add_sum_rres W.1, h1, C_zero, zero_add]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [e1 a, mul_assoc]
        · conv_lhs => rw [eq_C_add_sum_rres W.2, h2, C_zero, zero_add]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [e2 a, mul_assoc]
      intro W hW hd
      by_cases h2 : W.2.coeff [] = 0
      · exact zeroCase W hW hd h2
      · have hle := minimal (m + 1) W hW (fun h => h2 (by rw [h]; rfl)) hd
        set c := W.2.coeff [] / V₀.2.coeff [] with hcdef
        have hW' := hW.sub (hV₀.smul c)
        have hd' : DegLE₂ (W - c • V₀) (m + 1) :=
          ⟨hd.1.sub ((hV₀d.1.mono hle).smul c), hd.2.sub ((hV₀d.2.mono hle).smul c)⟩
        have h2' : (W - c • V₀).2.coeff [] = 0 := by
          change W.2.coeff [] - c * V₀.2.coeff [] = 0
          rw [hcdef, div_mul_cancel₀ _ hc, sub_self]
        obtain ⟨T, hT, e1, e2⟩ := zeroCase _ hW' hd' h2'
        refine ⟨T + C c, hT.add (IsPoly.C c), ?_, ?_⟩
        · change W.1 - c • V₀.1 = V₀.1 * T at e1
          rw [mul_add, mul_C, ← e1, sub_add_cancel]
        · change W.2 - c • V₀.2 = V₀.2 * T at e2
          rw [mul_add, mul_C, ← e2, sub_add_cancel]
  intro W hW
  obtain ⟨d₁, h₁⟩ := hW.poly₁
  obtain ⟨d₂, h₂⟩ := hW.poly₂
  exact main (max d₁ d₂) W hW ⟨h₁.mono (le_max_left _ _), h₂.mono (le_max_right _ _)⟩

/-- **Theorem 14.3.7** over a field: if `P Q⁻¹ R` is a polynomial `F`, the three polynomials
share the factorization `P = P' S`, `Q = T S`, `R = T R'`, and then `F = P' R'`. -/
theorem common_factor {P Q R F : Ser α K} (hP : IsPoly P) (hQ : IsPoly Q) (hR : IsPoly R)
    (hF : IsPoly F) (hQ0 : Q.coeff [] ≠ 0) (h : P * Ring.inverse Q * R = F) :
    ∃ P' S T R' : Ser α K, IsPoly P' ∧ IsPoly S ∧ IsPoly T ∧ IsPoly R' ∧
      P = P' * S ∧ Q = T * S ∧ R = T * R' ∧ F = P' * R' := by
  have hu : IsUnit Q := isUnit_of_coeff_nil_ne_zero hQ0
  set Φ := P * Ring.inverse Q with hΦ
  have r1 : Related Φ (P, Q) := ⟨hP, hQ, by
    change P = P * Ring.inverse Q * Q
    rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]⟩
  have r2 : Related Φ (F, R) := ⟨hF, hR, h.symm⟩
  have hne : (P, Q) ≠ 0 := by
    intro e
    apply hQ0
    have := congrArg Prod.snd e
    change Q = 0 at this
    rw [this]
    rfl
  obtain ⟨V₀, hV₀, gen⟩ := related_generated r1 hne
  obtain ⟨S, hS, eP, eQ⟩ := gen _ r1
  obtain ⟨R', hR', eF, eR⟩ := gen _ r2
  exact ⟨V₀.1, S, V₀.2, R', hV₀.poly₁, hS, hV₀.poly₂, hR', eP, eQ, eR, eF⟩

end Generation

end Ser

end SmallestNoncompletable
