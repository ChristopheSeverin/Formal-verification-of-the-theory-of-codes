module

public import SmallestNoncompletable.Factorization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Residuals of the series of a free submonoid

Let `τ` satisfy `τ = 1 + M τ = 1 + τ M` for a polynomial `M` without constant term. This holds
for the characteristic series of `M*` when `M` is a code. The left residual of `τ` by a word is
`S τ` for a polynomial `S`, and its right residual is `τ P` for a polynomial `P`. If every word
`w` gives `u w v ∈ M*`, the two-sided residual is the series of all words. This yields the weak
factorization `A* = R₁ + S₁ M* P` of Lemma 14.4.3 (ii) of Berstel–Perrin–Reutenauer without
using the minimal ideal of the transition monoid. -/

@[expose] public section

namespace SmallestNoncompletable

namespace Ser

variable {α R : Type*} [CommRing R]

/-- The left residual by a word: the coefficient of `u w` at `w`. -/
def lresW : List α → Ser α R → Ser α R
  | [], f => f
  | a :: u, f => lresW u (shift a f)

/-- The right residual by a word: the coefficient of `w v` at `w`. -/
def rresW : List α → Ser α R → Ser α R
  | [], f => f
  | c :: v, f => rres c (rresW v f)

omit [CommRing R] in
theorem coeff_lresW (u w : List α) (f : Ser α R) : (lresW u f).coeff w = f.coeff (u ++ w) := by
  induction u generalizing f with
  | nil => rfl
  | cons a u ih => rw [lresW, ih]; rfl

omit [CommRing R] in
theorem coeff_rresW (v w : List α) (f : Ser α R) : (rresW v f).coeff w = f.coeff (w ++ v) := by
  induction v generalizing w with
  | nil => simp [rresW]
  | cons c v ih => rw [rresW, coeff_rres, ih]; simp

theorem lresW_add (u : List α) (f g : Ser α R) : lresW u (f + g) = lresW u f + lresW u g := by
  ext w
  simp [coeff_lresW]

theorem DegLE.shift {f : Ser α R} {d : ℕ} (hf : DegLE f (d + 1)) (a : α) :
    DegLE (Ser.shift a f) d := fun w hw => hf _ (by simp; omega)

theorem IsPoly.shift {f : Ser α R} (hf : IsPoly f) (a : α) : IsPoly (Ser.shift a f) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, (hd.mono (Nat.le_succ d)).shift a⟩

/-- The product rule for right residuals. -/
theorem rres_mul' (c : α) (f g : Ser α R) :
    rres c (f * g) = f * rres c g + g.coeff [] • rres c f := by
  ext w
  rw [coeff_add, coeff_smul, coeff_rres, coeff_mul, coeff_mul, List.length_append,
    List.length_singleton, Finset.sum_range_succ]
  have hlast : (w ++ [c]).drop (w.length + 1) = [] := by simp
  have htake : (w ++ [c]).take (w.length + 1) = w ++ [c] := by simp
  rw [hlast, htake, coeff_rres, mul_comm (g.coeff [])]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  rfl

@[simp] theorem rres_one (c : α) : rres c (1 : Ser α R) = 0 := by
  ext w
  simp only [coeff_rres, coeff_zero]
  cases w <;> rfl

section Star

variable {M τ : Ser α R}

theorem coeff_nil_of_star (hM0 : M.coeff [] = 0) (h1 : τ = 1 + M * τ) : τ.coeff [] = 1 := by
  have := congrArg (fun f : Ser α R => f.coeff []) h1
  simpa [hM0] using this

theorem shift_star (hM0 : M.coeff [] = 0) (h1 : τ = 1 + M * τ) (a : α) :
    shift a τ = shift a M * τ := by
  conv_lhs => rw [h1]
  rw [shift_add, shift_one, zero_add, shift_mul, hM0, zero_smul, zero_add]

theorem rres_star (hM0 : M.coeff [] = 0) (h2 : τ = 1 + τ * M) (c : α) :
    rres c τ = τ * rres c M := by
  conv_lhs => rw [h2]
  rw [rres_add, rres_one, zero_add, rres_mul', hM0, zero_smul, add_zero]

/-- The left residual of `S τ P + E` keeps this shape. -/
theorem lresW_star (hM : IsPoly M) (hM0 : M.coeff [] = 0) (h1 : τ = 1 + M * τ) (P : Ser α R)
    (hP : IsPoly P) (u : List α) :
    ∀ S E : Ser α R, IsPoly S → IsPoly E → ∃ S' E' : Ser α R, IsPoly S' ∧ IsPoly E' ∧
      lresW u (S * τ) = S' * τ ∧ lresW u (S * τ * P + E) = S' * τ * P + E' := by
  induction u with
  | nil => exact fun S E hS hE => ⟨S, E, hS, hE, rfl, rfl⟩
  | cons a u ih =>
    intro S E hS hE
    have hτ0 := coeff_nil_of_star hM0 h1
    have e1 : shift a (S * τ) = (S.coeff [] • shift a M + shift a S) * τ := by
      rw [shift_mul, shift_star hM0 h1, add_mul, smul_mul']
    have e2 : shift a (S * τ * P + E) =
        (S.coeff [] • shift a M + shift a S) * τ * P + (S.coeff [] • shift a P + shift a E) := by
      rw [shift_add, shift_mul, e1, coeff_mul_nil, hτ0, mul_one]
      abel
    obtain ⟨S', E', hS', hE', r1, r2⟩ := ih _ _ (((hM.shift a).smul _).add (hS.shift a))
      (((hP.shift a).smul _).add (hE.shift a))
    exact ⟨S', E', hS', hE', by rw [lresW, e1, r1], by rw [lresW, e2, r2]⟩

/-- The right residual of `τ P` keeps this shape. -/
theorem rresW_star (hM : IsPoly M) (hM0 : M.coeff [] = 0) (h2 : τ = 1 + τ * M) (v : List α) :
    ∀ P : Ser α R, IsPoly P → ∃ P' : Ser α R, IsPoly P' ∧ rresW v (τ * P) = τ * P' := by
  induction v with
  | nil => exact fun P hP => ⟨P, hP, rfl⟩
  | cons c v ih =>
    intro P hP
    obtain ⟨P', hP', e⟩ := ih P hP
    refine ⟨rres c P' + P'.coeff [] • rres c M, (hP'.rres c).add ((hM.rres c).smul _), ?_⟩
    rw [rresW, e, rres_mul', rres_star hM0 h2, mul_add, mul_smul']

end Star

section Weak

variable {K : Type*} [Field K] {M τ : Ser α K}

/-- **Weak factorization.** If `u w v ∈ M*` for every word `w`, the series of all words is
`R₁ + S₁ τ P` with polynomials whose constant terms are `1 - τ(u) τ(v)`, `τ(u)` and `τ(v)`. -/
theorem weak_factorization (hM : IsPoly M) (hM0 : M.coeff [] = 0) (h1 : τ = 1 + M * τ)
    (h2 : τ = 1 + τ * M) {u v : List α} (hsync : ∀ w, τ.coeff (u ++ w ++ v) = 1) :
    ∃ R₁ S₁ P : Ser α K, IsPoly R₁ ∧ IsPoly S₁ ∧ IsPoly P ∧
      allWords = R₁ + S₁ * τ * P ∧ S₁.coeff [] = τ.coeff u ∧ P.coeff [] = τ.coeff v ∧
      R₁.coeff [] = 1 - τ.coeff u * τ.coeff v := by
  have hτ0 := coeff_nil_of_star hM0 h1
  obtain ⟨P, hP, eP⟩ := rresW_star hM hM0 h2 v 1 IsPoly.one
  rw [mul_one] at eP
  obtain ⟨S, E, hS, hE, eS, eSE⟩ := lresW_star hM hM0 h1 P hP u 1 0 IsPoly.one IsPoly.zero
  rw [add_zero, one_mul] at eSE
  rw [one_mul] at eS
  have hall : allWords = lresW u (rresW v τ) := by
    ext w
    rw [coeff_lresW, coeff_rresW, coeff_allWords, hsync]
  have hPc : P.coeff [] = τ.coeff v := by
    have := congrArg (fun f : Ser α K => f.coeff []) eP
    simpa [coeff_rresW, hτ0] using this.symm
  have hSc : S.coeff [] = τ.coeff u := by
    have := congrArg (fun f : Ser α K => f.coeff []) eS
    simpa [coeff_lresW, hτ0] using this.symm
  have hmain : allWords = E + S * τ * P := by rw [hall, eP, eSE, add_comm]
  refine ⟨E, S, P, hE, hS, hP, hmain, hSc, hPc, ?_⟩
  have := congrArg (fun f : Ser α K => f.coeff []) hmain
  simp only [coeff_allWords, coeff_add, coeff_mul_nil, hτ0, mul_one, hSc, hPc] at this
  rw [this]
  ring

end Weak

end Ser

end SmallestNoncompletable
