module

public import SubalgebraFreeness.Poly
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Relations of order two in a free presentation

Let `π : K⟨X⟩ → K⟨Y⟩` preserve constant terms and have every relation in `I²`, where `I` is the
zero-constant-term ideal. If the image `A` of `π` is itself a free algebra, then `π` is injective.

This is the manuscript's argument with `J = π(I)`. Translating the free generators of `A` by their
constant terms makes `J` the ideal of polynomials without constant term in those coordinates.
Relations in `I²` make the linear parts of the images of the letters independent. Sending these
linear forms back to their letters gives an endomorphism of `K⟨X⟩` that fixes every letter modulo
`I²`, and such an endomorphism is injective. -/

@[expose] public section
namespace SubalgebraFreeness

open MonoidAlgebra

variable {K : Type*} [Field K] {X Y : Type*}

/-- The `K`-algebra homomorphism determined by the images of the letters. -/
noncomputable def polyLift {A : Type*} [Semiring A] [Algebra K A] (f : X → A) : Poly K X →ₐ[K] A :=
  MonoidAlgebra.lift K A (FreeMonoid X) (FreeMonoid.lift f)

@[simp] theorem polyLift_letter {A : Type*} [Semiring A] [Algebra K A] (f : X → A) (x : X) :
    polyLift f (letter x : Poly K X) = f x := by
  simp [polyLift, letter, mono]

theorem algHom_ext_letter {A : Type*} [Semiring A] [Algebra K A] {φ ψ : Poly K X →ₐ[K] A}
    (h : ∀ x, φ (letter x) = ψ (letter x)) : φ = ψ := by
  apply MonoidAlgebra.algHom_ext'
  · apply FreeMonoid.hom_eq
    intro x
    exact h x
  · exact Subsingleton.elim _ _

/-- The coefficients of the one-letter words. -/
noncomputable def linPart : Poly K X →ₗ[K] (X →₀ K) :=
  (Finsupp.lcomapDomain FreeMonoid.of FreeMonoid.of_injective).comp
    (coeffLinearEquiv K).toLinearMap

theorem linPart_apply (p : Poly K X) (x : X) : linPart p x = p.coeff (FreeMonoid.of x) := rfl

/-- A linear combination of letters. -/
noncomputable def linEmb : (X →₀ K) →ₗ[K] Poly K X := Finsupp.linearCombination K letter

theorem linEmb_letter (v : X →₀ K) (x : X) : (linEmb v).coeff (FreeMonoid.of x) = v x := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => rw [map_add, coeff_add, Finsupp.add_apply, hv, hv', Finsupp.add_apply]
  | single y c =>
    rw [linEmb, Finsupp.linearCombination_single, coeff_smul_apply, letter, mono, coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · subst h; simp
    · rw [ite_eq_right (fun e => h (FreeMonoid.of_injective e)), ite_eq_right h, smul_zero]

theorem linEmb_coeff_of_length_ne (v : X →₀ K) {w : FreeMonoid X} (hw : w.toList.length ≠ 1) :
    (linEmb v).coeff w = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => rw [map_add, coeff_add, Finsupp.add_apply, hv, hv', add_zero]
  | single y c =>
    rw [linEmb, Finsupp.linearCombination_single, coeff_smul_apply, letter, mono, coeff_single,
      Finsupp.single_apply, ite_eq_right, smul_zero]
    rintro rfl
    exact hw rfl

theorem highOrder_linEmb (v : X →₀ K) : HighOrder 1 (linEmb v) :=
  fun _ hw => linEmb_coeff_of_length_ne v (by omega)

/-- A polynomial without constant term is its linear part plus an element of `I²`. -/
theorem highOrder_sub_linEmb {q : Poly K X} (hq : constCoeff q = 0) :
    HighOrder 2 (q - linEmb (linPart q)) := by
  intro w hw
  rw [coeff_sub, Finsupp.sub_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h0 | h1
  · have hw' : w = 1 := FreeMonoid.ext (List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp h0))
    subst hw'
    rw [linEmb_coeff_of_length_ne _ (by simp), ← constCoeff_apply, hq, sub_zero]
  · obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp h1
    have hw' : w = FreeMonoid.of y := FreeMonoid.ext hy
    subst hw'
    rw [linEmb_letter, linPart_apply, sub_self]

/-- An algebra homomorphism sends a polynomial of order two to a polynomial of order two as soon
as it sends letters to polynomials without constant term. -/
theorem highOrder_polyLift {Z : Type*} (f : X → Poly K Z) (hf : ∀ x, HighOrder 1 (f x)) {n : ℕ}
    {p : Poly K X} (hp : HighOrder n p) : HighOrder n (polyLift f p) :=
  HighOrder.map (polyLift f) (fun x => by simpa using hf x) hp

/-- **Order-two relations.** A constant-term-preserving homomorphism onto a free algebra whose
relations all lie in `I²` is injective. -/
theorem injective_of_free {B : Type*} (π : Poly K X →ₐ[K] Poly K Y)
    (hconst : ∀ x, constCoeff (π (letter x)) = 0)
    (hker : ∀ f, π f = 0 → HighOrder 2 f)
    (e : π.range ≃ₐ[K] Poly K B) : Function.Injective π := by
  classical
  -- The constant term is preserved.
  have hε : ∀ f, constCoeff (π f) = constCoeff f := by
    intro f
    have := algHom_ext_letter (φ := constCoeff.comp π) (ψ := (constCoeff : Poly K X →ₐ[K] K))
      (fun x => by
        rw [AlgHom.comp_apply, hconst, constCoeff_apply]
        simp [letter, mono])
    exact congrArg (fun φ : Poly K X →ₐ[K] K => φ f) this
  -- Translate the free generators by their constant terms.
  let σ : Poly K B ≃ₐ[K] π.range := e.symm
  let c : B → K := fun b => constCoeff ((σ (letter b) : π.range) : Poly K Y)
  let τ : Poly K B →ₐ[K] Poly K B := polyLift fun b => letter b - algebraMap K _ (c b)
  let τ' : Poly K B →ₐ[K] Poly K B := polyLift fun b => letter b + algebraMap K _ (c b)
  have hττ' : τ.comp τ' = AlgHom.id K _ := algHom_ext_letter fun b => by
    simp only [τ, τ', AlgHom.comp_apply, polyLift_letter, map_add, AlgHom.commutes,
      sub_add_cancel, AlgHom.id_apply]
  have hτ'τ : τ'.comp τ = AlgHom.id K _ := algHom_ext_letter fun b => by
    simp only [τ, τ', AlgHom.comp_apply, polyLift_letter, map_sub, AlgHom.commutes,
      add_sub_cancel_right, AlgHom.id_apply]
  let τe : Poly K B ≃ₐ[K] Poly K B := AlgEquiv.ofAlgHom τ τ' hττ' hτ'τ
  let σ' : Poly K B ≃ₐ[K] π.range := τe.trans σ
  have hσ'letter : ∀ b, ((σ' (letter b) : π.range) : Poly K Y) =
      ((σ (letter b) : π.range) : Poly K Y) - algebraMap K _ (c b) := by
    intro b
    change ((σ (τ (letter b)) : π.range) : Poly K Y) = _
    rw [polyLift_letter, map_sub, AlgEquiv.commutes, Subalgebra.coe_sub,
      Subalgebra.coe_algebraMap]
  have hσ'const : ∀ r, constCoeff ((σ' r : π.range) : Poly K Y) = constCoeff r := by
    intro r
    have := algHom_ext_letter
      (φ := (constCoeff : Poly K Y →ₐ[K] K).comp (π.range.val.comp (σ' : Poly K B →ₐ[K] π.range)))
      (ψ := (constCoeff : Poly K B →ₐ[K] K)) (fun b => by
        change constCoeff ((σ' (letter b) : π.range) : Poly K Y) = constCoeff (letter b)
        rw [hσ'letter, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
          sub_self, constCoeff_apply]
        simp [letter, mono])
    exact congrArg (fun φ : Poly K B →ₐ[K] K => φ r) this
  -- Elements of `J` lift to `I`, and elements of `J²` lift to `I²`.
  have lift₁ : ∀ s : Poly K B, HighOrder 1 s →
      ∃ f : Poly K X, HighOrder 1 f ∧ π f = (σ' s : Poly K Y) := by
    intro s hs
    obtain ⟨f, hf⟩ := (AlgHom.mem_range π).mp (σ' s).property
    refine ⟨f, ?_, hf⟩
    rw [highOrder_one_iff, ← hε, hf, hσ'const, ← highOrder_one_iff]
    exact hs
  have lift₂ : ∀ r : Poly K B, HighOrder 2 r →
      ∃ f : Poly K X, HighOrder 2 f ∧ π f = (σ' r : Poly K Y) := by
    intro r hr
    rw [sum_single r]
    refine Finset.sum_induction _ (fun g => ∃ f : Poly K X, HighOrder 2 f ∧ π f = (σ' g : Poly K Y))
      ?_ ?_ ?_
    · rintro g g' ⟨f, hf, hπ⟩ ⟨f', hf', hπ'⟩
      exact ⟨f + f', hf.add hf', by rw [map_add, hπ, hπ', map_add, Subalgebra.coe_add]⟩
    · exact ⟨0, HighOrder.zero, by simp⟩
    · intro w hw
      have hlen : 2 ≤ w.toList.length := by
        by_contra hlt
        exact (Finsupp.mem_support_iff.mp hw) (hr w (by omega))
      obtain ⟨b, w', rfl⟩ : ∃ b w', w = FreeMonoid.of b * w' := by
        cases w using FreeMonoid.mulCasesOn with
        | one => simp at hlen
        | of_mul b w' => exact ⟨b, w', rfl⟩
      have hw' : 1 ≤ w'.toList.length := by
        simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.length_append,
          List.length_singleton] at hlen
        omega
      obtain ⟨f₁, hf₁, h₁⟩ := lift₁ (letter b) (by
        simpa [letter, mono] using highOrder_single (FreeMonoid.of b) (1 : K))
      obtain ⟨f₂, hf₂, h₂⟩ := lift₁ (mono w') ((highOrder_single w' 1).mono' hw')
      refine ⟨r.coeff (FreeMonoid.of b * w') • (f₁ * f₂), (hf₁.mul hf₂).smul _, ?_⟩
      rw [map_smul π, map_mul π, h₁, h₂, mono_mul, map_smul σ', map_mul σ', Subalgebra.coe_smul,
        Subalgebra.coe_mul]
      rfl
  -- The linear parts of the images of the letters are independent.
  let q : X → Poly K B := fun x => σ'.symm ⟨π (letter x), AlgHom.mem_range_self π _⟩
  let v : X → B →₀ K := fun x => linPart (q x)
  have hq : ∀ x, (σ' (q x) : Poly K Y) = π (letter x) := fun x => by simp [q]
  have hqconst : ∀ x, constCoeff (q x) = 0 := fun x => by
    rw [← hσ'const, hq, hconst]
  have indep : Function.Injective (Finsupp.linearCombination K v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    let p : Poly K X := linEmb a
    let r : Poly K B := σ'.symm ⟨π p, AlgHom.mem_range_self π _⟩
    have hr_sum : r = ∑ x ∈ a.support, a x • q x := by
      apply σ'.injective
      apply Subtype.ext
      rw [AlgEquiv.apply_symm_apply, map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [p, map_smul, Subalgebra.coe_smul, hq, linEmb, Finsupp.linearCombination_apply,
        Finsupp.sum, map_sum]
    have hrlin : linPart r = 0 := by
      rw [hr_sum, map_sum]
      simpa [v, Finsupp.linearCombination_apply, Finsupp.sum] using ha
    have hrconst : constCoeff r = 0 := by
      rw [← hσ'const]
      simp only [r, AlgEquiv.apply_symm_apply, hε, p]
      rw [← highOrder_one_iff]
      exact highOrder_linEmb a
    have hr2 : HighOrder 2 r := by simpa [hrlin] using highOrder_sub_linEmb hrconst
    obtain ⟨f, hf, hπf⟩ := lift₂ r hr2
    have hpf : HighOrder 2 (p - f) := hker _ (by simp [map_sub, hπf, r])
    have hp2 : HighOrder 2 p := by simpa using hpf.add hf
    ext x
    have := hp2 (FreeMonoid.of x) (by simp)
    rwa [linEmb_letter] at this
  -- A left inverse on linear forms extends to an endomorphism fixing letters modulo `I²`.
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination K v)
    (LinearMap.ker_eq_bot.mpr indep)
  have hGv : ∀ x, G (v x) = Finsupp.single x 1 := fun x => by
    have := congrArg (fun φ : (X →₀ K) →ₗ[K] (X →₀ K) => φ (Finsupp.single x 1)) hG
    simpa [Finsupp.linearCombination_single] using this
  let Φ : Poly K B →ₐ[K] Poly K X := polyLift fun b => linEmb (G (Finsupp.single b 1))
  have hΦlin : ∀ u : B →₀ K, Φ (linEmb u) = linEmb (G u) := by
    intro u
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]
    | single b k =>
      rw [linEmb, Finsupp.linearCombination_single, map_smul, polyLift_letter]
      rw [← map_smul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  let ψ : Poly K X →ₐ[K] Poly K X := Φ.comp (σ'.symm.toAlgHom.comp π.rangeRestrict)
  have hψ : ∀ x, HighOrder 2 (ψ (letter x) - letter x) := by
    intro x
    have hqx : ψ (letter x) = Φ (q x) := rfl
    have split := highOrder_sub_linEmb (hqconst x)
    have hΦsplit : HighOrder 2 (Φ (q x - linEmb (linPart (q x)))) :=
      highOrder_polyLift _ (fun b => highOrder_linEmb _) split
    rw [map_sub, hΦlin] at hΦsplit
    have hlx : linEmb (G (linPart (q x))) = (letter x : Poly K X) := by
      change linEmb (G (v x)) = _
      rw [hGv, linEmb, Finsupp.linearCombination_single, one_smul]
    rwa [hlx, ← hqx] at hΦsplit
  have hψinj := injective_of_letters ψ hψ
  intro f g hfg
  apply hψinj
  simp only [ψ, AlgHom.comp_apply]
  congr 2
  exact Subtype.ext hfg

end SubalgebraFreeness
