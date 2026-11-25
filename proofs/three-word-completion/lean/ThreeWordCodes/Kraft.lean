module

public import ThreeWordCodes.Statement
public import Mathlib.InformationTheory.Coding.KraftMcMillan
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Fin

/-! # Maximality of a finite code with a finite two-sided cover

A product on a finite set of codewords has summable Bernoulli weight if the
Kraft sum is strictly less than one. Two finite flanks preserve summability.
The full language has weight one at each length, so it cannot have such a cover.
-/

@[expose] public section
namespace ThreeWordCodes

private noncomputable def tuples (I : Type*) : (Σ n : ℕ, Fin n → I) ≃ List I :=
  Equiv.ofBijective (fun x => List.ofFn x.2) (by
    constructor
    · rintro ⟨n, x⟩ ⟨m, y⟩ h
      have len := congrArg List.length h
      simp only [List.length_ofFn] at len
      subst m
      exact congrArg (Sigma.mk n) (List.ofFn_injective h)
    · intro w
      exact ⟨⟨w.length, w.get⟩, by simp⟩)

private theorem tuple_product {I : Type*} [Fintype I] (f : I → ℝ) (n : ℕ) :
    (∑' x : Fin n → I, ((List.ofFn x).map f).prod) = (∑ i, f i)^n := by
  classical
  rw [tsum_fintype, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simp [List.map_ofFn, List.prod_ofFn]

private theorem list_product_summable {I : Type*} [Fintype I] (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Summable (fun w : List I => (w.map f).prod) ↔ (∑ i, f i) < 1 := by
  rw [← (tuples I).summable_iff]
  change Summable (fun x : Σ n : ℕ, Fin n → I => ((List.ofFn x.2).map f).prod) ↔ _
  rw [summable_sigma_of_nonneg (fun x => List.prod_nonneg (by simpa using fun i => hf (x.2 i)))]
  simp only [Summable.of_finite, forall_const, true_and, tuple_product]
  rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (by simp [hf]))]

private noncomputable def weight (A : Type*) [Fintype A] (w : Word A) : ℝ :=
  (1 / Fintype.card A : ℝ) ^ w.length

private theorem weight_append {A : Type*} [Fintype A] (u v : Word A) :
    weight A (u ++ v) = weight A u * weight A v := by simp [weight, pow_add]

private theorem weight_concatenate {A : Type*} [Fintype A] {M : Finset (Word A)}
    (s : List (↥M)) :
    weight A (concatenate s) = (s.map (fun x => weight A x.val)).prod := by
  induction s with
  | nil => simp [weight, concatenate]
  | cons x s ih =>
    simp only [List.map_cons, List.prod_cons]
    change weight A (x.val ++ concatenate s) = weight A x.val * _
    rw [weight_append, ih]

private theorem all_words_not_summable (A : Type*) [Fintype A] [Nonempty A] :
    ¬ Summable (weight A) := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : weight A = fun w : List A => (w.map (fun _ => (1 / Fintype.card A : ℝ))).prod := by
    funext w
    induction w with
    | nil => simp [weight]
    | cons a w ih =>
      simp only [List.map_cons, List.prod_cons]
      change (1 / Fintype.card A : ℝ) ^ (w.length+1) = (1 / Fintype.card A : ℝ) * (w.map _).prod
      rw [← ih]
      simp [weight, pow_succ, mul_comm]
  rw [e, list_product_summable _ (fun _ => by positivity)]
  simp [hcard]

private theorem bounded_flanks {I J K : Type*} [Finite I] [Finite K]
    (f : I → ℝ) (g : J → ℝ) (h : K → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ j, 0 ≤ g j) (hh : ∀ k, 0 ≤ h k) (hs : Summable g) :
    Summable (fun x : I × J × K => f x.1 * g x.2.1 * h x.2.2) := by
  classical
  rw [summable_prod_of_nonneg (fun x => mul_nonneg (mul_nonneg (hf _) (hg _)) (hh _))]
  refine ⟨fun i => ?_, Summable.of_finite⟩
  rw [summable_prod_of_nonneg (fun x => mul_nonneg (mul_nonneg (hf _) (hg _)) (hh _))]
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_mul_left]
  exact (hs.mul_left (f i)).mul_right _

/-- A finite two-sided cover of all words forces the Kraft sum to be at least one. -/
theorem one_le_kraft_of_cover {A : Type*} [Fintype A] [Nonempty A]
    (M P Q : Finset (Word A)) (hc : Function.Surjective (assemble M P Q)) :
    1 ≤ ∑ w ∈ M, (1 / Fintype.card A : ℝ)^w.length := by
  classical
  by_contra! hlt
  let f (x : ↥M) := weight A x.val
  have hf (x : ↥M) : 0 ≤ f x := by dsimp [f, weight]; positivity
  have hs : Summable (fun s : List (↥M) => (s.map f).prod) :=
    (list_product_summable f hf).mpr (by
      change (∑ x : ↥M, weight A x.val) < 1
      rwa [Finset.sum_coe_sort M (weight A)])
  have hd : Summable (fun z => weight A (assemble M P Q z)) := by
    simpa only [assemble, weight_append, weight_concatenate, f] using
      bounded_flanks (fun x : ↥Q => weight A x.val) _ (fun x : ↥P => weight A x.val)
        (fun _ => by dsimp [weight]; positivity)
        (fun s => List.prod_nonneg (fun x hx => by
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
          exact hf c))
        (fun _ => by dsimp [weight]; positivity) hs
  have rightInv := Function.rightInverse_surjInv hc
  exact all_words_not_summable A (by simpa [Function.comp_def, rightInv _] using
    (hd.comp_injective rightInv.injective))

/-- The competitor can be any set, finite or infinite. -/
theorem maximal_of_finite_flanks {A : Type*} [Fintype A] [Nonempty A]
    (M P Q : Finset (Word A)) (hm : InformationTheory.IsUniquelyDecodable (M : Set (Word A)))
    (hc : Function.Surjective (assemble M P Q)) : IsMaximalCode (M : Set (Word A)) := by
  classical
  refine ⟨hm, fun C hMC hC => Set.Subset.antisymm ?_ hMC⟩
  intro w hw
  by_contra hn
  have hsub : (↑(insert w M) : Set (Word A)) ⊆ C := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw
    · exact hMC hz
  have hi : InformationTheory.IsUniquelyDecodable (↑(insert w M) : Set (Word A)) :=
    fun xs ys hx hy e => hC xs ys (fun v hv => hsub (hx v hv)) (fun v hv => hsub (hy v hv)) e
  have upper := hi.finsetSum_one_div_card_pow_length_le_one
  rw [Finset.sum_insert (show w ∉ M from hn)] at upper
  have hd : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have extra : 0 < (1 / Fintype.card A : ℝ)^w.length := by positivity
  linarith [one_le_kraft_of_cover M P Q hc]

end ThreeWordCodes
