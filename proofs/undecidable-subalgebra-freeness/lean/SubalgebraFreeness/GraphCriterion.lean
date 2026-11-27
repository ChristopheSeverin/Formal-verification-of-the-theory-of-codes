module

public import SubalgebraFreeness.Criterion
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Set.Finite.Basic

/-! # The graph criterion for rewriting graphs of outdegree at most one

The vertices are the words of `D* S D*`. Each rule `i` and each pair of words `u, v` over `D` give
an edge from `u ℓᵢ v` to `u rᵢ v`. When at most one edge leaves each vertex, every undirected
cycle is directed, and the directed cycles are the periodic points of the successor map.

* `incidence_kernel_periodic`: a kernel element of the incidence map vanishes on every edge whose
  source is not periodic.
* `incidence_not_injective`: a periodic vertex gives a nonzero kernel element.
* `free_of_no_periodic`, `not_free_of_periodic`: if no bare left side `ℓᵢ` is periodic, then
  `A` is free exactly when no vertex is periodic. This is the manuscript's criterion in the
  outdegree-one case. -/

@[expose] public section
namespace SubalgebraFreeness

open MonoidAlgebra

variable {K : Type*} [Field K] {D S ι : Type*}

namespace Rules

variable (R : Rules D S ι)

/-! ### Freeness and the incidence map -/

variable (K D ι) in
/-- Combinations of edges as polynomials in the presentation alphabet. -/
noncomputable def edgePoly : (Edge D ι →₀ K) →ₗ[K] Poly K (D ⊕ ι) :=
  (coeffLinearEquiv K).symm.toLinearMap ∘ₗ Finsupp.lmapDomain K K eword

variable (K D S) in
/-- Combinations of vertices as polynomials. -/
noncomputable def vertexPoly : (Vertex D S →₀ K) →ₗ[K] Poly K (D ⊕ S) :=
  (coeffLinearEquiv K).symm.toLinearMap ∘ₗ Finsupp.lmapDomain K K vword

theorem pres_edgePoly (g : Edge D ι →₀ K) :
    R.pres K (edgePoly K D ι g) = vertexPoly K D S (R.incidence K g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => rw [map_add, map_add, hg, hg', map_add, map_add]
  | single e c =>
    rw [incidence_single, map_smul, map_sub]
    simp only [edgePoly, vertexPoly, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      coeffLinearEquiv_symm_apply]
    rw [show ofCoeff (Finsupp.single (eword e) c) = c • (mono (eword e) : Poly K (D ⊕ ι)) by
      simp [mono], map_smul, pres_eword]
    simp [mono, smul_sub]

theorem edgePoly_injective : Function.Injective (edgePoly K D ι) := by
  intro g g' h
  have h' := congrArg MonoidAlgebra.coeff h
  simp only [edgePoly, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    coeffLinearEquiv_symm_apply, Finsupp.lmapDomain_apply] at h'
  exact Finsupp.mapDomain_injective eword_injective h'

theorem incidence_injective_of_pres_injective (h : Function.Injective (R.pres K)) :
    Function.Injective (R.incidence K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  apply edgePoly_injective (K := K)
  rw [map_zero]
  apply h
  rw [pres_edgePoly, hg, map_zero, map_zero]

/-- If the incidence map is injective, `A` is free on the letters of `D` and one letter per rule. -/
theorem free_of_incidence_injective (h : Function.Injective (R.incidence K)) :
    Nonempty ((R.pres K).range ≃ₐ[K] Poly K (D ⊕ ι)) :=
  ⟨(AlgEquiv.ofInjective (R.pres K) (R.pres_injective h)).symm⟩

/-- If no kernel element involves a bare rule letter and `A` is free, the incidence map is
injective. -/
theorem incidence_injective_of_free
    (hbare : ∀ g : Edge D ι →₀ K, R.incidence K g = 0 → ∀ i, g ([], i, []) = 0)
    {B : Type*} (e : (R.pres K).range ≃ₐ[K] Poly K B) : Function.Injective (R.incidence K) := by
  apply incidence_injective_of_pres_injective
  apply injective_of_free (R.pres K) _ (R.highOrder_of_pres_eq_zero hbare) e
  intro x
  rw [pres, polyLift_letter]
  exact R.constCoeff_gen x

/-! ### Outdegree at most one -/

/-- At most one edge leaves each vertex. -/
def Functional : Prop := ∀ e e' : Edge D ι, R.src e = R.src e' → e = e'

open Classical in
/-- The successor of a vertex, if an edge leaves it. -/
noncomputable def next (x : Vertex D S) : Option (Vertex D S) :=
  if h : ∃ e, R.src e = x then some (R.tgt h.choose) else none

/-- The successor map on `Option`, with `none` absorbing. -/
noncomputable def nextO : Option (Vertex D S) → Option (Vertex D S) := fun o => o.bind R.next

/-- A vertex lies on a directed cycle. -/
def Periodic (x : Vertex D S) : Prop := ∃ n, 0 < n ∧ R.nextO^[n] (some x) = some x

theorem next_src (hf : R.Functional) (e : Edge D ι) : R.next (R.src e) = some (R.tgt e) := by
  have h : ∃ e', R.src e' = R.src e := ⟨e, rfl⟩
  rw [next, dite_eq_left h, hf _ _ h.choose_spec]

theorem next_eq_some {x y : Vertex D S} (h : R.next x = some y) :
    ∃ e, R.src e = x ∧ R.tgt e = y := by
  unfold next at h
  split_ifs at h with he
  · exact ⟨he.choose, he.choose_spec, Option.some_inj.mp h⟩

theorem nextO_some (x : Vertex D S) : R.nextO (some x) = R.next x := rfl

theorem nextO_none (n : ℕ) : R.nextO^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, show R.nextO none = none from rfl, ih]

/-- A vertex reached from a periodic vertex is periodic. -/
theorem Periodic.of_reach {x y : Vertex D S} (hx : R.Periodic x) {m : ℕ}
    (hy : R.nextO^[m] (some x) = some y) : R.Periodic y := by
  obtain ⟨n, hn, hxn⟩ := hx
  refine ⟨n, hn, ?_⟩
  rw [← hy, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hxn]

/-- A kernel element of the incidence map vanishes on every edge whose source is not periodic. -/
theorem incidence_kernel_periodic (hf : R.Functional) {g : Edge D ι →₀ K}
    (hg : R.incidence K g = 0) {e : Edge D ι} (he : g e ≠ 0) : R.Periodic (R.src e) := by
  classical
  -- The coefficient of the edge leaving a vertex, if any.
  let out : Vertex D S → K := fun x => if h : ∃ e, R.src e = x then g h.choose else 0
  have hout : ∀ e, out (R.src e) = g e := by
    intro e
    have h : ∃ e', R.src e' = R.src e := ⟨e, rfl⟩
    simp only [out, dite_eq_left h, hf _ _ h.choose_spec]
  have hout_sum : ∀ x, out x = ∑ e' ∈ g.support.filter (fun e' => R.src e' = x), g e' := by
    intro x
    by_cases hx : ∃ e, R.src e = x
    · simp only [out, dite_eq_left hx]
      rw [Finset.sum_eq_single hx.choose]
      · intro e' he' hne
        exact absurd (hf _ _ ((Finset.mem_filter.mp he').2.trans hx.choose_spec.symm)) hne
      · intro hnot
        rw [Finset.mem_filter, not_and] at hnot
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.mpr hne) hx.choose_spec
    · simp only [out, dite_eq_right hx]
      rw [Finset.sum_eq_zero]
      intro e' he'
      exact absurd ⟨e', (Finset.mem_filter.mp he').2⟩ hx
  -- Balance at each vertex: the outgoing coefficient equals the incoming sum.
  have balance : ∀ x, out x = ∑ e' ∈ g.support.filter (fun e' => R.tgt e' = x), g e' := by
    intro x
    have hx0 := congrArg (fun f => f x) hg
    have expand : (R.incidence K g) x =
        (∑ e' ∈ g.support.filter (fun e' => R.src e' = x), g e') -
          ∑ e' ∈ g.support.filter (fun e' => R.tgt e' = x), g e' := by
      simp only [incidence, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, Finset.sum_filter]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e' _ => ?_
      by_cases h1 : R.src e' = x <;> by_cases h2 : R.tgt e' = x <;>
        simp [h1, h2]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hx0
    rw [expand, sub_eq_zero] at hx0
    rw [hout_sum, hx0]
  -- A vertex with nonzero outgoing coefficient has such a predecessor.
  have pred : ∀ x, out x ≠ 0 → ∃ y, out y ≠ 0 ∧ R.next y = some x := by
    intro x hx
    rw [balance] at hx
    obtain ⟨e', he', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have he'' := Finset.mem_filter.mp he'
    refine ⟨R.src e', by rw [hout]; exact hne, ?_⟩
    rw [next_src R hf, he''.2]
  choose! p hp using pred
  -- Follow predecessors inside the finite support until a vertex repeats.
  set x := R.src e
  have hx : out x ≠ 0 := by rw [hout]; exact he
  let seq : ℕ → Vertex D S := fun k => p^[k] x
  have hseq : ∀ k, out (seq k) ≠ 0 := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      simp only [seq, Function.iterate_succ_apply']
      exact (hp _ ih).1
  have hstep : ∀ k, R.nextO^[k] (some (seq k)) = some x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, nextO_some]
      simp only [seq, Function.iterate_succ_apply'] at ih ⊢
      rw [(hp _ (hseq k)).2]
      exact ih
  have hfin : Set.Finite (Set.range seq) := by
    refine (g.support.image R.src).finite_toSet.subset ?_
    rintro _ ⟨k, rfl⟩
    have hk := hseq k
    simp only [out] at hk
    split_ifs at hk with h
    · exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨h.choose, Finsupp.mem_support_iff.mpr hk, h.choose_spec⟩)
    · exact absurd rfl hk
  obtain ⟨a, b, hab, heq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem (f := seq) (fun k => Set.mem_range_self k) hfin
  refine ⟨b - a, by omega, ?_⟩
  have h1 := hstep b
  rw [← heq] at h1
  calc R.nextO^[b - a] (some x) = R.nextO^[b - a] (R.nextO^[a] (some (seq a))) := by
        rw [hstep a]
    _ = R.nextO^[b] (some (seq a)) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    _ = some x := h1

/-- The iterates of a periodic vertex are vertices. -/
theorem Periodic.iterate_isSome {x : Vertex D S} (hx : R.Periodic x) (k : ℕ) :
    (R.nextO^[k] (some x)).isSome := by
  obtain ⟨n, hn, hxn⟩ := hx
  by_contra hnone
  rw [Option.not_isSome_iff_eq_none] at hnone
  have hmul : ∀ m, R.nextO^[n * m] (some x) = some x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add_apply, hxn, ih]
  have : R.nextO^[n * k] (some x) = none := by
    have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    rw [show n * k = (n * k - k) + k by omega, Function.iterate_add_apply, hnone, nextO_none]
  rw [hmul] at this
  exact Option.some_ne_none x this

/-- A periodic vertex gives a nonzero kernel element of the incidence map: the sum of the edges
around its cycle. -/
theorem incidence_not_injective {x : Vertex D S}
    (hx : R.Periodic x) : ¬ Function.Injective (R.incidence K) := by
  classical
  intro hinj
  have hmem : some x ∈ Function.periodicPts R.nextO := by
    obtain ⟨n, hn, hxn⟩ := hx
    exact ⟨n, hn, hxn⟩
  set n := Function.minimalPeriod R.nextO (some x) with hn
  have hnpos : 0 < n := Function.minimalPeriod_pos_of_mem_periodicPts hmem
  -- The vertices and edges around the cycle.
  let orbit : ℕ → Vertex D S := fun k => (R.nextO^[k] (some x)).get (hx.iterate_isSome R k)
  have horbit : ∀ k, R.nextO^[k] (some x) = some (orbit k) := fun k => by simp [orbit]
  have hnext : ∀ k, R.next (orbit k) = some (orbit (k + 1)) := by
    intro k
    rw [← nextO_some, ← horbit k, (Function.iterate_succ_apply' (f := R.nextO) k (some x)).symm,
      horbit]
  choose edge hedge using fun k => R.next_eq_some (hnext k)
  have hperiod : orbit n = orbit 0 := by
    apply Option.some_injective
    rw [← horbit, ← horbit, hn, Function.iterate_minimalPeriod]
    rfl
  let f : Edge D ι →₀ K := ∑ k ∈ Finset.range n, Finsupp.single (edge k) 1
  have hf0 : R.incidence K f = 0 := by
    simp only [f, map_sum, incidence_single, one_smul]
    have : ∀ k ∈ Finset.range n, Finsupp.single (R.src (edge k)) (1 : K) -
        Finsupp.single (R.tgt (edge k)) 1 =
        Finsupp.single (orbit k) 1 - Finsupp.single (orbit (k + 1)) 1 := by
      intro k _
      rw [(hedge k).1, (hedge k).2]
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun k => Finsupp.single (orbit k) (1 : K)),
      hperiod, sub_self]
  have hfe : f (edge 0) = 1 := by
    simp only [f, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [Finsupp.single_eq_of_ne']
      intro heq
      apply hk0
      have hsrc : orbit k = orbit 0 := by rw [← (hedge k).1, ← (hedge 0).1, heq]
      have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := R.nextO) (x := some x)
      apply hinj (Finset.mem_range.mp hk) hnpos
      simp only [horbit, hsrc]
    · intro h0
      exact absurd (Finset.mem_range.mpr hnpos) h0
  have : f = 0 := hinj (hf0.trans (map_zero _).symm)
  rw [this] at hfe
  simp at hfe

/-- If no vertex is periodic, the incidence map is injective. -/
theorem incidence_injective_of_no_periodic (hf : R.Functional) (h : ∀ x, ¬ R.Periodic x) :
    Function.Injective (R.incidence K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  ext e
  by_contra he
  exact h _ (R.incidence_kernel_periodic hf hg he)

theorem src_bare (i : ι) : R.src ([], i, []) = R.lhs i := by
  simp [src, put]

/-- **The graph criterion, forest direction.** Without periodic vertices `A` is free on `D ∪ Z`. -/
theorem free_of_no_periodic (hf : R.Functional) (h : ∀ x, ¬ R.Periodic x) :
    Nonempty ((R.pres K).range ≃ₐ[K] Poly K (D ⊕ ι)) :=
  R.free_of_incidence_injective (R.incidence_injective_of_no_periodic hf h)

/-- **The graph criterion, cycle direction.** If no bare left side `ℓᵢ` is periodic, a periodic
vertex prevents `A` from being free on any alphabet. -/
theorem not_free_of_periodic (hf : R.Functional) (hbare : ∀ i, ¬ R.Periodic (R.lhs i))
    {x : Vertex D S} (hx : R.Periodic x) {B : Type*} :
    IsEmpty ((R.pres K).range ≃ₐ[K] Poly K B) := by
  refine ⟨fun e => R.incidence_not_injective (K := K) hx ?_⟩
  refine R.incidence_injective_of_free (fun g hg i => ?_) e
  by_contra hne
  exact hbare i (R.src_bare i ▸ R.incidence_kernel_periodic hf hg hne)

end Rules

end SubalgebraFreeness
