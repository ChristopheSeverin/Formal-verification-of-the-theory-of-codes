module

public import SubalgebraFreeness.GraphCriterion

/-! # The graph criterion for arbitrary rewriting graphs

The manuscript states its criterion for the underlying undirected multigraph. An edge `e` lies
on an undirected cycle exactly when its endpoints are joined by an undirected walk that avoids
`e`. This is how `OnCycle` is defined. A loop lies on a cycle of length one, since its endpoints
coincide. Each of two parallel edges lies on a cycle of length two, since the other one joins its
endpoints. The multigraph is a forest when no edge lies on a cycle.

* `exists_kernel_of_onCycle`: the signed sum of `e` and of a walk joining its endpoints is a
  kernel element of the incidence map with coefficient `1` at `e`.
* `kernel_eq_zero_of_not_onCycle`: an edge on no cycle has coefficient zero in every kernel
  element. Deleting it disconnects its endpoints, and summing the vertex coefficients over the
  component of its target gives, up to sign, its coefficient.
* `free_iff_forest`: if no cycle uses an edge `(1, i, 1)`, then `A` is free exactly when the
  multigraph is a forest. -/

@[expose] public section
namespace SubalgebraFreeness

variable {K : Type*} [Field K] {D S ι : Type*}

namespace Rules

variable (R : Rules D S ι)

/-- One undirected step along an edge other than `e`. -/
def StepWithout (e : Edge D ι) (x y : Vertex D S) : Prop :=
  ∃ e', e' ≠ e ∧ (R.src e' = x ∧ R.tgt e' = y ∨ R.src e' = y ∧ R.tgt e' = x)

/-- The edge `e` lies on an undirected cycle: an undirected walk avoiding `e` joins its target to
its source. -/
def OnCycle (e : Edge D ι) : Prop := Relation.ReflTransGen (R.StepWithout e) (R.tgt e) (R.src e)

/-- The underlying undirected multigraph is a forest. -/
def IsForest : Prop := ∀ e, ¬ R.OnCycle e

/-- A loop lies on a cycle of length one. -/
theorem onCycle_of_loop {e : Edge D ι} (he : R.src e = R.tgt e) : R.OnCycle e := by
  rw [OnCycle, he]

/-- Each of two parallel edges lies on a cycle of length two. -/
theorem onCycle_of_parallel {e e' : Edge D ι} (hne : e' ≠ e) (hs : R.src e' = R.src e)
    (ht : R.tgt e' = R.tgt e) : R.OnCycle e :=
  Relation.ReflTransGen.single ⟨e', hne, Or.inr ⟨hs, ht⟩⟩

/-- **A cycle gives a nonzero kernel element.** -/
theorem exists_kernel_of_onCycle {e : Edge D ι} (he : R.OnCycle e) :
    ∃ g : Edge D ι →₀ K, R.incidence K g = 0 ∧ g e = 1 := by
  classical
  -- A combination of edges other than `e` whose boundary is `tgt e - x`.
  have walk : ∀ x, Relation.ReflTransGen (R.StepWithout e) (R.tgt e) x →
      ∃ h : Edge D ι →₀ K, h e = 0 ∧
        R.incidence K h = Finsupp.single (R.tgt e) 1 - Finsupp.single x 1 := by
    intro x hx
    induction hx with
    | refl => exact ⟨0, rfl, by simp⟩
    | tail _ hstep ih =>
      obtain ⟨h, h0, hh⟩ := ih
      obtain ⟨e', hne, (⟨hs, ht⟩ | ⟨hs, ht⟩)⟩ := hstep
      · refine ⟨h + Finsupp.single e' 1, by simp [h0, Finsupp.single_eq_of_ne hne.symm], ?_⟩
        rw [map_add, hh, incidence_single, one_smul, hs, ht]
        abel
      · refine ⟨h - Finsupp.single e' 1, by simp [h0, Finsupp.single_eq_of_ne hne.symm], ?_⟩
        rw [map_sub, hh, incidence_single, one_smul, hs, ht]
        abel
  obtain ⟨h, h0, hh⟩ := walk _ he
  refine ⟨h + Finsupp.single e 1, ?_, by simp [h0]⟩
  rw [map_add, hh, incidence_single, one_smul]
  abel

/-- **An edge on no cycle has coefficient zero in every kernel element.** -/
theorem kernel_eq_zero_of_not_onCycle {e : Edge D ι} (he : ¬ R.OnCycle e)
    {g : Edge D ι →₀ K} (hg : R.incidence K g = 0) : g e = 0 := by
  classical
  -- The component of the target of `e` once `e` is deleted.
  let C : Set (Vertex D S) := {x | Relation.ReflTransGen (R.StepWithout e) (R.tgt e) x}
  have hsrc : R.src e ∉ C := he
  have htgt : R.tgt e ∈ C := Relation.ReflTransGen.refl
  have hother : ∀ e', e' ≠ e → (R.src e' ∈ C ↔ R.tgt e' ∈ C) := by
    intro e' hne
    exact ⟨fun h => h.tail ⟨e', hne, Or.inl ⟨rfl, rfl⟩⟩,
      fun h => h.tail ⟨e', hne, Or.inr ⟨rfl, rfl⟩⟩⟩
  -- Sum the vertex coefficients over the component.
  let χ : (Vertex D S →₀ K) →ₗ[K] K :=
    Finsupp.linearCombination K fun x => if x ∈ C then (1 : K) else 0
  have key : ∀ g : Edge D ι →₀ K, χ (R.incidence K g) = -g e := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => rw [map_add, map_add, hg, hg', Finsupp.add_apply, neg_add]
    | single e' c =>
      rw [incidence_single, map_smul, map_sub]
      simp only [χ, Finsupp.linearCombination_single, smul_eq_mul]
      by_cases hne : e' = e
      · subst hne
        simp [hsrc, htgt]
      · rw [Finsupp.single_eq_of_ne' hne]
        by_cases hs : R.src e' ∈ C
        · simp [hs, (hother e' hne).mp hs]
        · simp [hs, show R.tgt e' ∉ C from fun h => hs ((hother e' hne).mpr h)]
  have := key g
  rw [hg, map_zero, zero_eq_neg] at this
  exact this

/-- In a forest the incidence map is injective. -/
theorem incidence_injective_of_forest (h : R.IsForest) : Function.Injective (R.incidence K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  ext e
  exact R.kernel_eq_zero_of_not_onCycle (h e) hg

/-- **The graph criterion, forest direction.** If the multigraph is a forest, `A` is free on the
letters of `D` and one letter per rule. -/
theorem free_of_forest (h : R.IsForest) : Nonempty ((R.pres K).range ≃ₐ[K] Poly K (D ⊕ ι)) :=
  R.free_of_incidence_injective (R.incidence_injective_of_forest h)

/-- **The graph criterion, cycle direction.** If no cycle uses an edge `(1, i, 1)` and `A` is free
on some alphabet, the multigraph is a forest. -/
theorem forest_of_free (hbare : ∀ i, ¬ R.OnCycle ([], i, [])) {B : Type*}
    (e : (R.pres K).range ≃ₐ[K] Poly K B) : R.IsForest := by
  have hinj := R.incidence_injective_of_free (K := K)
    (fun g hg i => R.kernel_eq_zero_of_not_onCycle (hbare i) hg) e
  intro e' he'
  obtain ⟨g, hg, hge⟩ := R.exists_kernel_of_onCycle (K := K) he'
  have := hinj (hg.trans (map_zero _).symm)
  rw [this] at hge
  simp at hge

/-- **The graph criterion.** If no undirected cycle uses an edge `(1, i, 1)`, then `A` is a free
`K`-algebra exactly when the underlying undirected multigraph is a forest. -/
theorem free_iff_forest {D S ι : Type} (R : Rules D S ι) (hbare : ∀ i, ¬ R.OnCycle ([], i, [])) :
    (∃ B : Type, Nonempty ((R.pres K).range ≃ₐ[K] Poly K B)) ↔ R.IsForest :=
  ⟨fun ⟨_, ⟨e⟩⟩ => R.forest_of_free hbare e, fun h => ⟨_, R.free_of_forest h⟩⟩

end Rules

end SubalgebraFreeness
