module

public import ThreeWordCodes.FirstLongGap
public import ThreeWordCodes.PureMargins

/-! # Restricting Proposition 6 to a strictly interior minimum -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

/-- Every remaining candidate has an interior short gap that is globally
minimal and strictly smaller than both endpoint gaps. -/
def InteriorMinimumConstruction : Prop :=
  ∀ (k l f t : ℕ) (middle : List ℕ), 0<k → 0<l →
    (∀ z ∈ f::(middle++[t]), max k l ≤ z) →
    (∃ m ∈ middle, m<f ∧ m<t ∧ m<k+l ∧ ∀ z ∈ f::(middle++[t]), m≤z) →
    NamedCode (oneMarker k l (mixed 0 (f::(middle++[t])) 0)) →
    Completable (oneMarker k l (mixed 0 (f::(middle++[t])) 0))

private theorem ends_or_interior (f t : ℕ) (middle : List ℕ) :
    (∀ x∈middle++[t], f≤x) ∨ (∀ x∈f::middle,t≤x) ∨
      ∃ m ∈ middle, m<f ∧ m<t ∧ ∀ z ∈ f::(middle++[t]), m≤z := by
  let xs := f::(middle++[t])
  let D := xs.toFinset
  have nonempty : D.Nonempty := ⟨f,by simp [D,xs]⟩
  let m := D.min' nonempty
  have low (z : ℕ) (mem : z∈xs) : m≤z := Finset.min'_le D z (List.mem_toFinset.mpr mem)
  have mem : m∈xs := List.mem_toFinset.mp (Finset.min'_mem D nonempty)
  by_cases first : m=f
  · exact Or.inl (fun z mz => first ▸ low z (List.mem_cons_of_mem _ mz))
  by_cases last : m=t
  · exact Or.inr (Or.inl (fun z mz => last ▸ low z (by
      rcases List.mem_cons.mp mz with rfl | h
      · simp [xs]
      · simp [xs,h])))
  · have mf := low f (by simp [xs])
    have mt := low t (by simp [xs])
    have interior : m∈middle := by simpa [xs,first,last] using mem
    exact Or.inr (Or.inr ⟨m,interior,by omega,by omega,low⟩)

theorem one_marker_iff_interior_minimum : OneMarkerConstruction ↔ InteriorMinimumConstruction := by
  constructor
  · intro all k l f t middle pk pl bounds ⟨m,mem,_,_,short,_⟩ code
    exact all k l _ pk pl bounds ⟨m,by simp [mem],short⟩ code
  · intro interior k l xs pk pl bounds short code
    cases xs with
    | nil => simp at short
    | cons f rest =>
      induction rest using List.reverseRecOn with
      | nil => exact minimum_first_gap_completion k l f [] (by simp) code
      | append_singleton middle t _ =>
        rcases ends_or_interior f t middle with first | last | ⟨m,mem,lowF,lowT,all⟩
        · exact minimum_first_gap_completion k l f (middle++[t]) first code
        · exact minimum_last_gap_completion k l t (f::middle) last code
        · obtain ⟨z,hz,sz⟩ := short
          exact interior k l f t middle pk pl bounds ⟨m,mem,lowF,lowT,(all z hz).trans_lt sz,all⟩ code

/-- The whole arbitrary-alphabet Proposition 6 is equivalent to the
strict-interior-minimum family above. -/
theorem pure_power_iff_interior_minimum : PurePowerTheorem.{0} ↔ InteriorMinimumConstruction :=
  pure_power_iff_one_marker.trans one_marker_iff_interior_minimum

end ThreeWordCodes.BinaryGaps
