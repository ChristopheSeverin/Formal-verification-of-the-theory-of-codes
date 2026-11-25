module

public import ThreeWordCodes.Substitution

/-! # Shortening and completion of a noncommuting pair -/

@[expose] public section
namespace ThreeWordCodes
variable {A I J : Type*}

def Completable (v : I → Word A) : Prop := NamedCode v ∧ HasPositiveCompletion (Set.range v)

theorem Completable.substitute [Fintype A] [Nonempty I] {v : I → Word A} {w : J → Word I}
    (hv : Completable v) (hw : Completable w) : Completable (fun j => spell v (w j)) := by
  refine ⟨hv.1.substitution hw.1, ?_⟩
  apply (completion_substitution hv.1.entries_injective hv.2 hw.2).mono
  rintro _ ⟨j, rfl⟩
  exact ⟨w j, ⟨j, rfl⟩, rfl⟩

theorem completable_prefix [Fintype A] [Fintype I] {v : I → Word A}
    (hi : Function.Injective v) (he : ∀ i, v i ≠ [])
    (hp : InformationTheory.IsPrefixFree (Set.range v)) : Completable v := by
  classical
  have hc := hp.isUniquelyDecodable (by rintro ⟨i, h⟩; exact he i h)
  let X := Finset.univ.image v
  have eqset : (X : Set (Word A)) = Set.range v := by simp [X]
  refine ⟨(namedCode_iff_range _).mpr ⟨hi, hc⟩, ?_⟩
  rw [← eqset] at hc hp ⊢
  exact prefix_case X hc hp

theorem Completable.reverse [Fintype A] {v : I → Word A} (h : Completable v) :
    Completable (fun i => (v i).reverse) := by
  refine ⟨h.1.reverse, h.2.reverse.mono ?_⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨v i, ⟨i, rfl⟩, rfl⟩

theorem first_marked_completion [Fintype I] (t : I → Word I) :
    Completable (fun i => i :: t i) := by
  apply completable_prefix (first_marked_code t).entries_injective (by simp)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ ⟨s, e⟩
  obtain ⟨rfl, _⟩ := List.cons.inj e
  rfl

theorem last_marked_completion [Fintype I] (t : I → Word I) :
    Completable (fun i => t i ++ [i]) := by
  simpa using (first_marked_completion (fun i => (t i).reverse)).reverse

/-- Adding an arbitrary word on the names to the left of each entry lifts completion. -/
theorem Completable.padLeft [Fintype A] [Fintype I] [Nonempty I] {v : I → Word A}
    (h : Completable v) (t : I → Word I) : Completable (fun i => spell v (t i) ++ v i) := by
  simpa using h.substitute (last_marked_completion t)

theorem Completable.padRight [Fintype A] [Fintype I] [Nonempty I] {v : I → Word A}
    (h : Completable v) (t : I → Word I) : Completable (fun i => v i ++ spell v (t i)) :=
  h.substitute (first_marked_completion t)

def pair (u v : Word A) : Bool → Word A
  | false => u
  | true => v

private theorem left_step [Fintype A] {u v : Word A} (h : Completable (pair u v)) :
    Completable (pair u (u ++ v)) := by
  have e : (fun i => spell (pair u v) (if i then [false] else []) ++ pair u v i) = pair u (u ++ v) := by
    funext i
    cases i <;> simp [pair]
  exact e ▸ h.padLeft (fun i => if i then [false] else [])

private theorem right_step [Fintype A] {u v : Word A} (h : Completable (pair u v)) :
    Completable (pair (v ++ u) v) := by
  have e : (fun i => spell (pair u v) (if i then [] else [true]) ++ pair u v i) = pair (v ++ u) v := by
    funext i
    cases i <;> simp [pair]
  exact e ▸ h.padLeft (fun i => if i then [] else [true])

/-- Induction on total length follows the prefix comparison all the way to a prefix pair. -/
theorem noncommuting_pair_completion [Fintype A] (u v : Word A) (h : u ++ v ≠ v ++ u) :
    Completable (pair u v) := by
  classical
  induction len : u.length + v.length using Nat.strong_induction_on generalizing u v with
  | ind n ih =>
    have nu : u ≠ [] := by rintro rfl; simp at h
    have nv : v ≠ [] := by rintro rfl; simp at h
    have uv : u ≠ v := by rintro rfl; exact h rfl
    by_cases p : u <+: v
    · obtain ⟨r, rfl⟩ := p
      have short : u ++ r ≠ r ++ u := by
        intro eqn
        apply h
        calc u ++ (u ++ r) = u ++ (r ++ u) := congrArg (u ++ ·) eqn
             _ = _ := (List.append_assoc ..).symm
      apply left_step
      exact ih _ (by simp at len; have := List.length_pos_iff.mpr nu; omega) u r short rfl
    by_cases q : v <+: u
    · obtain ⟨r, rfl⟩ := q
      have short : r ++ v ≠ v ++ r := by
        intro eqn
        apply h
        calc (v ++ r) ++ v = v ++ (r ++ v) := List.append_assoc ..
             _ = _ := congrArg (v ++ ·) eqn
      apply right_step
      exact ih _ (by simp at len; have := List.length_pos_iff.mpr nv; omega) r v short rfl
    apply completable_prefix
    · intro i j
      cases i <;> cases j <;> simp_all [pair, Ne.symm uv]
    · intro i
      cases i <;> assumption
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hp
      cases i <;> cases j <;> simp_all [pair]

theorem named_pair_iff_noncommuting [Fintype A] (u v : Word A) :
    NamedCode (pair u v) ↔ u ++ v ≠ v ++ u := by
  refine ⟨fun hi e => ?_, fun h => (noncommuting_pair_completion u v h).1⟩
  have he : spell (pair u v) [false, true] = spell (pair u v) [true, false] := by
    simpa [pair] using e
  have := hi he
  simp at this

end ThreeWordCodes
