module

public import ThreeWordCodes.Shortening

/-! # Renaming token indices and binary letters -/

@[expose] public section
namespace ThreeWordCodes
variable {A I J : Type*}

theorem spell_rename (v : I → Word A) (f : J → I) (s : Word J) :
    spell (fun j => v (f j)) s = spell v (s.map f) := by
  induction s with
  | nil => rfl
  | cons j s ih => simp [ih]

theorem NamedCode.reindex {v : I → Word A} (hc : NamedCode v) {f : J → I}
    (inj : Function.Injective f) : NamedCode (fun j => v (f j)) := by
  intro s t eqn
  simp only [spell_rename] at eqn
  exact List.map_injective_iff.mpr inj (hc eqn)

theorem Completable.reindex {v : I → Word A} (hc : Completable v) {f : J → I}
    (inj : Function.Injective f) : Completable (fun j => v (f j)) :=
  ⟨hc.1.reindex inj,hc.2.mono (by rintro w ⟨j,rfl⟩; exact ⟨f j,rfl⟩)⟩

theorem completable_reindex_iff (v : I → Word A) (e : J ≃ I) :
    Completable (fun j => v (e j)) ↔ Completable v := by
  refine ⟨fun h => ?_,fun h => h.reindex e.injective⟩
  simpa using h.reindex e.symm.injective

/-- Exchange the binary letters precisely when the distinguished one is true. -/
def letterFlip (c x : Bool) : Bool := if c then !x else x

@[simp] theorem letterFlip_twice (c x : Bool) : letterFlip c (letterFlip c x) = x := by
  cases c <;> cases x <;> rfl

theorem map_spell (f : A → J) (v : I → Word A) (s : Word I) :
    spell (fun k => (v k).map f) s = (spell v s).map f := by
  induction s with
  | nil => rfl
  | cons k s ih => simp [ih]

theorem named_flip_iff (v : I → Word Bool) (c : Bool) :
    NamedCode (fun i => (v i).map (letterFlip c)) ↔ NamedCode v := by
  have inject : Function.Injective (letterFlip c) := Function.LeftInverse.injective (letterFlip_twice c)
  constructor
  · intro h s t eqn
    apply h
    simp only [map_spell,eqn]
  · intro h s t eqn
    simp only [map_spell] at eqn
    exact h (List.map_injective_iff.mpr inject eqn)

private theorem flip_complete [Nonempty I] {v : I → Word Bool} (hc : Completable v) (c : Bool) :
    Completable (fun i => (v i).map (letterFlip c)) := by
  let g (x : Bool) := [letterFlip c x]
  have e : pair (g false) (g true) = g := by funext x; cases x <;> rfl
  have ng : g false ++ g true ≠ g true ++ g false := by cases c <;> decide
  have base : Completable g := e ▸ noncommuting_pair_completion _ _ ng
  have maps (s : Word Bool) : spell g s = s.map (letterFlip c) := by
    induction s with
    | nil => rfl
    | cons b w ih => exact congrArg (letterFlip c b :: ·) ih
  simpa only [maps] using base.substitute hc

theorem completable_flip_iff [Nonempty I] (v : I → Word Bool) (c : Bool) :
    Completable (fun i => (v i).map (letterFlip c)) ↔ Completable v := by
  refine ⟨fun h => ?_,fun h => flip_complete h c⟩
  simpa [List.map_map,Function.comp_def] using flip_complete h c

/-- An ordering uses the same names as the binary gap lemmas. -/
def threeNames (p u v : Fin 3) : Option Bool → Fin 3
  | some false => p
  | some true => u
  | none => v

theorem order_three (p : Fin 3) : ∃ u v : Fin 3, Function.Bijective (threeNames p u v) := by
  revert p
  decide

end ThreeWordCodes
