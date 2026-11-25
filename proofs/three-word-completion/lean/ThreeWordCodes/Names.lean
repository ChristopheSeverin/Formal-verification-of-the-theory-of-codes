module

public import ThreeWordCodes.Definitions
public import Mathlib.Data.List.Basic

/-! # Named tokens, equality of relations, and shortening -/

@[expose] public section

namespace ThreeWordCodes

variable {A B N I J : Type*}

def spell (v : N → Word A) (xs : Word N) : Word A := xs.flatMap v

@[simp] theorem spell_nil (v : N → Word A) : spell v [] = [] := rfl
@[simp] theorem spell_cons (v : N → Word A) (i : N) (s : Word N) :
    spell v (i :: s) = v i ++ spell v s := rfl

@[simp] theorem spell_append (v : N → Word A) (s t : Word N) :
    spell v (s ++ t) = spell v s ++ spell v t := by simp [spell]

theorem spell_substitution (v : N → Word A) (outer : I → Word N) (s : Word I) :
    spell (fun i => spell v (outer i)) s = spell v (spell outer s) := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [ih]

/-- Injectivity is on sequences of names; equal word images already cause ambiguity. -/
def NamedCode (v : N → Word A) : Prop := Function.Injective (spell v)

/-- Equality of the two word-equation kernels on the same names. -/
def SameEquations (v : N → Word A) (w : N → Word B) : Prop :=
  ∀ s t, spell v s = spell v t ↔ spell w s = spell w t

theorem SameEquations.symm {v : N → Word A} {w : N → Word B} (h : SameEquations v w) :
    SameEquations w v := fun s t => (h s t).symm

theorem SameEquations.trans {C : Type*} {v : N → Word A} {w : N → Word B} {z : N → Word C}
    (h : SameEquations v w) (h' : SameEquations w z) : SameEquations v z :=
  fun s t => (h s t).trans (h' s t)

theorem SameEquations.substitution {v : N → Word A} {w : N → Word B}
    (h : SameEquations v w) (outer : I → Word N) :
    SameEquations (fun i => spell v (outer i)) (fun i => spell w (outer i)) := by
  intro s t
  simpa only [spell_substitution] using h (spell outer s) (spell outer t)

theorem SameEquations.namedCode_iff {v : N → Word A} {w : N → Word B}
    (h : SameEquations v w) : NamedCode v ↔ NamedCode w :=
  ⟨fun hv s t e => hv ((h s t).mpr e), fun hw s t e => hw ((h s t).mp e)⟩

theorem NamedCode.substitution {v : N → Word A} {outer : I → Word N}
    (h : NamedCode v) (ho : NamedCode outer) : NamedCode (fun i => spell v (outer i)) := by
  intro s t e
  simp only [spell_substitution] at e
  exact ho (h e)

theorem NamedCode.preserves_equations {v : N → Word A} (h : NamedCode v)
    (outer : I → Word N) : SameEquations outer (fun i => spell v (outer i)) := by
  intro s t
  simp only [spell_substitution]
  exact ⟨congrArg (spell v), fun he => h he⟩

theorem NamedCode.entries_injective {v : N → Word A} (h : NamedCode v) :
    Function.Injective v := by
  intro i j he
  have eqs : spell v [i] = spell v [j] := by simpa using he
  simpa using h eqs

theorem NamedCode.entry_ne_nil {v : N → Word A} (h : NamedCode v) (i : N) : v i ≠ [] := by
  intro hi
  have eqs : spell v [i] = spell v [] := by simp [hi]
  have := h eqs
  simp at this

private theorem names_of_words {v : N → Word A} (xs : List (Word A))
    (h : ∀ x ∈ xs, x ∈ Set.range v) : ∃ s : Word N, s.map v = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨i, rfl⟩ := h x (by simp)
    obtain ⟨s, hs⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨i :: s, by simp [hs]⟩

theorem namedCode_iff_range (v : N → Word A) :
    NamedCode v ↔ Function.Injective v ∧ InformationTheory.IsUniquelyDecodable (Set.range v) := by
  constructor
  · intro h
    refine ⟨h.entries_injective, ?_⟩
    intro xs ys hx hy e
    obtain ⟨s, rfl⟩ := names_of_words xs hx
    obtain ⟨t, rfl⟩ := names_of_words ys hy
    exact congrArg (List.map v) (h (by simpa [spell, List.flatMap_def] using e))
  · rintro ⟨hi, hd⟩ s t e
    apply List.map_injective_iff.mpr hi
    apply hd
    · intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact ⟨i, rfl⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact ⟨i, rfl⟩
    · simpa [spell, List.flatMap_def] using e

theorem spell_reverse (v : N → Word A) (s : Word N) :
    spell (fun i => (v i).reverse) s = (spell v s.reverse).reverse := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [ih]

theorem NamedCode.reverse {v : N → Word A} (h : NamedCode v) :
    NamedCode (fun i => (v i).reverse) := by
  intro s t e
  simp only [spell_reverse, List.reverse_inj] at e
  exact List.reverse_inj.mp (h e)

/-- A distinct first letter identifies the token; the rest of that token can be arbitrary. -/
theorem first_marked_code (extra : I → Word I) : NamedCode (fun i => i :: extra i) := by
  intro s
  induction s with
  | nil =>
    intro t e
    cases t with
    | nil => rfl
    | cons j t => simp at e
  | cons i s ih =>
    intro t e
    cases t with
    | nil => simp at e
    | cons j t =>
      obtain ⟨hij, he⟩ := List.cons.inj e
      subst j
      exact congrArg (List.cons i) (ih (List.append_cancel_left he))

theorem last_marked_code (extra : I → Word I) :
    NamedCode (fun i => extra i ++ [i]) := by
  simpa using (first_marked_code (fun i => (extra i).reverse)).reverse

/-- All left paddings on the names lift injectivity. One shortening is a special case. -/
theorem NamedCode.pad_left {v : I → Word A} (h : NamedCode v) (extra : I → Word I) :
    NamedCode (fun i => spell v (extra i) ++ v i) := by
  simpa using h.substitution (last_marked_code extra)

theorem NamedCode.pad_right {v : I → Word A} (h : NamedCode v) (extra : I → Word I) :
    NamedCode (fun i => v i ++ spell v (extra i)) :=
  h.substitution (first_marked_code extra)

end ThreeWordCodes
