module

public import ThreeWordCodes.Shortening

/-! # Greedy reading on a finite prefix code

An input outside the prefixes of products has a nonempty unread suffix that is
incomparable with every token. This gives both injectivity and a finite positive
completion of the input together with the original tokens.
-/

@[expose] public section
namespace ThreeWordCodes

variable {A I : Type*}

/-- The extra token has name `none`; original tokens keep their names. -/
def addToken (v : I → Word A) (w : Word A) : Option I → Word A
  | none => w
  | some i => v i

private theorem peel {v : I → Word A} (hne : ∀ i, v i ≠ []) (w : Word A) :
    ∃ s : Word I, ∃ t : Word A, w = spell v s ++ t ∧ ∀ i, ¬ v i <+: t := by
  classical
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases stop : ∀ i, ¬ v i <+: w
    · exact ⟨[], w, rfl, stop⟩
    · push Not at stop
      obtain ⟨i, t, e⟩ := stop
      have lengths := congrArg List.length e
      simp only [List.length_append] at lengths
      have := List.length_pos_iff.mpr (hne i)
      obtain ⟨s, r, hr, hs⟩ := ih t.length (by omega) t rfl
      exact ⟨i :: s, r, by rw [← e, hr]; simp [List.append_assoc], hs⟩

theorem greedy_completion [Fintype A] [Fintype I] {v : I → Word A}
    (hi : Function.Injective v) (hn : ∀ i, v i ≠ [])
    (hp : InformationTheory.IsPrefixFree (Set.range v)) (w : Word A)
    (h : ¬ ∃ s : Word I, w <+: spell v s) : Completable (addToken v w) := by
  classical
  obtain ⟨s, t, hw, stop⟩ := peel hn w
  have nt : t ≠ [] := by
    intro e
    apply h
    exact ⟨s, by simp [hw, e]⟩
  have start (i : I) : ¬ t <+: v i := by
    rintro ⟨r, hr⟩
    apply h
    exact ⟨s ++ [i], ⟨r, by simp [hw, ← hr, List.append_assoc]⟩⟩
  have newcode : Completable (addToken v t) := by
    apply completable_prefix
    · rintro (_ | i) (_ | j) eqn
      · rfl
      · change t = v j at eqn
        exact (start j (by rw [eqn])).elim
      · change v i = t at eqn
        exact (stop i (by rw [eqn])).elim
      · exact congrArg some (hi eqn)
    · rintro (_ | i)
      · exact nt
      · exact hn i
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ cmp
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j => exact (start j cmp).elim
      | some i =>
        cases j with
        | none => exact (stop i cmp).elim
        | some j => exact hp _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ cmp
  let pre : Option I → Word (Option I) := fun j => match j with
    | none => s.map some
    | some _ => []
  have he : (fun i => spell (addToken v t) (pre i) ++ addToken v t i) = addToken v w := by
    funext i
    cases i with
    | none => simpa [pre, addToken, spell, List.flatMap_def, List.map_map, Function.comp_def] using hw.symm
    | some i => rfl
  exact he ▸ newcode.padLeft pre

theorem prefix_of_products_of_ambiguity [Fintype A] [Fintype I] {v : I → Word A}
    (hi : Function.Injective v) (hn : ∀ i, v i ≠ [])
    (hp : InformationTheory.IsPrefixFree (Set.range v)) (w : Word A)
    (h : ¬ NamedCode (addToken v w)) : ∃ s : Word I, w <+: spell v s := by
  by_contra no
  exact h (greedy_completion hi hn hp w no).1

end ThreeWordCodes
