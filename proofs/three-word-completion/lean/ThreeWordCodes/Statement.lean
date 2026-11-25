module

public import ThreeWordCodes.Prefix

/-! # Positive finite completion of three-word codes -/

@[expose] public section

namespace ThreeWordCodes

universe u
variable {A : Type*}

/-- The left and right factors denote positions in the output word. -/
def HasPositiveCompletion (X : Set (Word A)) : Prop :=
  ∃ M L R : Finset (Word A), X ⊆ (M : Set (Word A)) ∧
    IsMaximalCode (M : Set (Word A)) ∧ PositiveFactorization M R L

/-- Every three-word code on a finite alphabet admits a positive finite completion. -/
def ThreeWordTheorem : Prop :=
  ∀ (A : Type u) [Fintype A] (X : Finset (Word A)),
    X.card = 3 → InformationTheory.IsUniquelyDecodable (X : Set (Word A)) →
      HasPositiveCompletion (X : Set (Word A))

theorem HasPositiveCompletion.mono {X Y : Set (Word A)} (h : HasPositiveCompletion Y)
    (hXY : X ⊆ Y) : HasPositiveCompletion X := by
  obtain ⟨M, L, R, hYM, hm, hf⟩ := h
  exact ⟨M, L, R, hXY.trans hYM, hm, hf⟩

theorem PositiveCompletion.toPositive [Fintype A] {X M P Q : Finset (Word A)}
    (h : PositiveCompletion X M P Q) : HasPositiveCompletion (X : Set (Word A)) :=
  ⟨M, Q, P, h.1, h.2.1, h.2.2.2⟩

theorem prefix_case [Fintype A] (X : Finset (Word A))
    (hc : InformationTheory.IsUniquelyDecodable (X : Set (Word A)))
    (hp : InformationTheory.IsPrefixFree (X : Set (Word A))) :
    HasPositiveCompletion (X : Set (Word A)) := by
  obtain ⟨M, P, Q, h⟩ := finite_prefix_positive_completion X hc hp
  exact h.toPositive

end ThreeWordCodes
