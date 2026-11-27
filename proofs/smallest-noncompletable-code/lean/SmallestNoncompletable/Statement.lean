module

public import ThreeWordCodes.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Statement of the simultaneous minimality theorem

A code is a uniquely decodable set of words. A positive completion of `Y` on the alphabet `A`
is a finite maximal code `M ⊇ Y` on `A` with finite sets `L`, `R` such that every word has a
unique expression `ℓ m₁ ⋯ mⱼ r` with `ℓ ∈ L`, `mᵢ ∈ M` and `r ∈ R`
(`ThreeWordCodes.HasPositiveCompletion`). -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

universe u

variable {A : Type*}

/-- The total length `τ(Y)`. -/
def totalLength (Y : Finset (Word A)) : ℕ := ∑ y ∈ Y, y.length

/-- The maximal length `λ(Y)`, with `λ(∅) = 0`. -/
def maxLength (Y : Finset (Word A)) : ℕ := Y.sup List.length

/-- The set `X = {aa, abab, baaa, b}`. -/
def Xfinset [DecidableEq A] (a b : A) : Finset (Word A) := {[a, a], [a, b, a, b], [b, a, a, a], [b]}

/-- **Theorem 1 (simultaneous minimality).**

(a) Every finite code `Y` on a finite alphabet has a positively factorizing finite maximal
completion on that alphabet whenever `|Y| ≤ 3`, `λ(Y) ≤ 3` or `τ(Y) ≤ 10`.

(b) For distinct letters `a`, `b` of any alphabet, `X = {aa, abab, baaa, b}` is a code which is
contained in no finite maximal code on that alphabet.

(c) `|X| = 4`, `λ(X) = 4` and `τ(X) = 11`. -/
def SimultaneousMinimality : Prop :=
  (∀ (A : Type u) [Fintype A] [DecidableEq A] (Y : Finset (Word A)),
      IsUniquelyDecodable (Y : Set (Word A)) →
        (Y.card ≤ 3 ∨ maxLength Y ≤ 3 ∨ totalLength Y ≤ 10) →
          HasPositiveCompletion (Y : Set (Word A))) ∧
    ∀ (A : Type u) [DecidableEq A] (a b : A), a ≠ b →
      IsUniquelyDecodable (Xfinset a b : Set (Word A)) ∧
        (∀ M : Finset (Word A), Xfinset a b ⊆ M → ¬ IsMaximalCode (M : Set (Word A))) ∧
        (Xfinset a b).card = 4 ∧ maxLength (Xfinset a b) = 4 ∧ totalLength (Xfinset a b) = 11

end SmallestNoncompletable
