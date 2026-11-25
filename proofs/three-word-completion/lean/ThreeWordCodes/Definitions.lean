module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic

/-! # Words, certificates, and finite maximal completion

Words are lists of letters. Unique decodability is the mathlib predicate.
The polynomial and parsing certificates use the same three finite sets. -/

@[expose] public section

namespace ThreeWordCodes

universe u
abbrev Word (A : Type u) := List A

/-- Maximality among all uniquely decodable sets on the same alphabet. -/
def IsMaximalCode {A : Type*} (M : Set (Word A)) : Prop :=
  InformationTheory.IsUniquelyDecodable M ∧
    ∀ C : Set (Word A), M ⊆ C → InformationTheory.IsUniquelyDecodable C → C = M

/-- Concatenate a list of words belonging to M. -/
def concatenate {A : Type*} {M : Finset (Word A)} (blocks : List (↥M)) : Word A :=
  (blocks.map Subtype.val).flatten

/-- Assemble a left part in Q, a list of codewords in M, and a right part in P. -/
def assemble {A : Type*} (M P Q : Finset (Word A))
    (d : ↥Q × List (↥M) × ↥P) : Word A :=
  d.1.val ++ concatenate d.2.1 ++ d.2.2.val

def PositiveFactorization {A : Type*} (M P Q : Finset (Word A)) : Prop :=
  Function.Bijective (assemble M P Q)

/-- The immediate children of P, specified without enumerating the alphabet. -/
def IsChild {A : Type*} (P : Finset (Word A)) (w : Word A) : Prop :=
  ∃ p ∈ P, ∃ a : A, p ++ [a] = w

/-- Count pairs (i,q) in S × Q for which spell(i) q is w. Taking S = P counts
pairs. Taking S = P × A counts triples, including all distinct cuts of w. -/
def productCoeff {A ι : Type*} [DecidableEq A] (S : Finset ι) (spell : ι → Word A)
    (Q : Finset (Word A)) (w : Word A) : ℕ :=
  ((S ×ˢ Q).filter fun t => spell t.1 ++ t.2 = w).card

/-- The wordwise identity [M] + [P][Q] = 1 + [P][A][Q]. Moving terms gives
the integer polynomial identity [M] − 1 = [P]([A] − 1)[Q]. -/
def PolynomialIdentity {A : Type*} [Fintype A] (M P Q : Finset (Word A)) : Prop := by
  classical
  exact ∀ w, (if w ∈ M then 1 else 0) + productCoeff P id Q w =
    (if w = [] then 1 else 0) +
      productCoeff (P ×ˢ (Finset.univ : Finset A)) (fun pa => pa.1 ++ [pa.2]) Q w

/-- A finite completion carrying both witnesses with the prescribed factor order. -/
def PositiveCompletion {A : Type*} [Fintype A] (X M P Q : Finset (Word A)) : Prop :=
  X ⊆ M ∧ IsMaximalCode (M : Set (Word A)) ∧
    PolynomialIdentity M P Q ∧ PositiveFactorization M P Q

/-- The proposition that every three-word code has a completion with an explicit polynomial certificate. -/
def ThreeWordPolynomialCompletion : Prop :=
  ∀ (A : Type u) [Fintype A] (X : Finset (Word A)),
    X.card = 3 → InformationTheory.IsUniquelyDecodable (X : Set (Word A)) →
      ∃ M P Q : Finset (Word A), PositiveCompletion X M P Q

end ThreeWordCodes
