module

public import ThreeWordCodes.Tree
public import Mathlib.Data.List.Induction

/-! # Unique parsing up to a final internal node -/

@[expose] public section

namespace ThreeWordCodes

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {I : Finset (Word A)}

theorem parse_exists (hI : RootedPrefixClosed I) (w : Word A) :
    ∃ blocks : List (↥(leaves I)), ∃ p : ↥I, concatenate blocks ++ p.val = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], ⟨[], hI.root⟩, rfl⟩
  | append_singleton w a ih =>
    obtain ⟨blocks, p, rfl⟩ := ih
    by_cases h : p.val ++ [a] ∈ I
    · exact ⟨blocks, ⟨_, h⟩, (List.append_assoc ..).symm⟩
    · let leaf : ↥(leaves I) := ⟨p.val ++ [a],
        mem_leaves.mpr ⟨⟨p.val, p.property, a, rfl⟩, h⟩⟩
      exact ⟨blocks ++ [leaf], ⟨[], hI.root⟩, by simp [concatenate, leaf, List.append_assoc]⟩

private theorem no_leaf_prefix (hI : RootedPrefixClosed I) (b : ↥(leaves I)) (p : ↥I) :
    ¬ b.val <+: p.val :=
  fun h => (mem_leaves.mp b.property).2 (hI.closed p.property h)

theorem parse_unique (hI : RootedPrefixClosed I)
    (s t : List (↥(leaves I))) (p q : ↥I)
    (h : concatenate s ++ p.val = concatenate t ++ q.val) : s = t ∧ p = q := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => exact ⟨rfl, Subtype.ext (by simpa [concatenate] using h)⟩
    | cons b t =>
      have he : p.val = b.val ++ (concatenate t ++ q.val) := by
        simpa [concatenate, List.append_assoc] using h
      exact (no_leaf_prefix hI b p ⟨_, he.symm⟩).elim
  | cons a s ih =>
    cases t with
    | nil =>
      have he : a.val ++ (concatenate s ++ p.val) = q.val := by
        simpa [concatenate, List.append_assoc] using h
      exact (no_leaf_prefix hI a q ⟨_, he⟩).elim
    | cons b t =>
      have he : a.val ++ (concatenate s ++ p.val) = b.val ++ (concatenate t ++ q.val) := by
        simpa [concatenate, List.append_assoc] using h
      have hab : a = b := by
        apply Subtype.ext
        rcases List.append_eq_append_iff.mp he with ⟨v, hv, _⟩ | ⟨v, hv, _⟩
        · exact leaves_prefixFree hI _ a.property _ b.property ⟨v, hv.symm⟩
        · exact (leaves_prefixFree hI _ b.property _ a.property ⟨v, hv.symm⟩).symm
      subst b
      obtain ⟨hst, hpq⟩ := ih t (List.append_cancel_left he)
      exact ⟨congrArg (List.cons a) hst, hpq⟩

theorem leaves_factorization (hI : RootedPrefixClosed I) :
    PositiveFactorization (leaves I) I {[]} := by
  constructor
  · rintro ⟨⟨u, hu⟩, s, p⟩ ⟨⟨v, hv⟩, t, q⟩ h
    obtain rfl : u = [] := Finset.mem_singleton.mp hu
    obtain rfl : v = [] := Finset.mem_singleton.mp hv
    obtain ⟨rfl, rfl⟩ := parse_unique hI s t p q (by simpa [assemble] using h)
    rfl
  · intro w
    obtain ⟨s, p, hw⟩ := parse_exists hI w
    exact ⟨(⟨[], Finset.mem_singleton_self _⟩, s, p), by simpa [assemble] using hw⟩

end ThreeWordCodes
