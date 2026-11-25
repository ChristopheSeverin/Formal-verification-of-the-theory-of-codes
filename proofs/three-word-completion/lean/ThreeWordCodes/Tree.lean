module

public import ThreeWordCodes.Definitions
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Range

/-! # Completing a finite prefix tree

The internal nodes are the root and the proper prefixes of prescribed words.
A leaf is an immediate child of an internal node which is not itself internal. -/

@[expose] public section

namespace ThreeWordCodes

variable {A : Type*}

/-- Include the root even when the prescribed set is empty. -/
def internalNodes [DecidableEq A] (X : Finset (Word A)) : Finset (Word A) :=
  insert [] (X.biUnion fun w => (Finset.range w.length).image (fun i => w.take i))

def leaves [Fintype A] [DecidableEq A] (I : Finset (Word A)) : Finset (Word A) :=
  (I.biUnion fun p => Finset.univ.image (fun a : A => p ++ [a])) \ I

structure RootedPrefixClosed (I : Finset (Word A)) : Prop where
  root : [] ∈ I
  closed : ∀ {p w : Word A}, w ∈ I → p <+: w → p ∈ I

theorem mem_internalNodes [DecidableEq A] {X : Finset (Word A)} {p : Word A} :
    p ∈ internalNodes X ↔
      p = [] ∨ ∃ w ∈ X, p <+: w ∧ p.length < w.length := by
  simp only [internalNodes, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨w, hw, i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hw, List.take_prefix i w, by simpa [Nat.min_eq_left hi.le] using hi⟩
  · rintro (h | ⟨w, hw, hp, hlen⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hw, p.length, hlen, (List.prefix_iff_eq_take.mp hp).symm⟩

theorem internalNodes_closed [DecidableEq A] (X : Finset (Word A)) :
    RootedPrefixClosed (internalNodes X) := by
  refine ⟨mem_internalNodes.mpr (Or.inl rfl), ?_⟩
  intro p w hw hp
  rcases mem_internalNodes.mp hw with rfl | ⟨z, hz, hwz, hlen⟩
  · exact mem_internalNodes.mpr (Or.inl (List.eq_nil_of_prefix_nil hp))
  · exact mem_internalNodes.mpr (Or.inr ⟨z, hz, hp.trans hwz, lt_of_le_of_lt hp.length_le hlen⟩)

theorem mem_leaves [Fintype A] [DecidableEq A] {I : Finset (Word A)} {w : Word A} :
    w ∈ leaves I ↔ IsChild I w ∧ w ∉ I := by
  simp [leaves, IsChild]

theorem child_of_internal {I : Finset (Word A)} (hI : RootedPrefixClosed I)
    {w : Word A} (hw : w ∈ I) (hn : w ≠ []) : IsChild I w := by
  have h := List.dropLast_concat_getLast hn
  exact ⟨w.dropLast, hI.closed hw ⟨_, h⟩, w.getLast hn, h⟩

theorem nil_not_child (I : Finset (Word A)) : ¬ IsChild I [] := by
  rintro ⟨p, _, a, h⟩
  simp at h

variable [Fintype A] [DecidableEq A]

theorem leaves_prefixFree {I : Finset (Word A)} (hI : RootedPrefixClosed I) :
    InformationTheory.IsPrefixFree (leaves I : Set (Word A)) := by
  intro x hx y hy hxy
  obtain ⟨⟨p, hp, a, rfl⟩, _⟩ := mem_leaves.mp hy
  rcases List.prefix_concat_iff.mp hxy with he | hxpre
  · exact he
  · exact ((mem_leaves.mp hx).2 (hI.closed hp hxpre)).elim

theorem subset_leaves {X : Finset (Word A)}
    (hpre : InformationTheory.IsPrefixFree (X : Set (Word A))) (hne : [] ∉ X) :
    X ⊆ leaves (internalNodes X) := by
  intro w hw
  have hn : w ≠ [] := fun h => hne (h ▸ hw)
  have split := List.dropLast_concat_getLast hn
  have ltlen : w.dropLast.length < w.length := by
    have e := congrArg List.length split
    simp only [List.length_append, List.length_singleton] at e
    omega
  apply mem_leaves.mpr
  constructor
  · exact ⟨w.dropLast, mem_internalNodes.mpr (Or.inr ⟨w, hw, ⟨_, split⟩, ltlen⟩),
      w.getLast hn, split⟩
  · intro h
    rcases mem_internalNodes.mp h with h0 | ⟨z, hz, hprefix, hlt⟩
    · exact hn h0
    · have he := hpre w hw z hz hprefix
      exact (Nat.ne_of_lt hlt) (congrArg List.length he)

end ThreeWordCodes
