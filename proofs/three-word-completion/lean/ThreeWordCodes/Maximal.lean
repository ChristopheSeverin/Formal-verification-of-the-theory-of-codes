module

public import ThreeWordCodes.Definitions
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.List.Basic

/-! # Maximality from finitely many right remainders -/

@[expose] public section

namespace ThreeWordCodes

private theorem mem_of_mem_blocks {A : Type*} {M : Finset (Word A)}
    {blocks : List (↥M)} {w : Word A} (hw : w ∈ blocks.map Subtype.val) : w ∈ M := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hw
  exact b.property

/-- If M is a code and M* R covers every word for a finite R, M is maximal.
Two distinct powers of a word in a competing code share their right remainder.
Right cancellation and unique decoding then put that word in M. -/
theorem maximal_of_finite_right_remainders {A : Type*} (M R : Finset (Word A))
    (hcode : InformationTheory.IsUniquelyDecodable (M : Set (Word A)))
    (hcover : ∀ w : Word A, ∃ blocks : List (↥M), ∃ r : ↥R,
      concatenate blocks ++ r.val = w) :
    IsMaximalCode (M : Set (Word A)) := by
  classical
  refine ⟨hcode, ?_⟩
  intro C hMC hC
  apply Set.Subset.antisymm _ hMC
  intro w hw
  choose blocks tail hparse using fun n : ℕ => hcover (List.replicate n w).flatten
  obtain ⟨i, j, hlt, heq⟩ : ∃ i j : ℕ, i < j ∧ tail i = tail j := by
    obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite tail
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  have hsame :
      ((List.replicate (j - i) w).flatten ++ concatenate (blocks i)) ++ (tail i).val =
      concatenate (blocks j) ++ (tail i).val := by
    calc
      _ = (List.replicate (j - i) w).flatten ++ (List.replicate i w).flatten := by
        rw [List.append_assoc, hparse i]
      _ = (List.replicate j w).flatten := by
        rw [← List.flatten_append, ← List.replicate_add, Nat.sub_add_cancel hlt.le]
      _ = _ := by rw [heq]; exact (hparse j).symm
  have hwords := List.append_cancel_right hsame
  have hlist : List.replicate (j - i) w ++ (blocks i).map Subtype.val =
      (blocks j).map Subtype.val := by
    apply hC
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (List.mem_replicate.mp hv).2 ▸ hw
      · exact hMC (mem_of_mem_blocks hv)
    · exact fun v hv => hMC (mem_of_mem_blocks hv)
    · simpa only [List.flatten_append, concatenate] using hwords
  have hin : w ∈ List.replicate (j - i) w ++ (blocks i).map Subtype.val :=
    List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  exact mem_of_mem_blocks (hlist ▸ hin)

end ThreeWordCodes
