module

public import ThreeWordCodes.Prefix

/-! # The binary example with prescribed words a, ba, and bba -/

@[expose] public section

namespace ThreeWordCodes.BinaryExample

abbrev a : Bool := false
abbrev b : Bool := true

def prescribed : Finset (Word Bool) := {[a], [b, a], [b, b, a]}
def completed : Finset (Word Bool) := {[a], [b, a], [b, b, a], [b, b, b]}
def remainders : Finset (Word Bool) := {[], [b], [b, b]}

theorem prescribed_prefixFree :
    InformationTheory.IsPrefixFree (prescribed : Set (Word Bool)) := by
  intro x hx y hy hxy
  change x ∈ prescribed at hx
  change y ∈ prescribed at hy
  simp only [prescribed, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert hxy; decide)

theorem computed_internals : internalNodes prescribed = remainders := by decide
theorem computed_leaves : leaves (internalNodes prescribed) = completed := by decide

/-- The additional word is bbb. The only left factor is the empty word. -/
theorem binary_completion : PositiveCompletion prescribed completed remainders {[]} := by
  have h := prefix_completion_explicit prescribed prescribed_prefixFree (by decide)
  rw [computed_leaves, computed_internals] at h
  exact h

end ThreeWordCodes.BinaryExample
