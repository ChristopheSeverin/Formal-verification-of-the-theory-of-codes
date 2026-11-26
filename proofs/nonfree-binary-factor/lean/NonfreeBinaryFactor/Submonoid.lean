module

public import NonfreeBinaryFactor.NormalForms
public import Mathlib.Data.List.Infix
public import Mathlib.Algebra.Group.Submonoid.Basic

/-! # The middle submonoid of the binary free monoid -/

@[expose] public section
namespace NonfreeBinaryFactor

abbrev a : Bool := false
abbrev b : Bool := true
abbrev BinaryWord := List Bool

/-- Avoid the prefix `ab`. An initial `b` must be followed by `ab`. -/
def LeftNormal (w : BinaryWord) : Prop := Reduced [a,b] b w

/-- Avoid the suffix `aabb`. A final `a` must be preceded by `aabb`. -/
def RightNormal (w : BinaryWord) : Prop := Reduced [b,b,a,a] a w.reverse

def Middle (w : BinaryWord) : Prop := LeftNormal w ∧ RightNormal w

theorem middle_nil : Middle [] := by simp [Middle, LeftNormal, RightNormal, Reduced]

/-- The only one- and two-letter words passing the left test are `a` and
`aa`. Neither passes the right test. -/
theorem length_ge_three {w : BinaryWord} (hw : Middle w) (hne : w ≠ []) : 3 ≤ w.length := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases t with
  | nil =>
    cases x <;> simp [Middle, LeftNormal, RightNormal, Reduced, a, b] at hw
  | cons y t =>
    cases t with
    | nil =>
      cases x <;> cases y <;> simp [Middle, LeftNormal, RightNormal, Reduced, a, b] at hw
    | cons z t => simp

private theorem left_of_append {u v : BinaryWord} (hu : LeftNormal u) (lu : 3 ≤ u.length) :
    LeftNormal (u ++ v) := by
  have test (p : BinaryWord) (hp : p.length ≤ 3) :
      p <+: u ++ v ↔ p <+: u := List.isPrefix_append_of_length (hp.trans lu)
  unfold LeftNormal Reduced
  rw [test [a,b] (by decide), test [b] (by decide), test [b,a,b] (by decide)]
  exact hu

private theorem right_of_append {u v : BinaryWord} (hv : Middle v) (lv : 3 ≤ v.length) :
    RightNormal (u ++ v) := by
  unfold RightNormal
  rw [List.reverse_append]
  have len : 3 ≤ v.reverse.length := by simpa using lv
  have right : Reduced [b,b,a,a] a v.reverse := hv.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases fits : 4 ≤ v.reverse.length
    · exact right.1 ((List.isPrefix_append_of_length (l₁ := [b,b,a,a]) fits).mp h)
    · -- The last word would have to be exactly the three-letter suffix abb.
      have three : [b,b,a] <+: v.reverse ++ u.reverse :=
        (show [b,b,a] <+: [b,b,a,a] by decide).trans h
      have pre : [b,b,a] <+: v.reverse := (List.isPrefix_append_of_length (l₁ := [b,b,a]) len).mp three
      have eq := pre.eq_of_length_le (show v.reverse.length ≤ 3 by omega)
      have bad : v = [a,b,b] := by simpa using (congrArg List.reverse eq).symm
      have left := hv.1
      rw [bad] at left
      simp [LeftNormal, Reduced, a, b] at left
  · have pre : [a] <+: v.reverse := (List.isPrefix_append_of_length
        (show [a].length ≤ v.reverse.length by change 1 ≤ _; omega)).mp h
    exact List.prefix_append_of_prefix (right.2 pre)

theorem middle_append {u v : BinaryWord} (hu : Middle u) (hv : Middle v) :
    Middle (u ++ v) := by
  by_cases eu : u = []
  · simpa [eu] using hv
  by_cases ev : v = []
  · simpa [ev] using hu
  exact ⟨left_of_append hu.1 (length_ge_three hu eu), right_of_append hv (length_ge_three hv ev)⟩

/-- The witness, with the identity and multiplication inherited from the
binary free monoid. -/
def middleSubmonoid : Submonoid (FreeMonoid Bool) where
  carrier := {w | Middle w.toList}
  one_mem' := middle_nil
  mul_mem' := middle_append

@[simp] theorem mem_middleSubmonoid {w : FreeMonoid Bool} :
    w ∈ middleSubmonoid ↔ Middle w.toList := Iff.rfl

end NonfreeBinaryFactor
