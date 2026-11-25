module

public import ThreeWordCodes.Names
public import Mathlib.GroupTheory.FreeGroup.Basic

/-! # Free-group changes of coordinates on positive word equations -/

@[expose] public section
namespace ThreeWordCodes
variable {A B I : Type*}

def groupWord (w : Word A) : FreeGroup A := FreeGroup.mk (w.map (fun a => (a,true)))

@[simp] theorem groupWord_nil : groupWord ([] : Word A) = 1 := rfl
@[simp] theorem groupWord_singleton (a : A) : groupWord [a] = FreeGroup.of a := rfl
@[simp] theorem groupWord_append (u v : Word A) : groupWord (u++v) = groupWord u * groupWord v := by
  simp [groupWord]

theorem groupWord_injective : Function.Injective (groupWord (A := A)) := by
  have reduced (w : Word A) : FreeGroup.IsReduced (w.map (fun a => (a,true))) := by
    induction w with
    | nil => exact .nil
    | cons a w ih =>
      cases w with
      | nil => exact .singleton
      | cons b z => exact FreeGroup.isReduced_cons_cons.mpr ⟨fun _ => rfl,ih⟩
  intro u v he
  obtain ⟨z,uz,vz⟩ := FreeGroup.Red.exact.mp he
  have same := ((reduced u).red_iff_eq.mp uz).symm.trans ((reduced v).red_iff_eq.mp vz)
  simpa [List.map_map,Function.comp_def] using congrArg (List.map Prod.fst) same

/-- An injective group substitution preserves exactly the positive equations on names,
provided the entries in the new coordinates are positive words. -/
theorem sameEquations_of_group_change (F : FreeGroup A →* FreeGroup B) (inj : Function.Injective F)
    {v : I → Word A} {w : I → Word B} (images : ∀ i, F (groupWord (v i)) = groupWord (w i)) :
    SameEquations v w := by
  have products (s : Word I) : F (groupWord (spell v s)) = groupWord (spell w s) := by
    induction s with
    | nil => simp
    | cons i s ih => simp [images,ih]
  intro s t
  constructor
  · intro eqn
    apply groupWord_injective
    rw [← products, ← products, eqn]
  · intro eqn
    apply groupWord_injective
    apply inj
    rw [products,products,eqn]

namespace GroupCoordinates

def a := FreeGroup.of false
def b := FreeGroup.of true

/-- The generator a becomes D⁻¹ and b becomes Dˡ J Dʳ. Using the same formula
in the opposite direction recovers a and b. -/
def change (l r : ℤ) : FreeGroup Bool →* FreeGroup Bool :=
  FreeGroup.lift fun x => if x then a^l * b * a^r else a⁻¹

@[simp] theorem change_a (l r : ℤ) : change l r a = a⁻¹ := by simp [change,a]
@[simp] theorem change_b (l r : ℤ) : change l r b = a^l * b * a^r := by simp [change,b]

theorem change_involutive (l r : ℤ) : Function.Involutive (change l r) := by
  have hom : (change l r).comp (change l r) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro x
    cases x with
    | false =>
      change change l r (change l r a) = a
      simp
    | true =>
      change change l r (change l r b) = b
      simp [mul_assoc]
  intro x
  exact congrArg (fun H : FreeGroup Bool →* FreeGroup Bool => H x) hom

/-- The particular coordinates J=aba, D=a⁻¹ send aba to J, ab to JD, and ba to DJ. -/
theorem aba_coordinates :
    change 1 1 (a*b*a) = b ∧ change 1 1 (a*b) = b*a ∧ change 1 1 (b*a) = a*b := by
  simp [mul_assoc]

end GroupCoordinates
end ThreeWordCodes
