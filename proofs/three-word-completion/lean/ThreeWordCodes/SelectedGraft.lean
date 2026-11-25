module

public import ThreeWordCodes.Graft
public import ThreeWordCodes.Greedy

/-! # Testing the selected leaves on their own alphabet

A graft can be specified before completing the inner prefix tree. All tests
on a finite list of selected words take place on the original token names.
This lets the same construction use different positive images of the names.
-/

@[expose] public section
namespace ThreeWordCodes
namespace SelectedGraft
variable {A B : Type*}

/-- The root and the proper suffixes of every selected leaf. -/
def nodes [DecidableEq B] (E : List (Word B)) : List (Word B) :=
  [] :: E.flatMap fun e => e.tails.filter (· != e)

@[simp] theorem mem_nodes [DecidableEq B] {E : List (Word B)} {q : Word B} :
    q ∈ nodes E ↔ q=[] ∨ ∃ e∈E, q <:+ e ∧ q≠e := by
  simp [nodes,List.mem_tails]

/-- Finite conditions on a tree graft, decidable for concrete words. -/
def Valid [DecidableEq B] (v : B → Word A) (E : List (Word B)) (s : Word B) (t : Word A) : Prop :=
  [] ∉ E ∧ s ∈ E ∧ t≠[] ∧
  (∀ e∈E, ∀ f∈E, e <:+ f → e=f) ∧
  ∀ q∈nodes E, spell v q≠t ∧ (Comparable t (spell v q) → s++q∈E)

instance [DecidableEq A] [DecidableEq B] (v : B → Word A) (E : List (Word B)) (s : Word B) (t : Word A) :
    Decidable (Valid v E s t) := by
  unfold Valid Comparable
  infer_instance

/-- A successful selection gives a polynomial certificate for the target and
for every selected leaf whose token sequence does not start with s. -/
theorem certificate [Fintype A] [Nonempty A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (v : B → Word A) (hi : Function.Injective v) (hne : ∀ b, v b ≠ [])
    (pf : InformationTheory.IsPrefixFree (Set.range v))
    (E : List (Word B)) (s : Word B) (t : Word A) (ok : Valid v E s t) :
    HasFiniteCertificate ({spell v s ++ t} ∪
      (spell v '' {e | e∈E ∧ ¬s <+: e})) := by
  classical
  obtain ⟨nonempty,selected,nt,suffix,checks⟩ := ok
  let X := Finset.univ.image v
  have inside : X ⊆ leaves (internalNodes X) := subset_leaves (by simpa [X] using pf)
    (by simpa [X] using hne)
  let name (b : B) : ↥(leaves (internalNodes X)) := ⟨v b,inside (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)⟩
  have inj : Function.Injective name := fun x y h => hi (congrArg Subtype.val h)
  have injWord : Function.Injective (List.map name) := List.map_injective_iff.mpr inj
  let phi := fun c : ↥(leaves (internalNodes X)) => c.val
  have spelling (e : Word B) : spell phi (e.map name) = spell v e := by
    induction e with
    | nil => rfl
    | cons j e ih => exact congrArg (v j ++ ·) ih
  let leavesE := E.toFinset.image (List.map name)
  have mem {w} : w∈leavesE ↔ ∃ e∈E, e.map name=w := by simp [leavesE]
  have read {w} (hw : w ∈ suffixNodes leavesE) : ∃ e∈nodes E, w=e.map name := by
    rcases mem_suffixNodes.mp hw with rfl | ⟨z,hz,pr,ne⟩
    · exact ⟨[],mem_nodes.mpr (Or.inl rfl),rfl⟩
    · obtain ⟨f,hf,rfl⟩ := mem.mp hz
      obtain ⟨q,suf,rfl⟩ := List.suffix_map_iff.mp pr
      exact ⟨q,mem_nodes.mpr (Or.inr ⟨f,hf,suf,fun e => ne (congrArg (List.map name) e)⟩),rfl⟩
  have out := tree_extension_certificate (internalNodes X) (internalNodes_closed X) leavesE
    (fun h => by
      obtain ⟨e,he,eqn⟩ := mem.mp h
      exact nonempty ((List.map_eq_nil_iff.mp eqn) ▸ he))
    (by
      intro x hx y hy cmp
      obtain ⟨e,he,rfl⟩ := mem.mp hx
      obtain ⟨f,hf,rfl⟩ := mem.mp hy
      exact congrArg (List.map name) (suffix e he f hf ((List.suffix_map_iff_of_injective inj).mp cmp)))
    (s.map name) (mem.mpr ⟨s,selected,rfl⟩) t nt
    (by
      rw [mem_codedSet]
      rintro ⟨w,hw,eqn⟩
      obtain ⟨e,he,rfl⟩ := read hw
      exact (checks e he).1 ((spelling e).symm.trans eqn))
    (by
      intro w hw cmp
      obtain ⟨e,he,rfl⟩ := read hw
      apply mem.mpr
      exact ⟨s++e,(checks e he).2 (by simpa only [←spelling] using cmp),List.map_append⟩)
  apply out.mono
  rintro w (h | ⟨e,⟨he,away⟩,rfl⟩)
  · left
    change w ∈ {spell phi (s.map name) ++ t}
    simpa only [spelling] using h
  · right
    refine ⟨e.map name,⟨mem.mpr ⟨e,he,rfl⟩,?_⟩,spelling e⟩
    rintro ⟨w,hw,eqn⟩
    obtain ⟨q,_,rfl⟩ := read hw
    exact away ⟨q,injWord ((List.map_append).trans eqn)⟩

end SelectedGraft
end ThreeWordCodes
