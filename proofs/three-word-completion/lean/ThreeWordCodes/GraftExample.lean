module

public import ThreeWordCodes.Graft

/-! # A three-word completion requiring both prefix and suffix comparisons

The inner leaves are a, ba, bb. Writing A for a and C for ba, the suffix code
on these names is {A, AC, CC}. Graft aab onto CC to obtain babaaab.
-/

@[expose] public section
namespace ThreeWordCodes.GraftExample
abbrev a : Bool := false
abbrev b : Bool := true
def input : Finset (Word Bool) := {[a], [a,b,a], [b,a,b,a,a,a,b]}
def internal : Finset (Word Bool) := {[],[b]}
private theorem rooted : RootedPrefixClosed internal := by
  refine ⟨by decide, ?_⟩
  intro p w hw hp
  simp only [internal, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
  rcases hw with rfl | rfl
  · exact Or.inl (List.eq_nil_of_prefix_nil hp)
  · cases p with
    | nil => exact Or.inl rfl
    | cons c p =>
      obtain ⟨t,h⟩ := hp
      simp at h
      simp [h]

abbrev leafA : ↥(leaves internal) := ⟨[a],by decide⟩
abbrev leafC : ↥(leaves internal) := ⟨[b,a],by decide⟩
private def E : Finset (Word (↥(leaves internal))) := {[leafA], [leafA,leafC], [leafC,leafC]}
private theorem suffixFree : ∀ x ∈ E, ∀ y ∈ E, x <:+ y → x = y := by
  intro x hx y hy cmp
  simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert cmp; decide)

private theorem nodes : suffixNodes E = {[], [leafC]} := by
  classical
  ext w
  rw [mem_suffixNodes]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (z | ⟨e,he,pr,ne⟩)
    · exact Or.inl z
    · simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> simp only [← List.mem_tails] at pr <;>
        simp [List.tails] at pr <;> grind
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨[leafC,leafC], by decide, ⟨[leafC],rfl⟩, by decide⟩

/-- A single construction works for every tail that is prefix-incomparable
with ba. In particular every tail beginning in a is allowed. -/
theorem family_certificate (t : Word Bool) (sep : ¬ Comparable t [b,a]) :
    HasFiniteCertificate ({[a], [a,b,a], [b,a,b,a] ++ t} : Set (Word Bool)) := by
  let s := [leafC,leafC]
  have ne : t ≠ [] := by rintro rfl; exact sep (Or.inl (by simp))
  have out := tree_extension_certificate internal rooted E (by decide) suffixFree s (by decide) t ne
    (by
      rw [nodes,mem_codedSet]
      rintro ⟨v,hv,eqn⟩
      rcases Finset.mem_insert.mp hv with rfl | hs
      · exact ne eqn.symm
      · obtain rfl := Finset.mem_singleton.mp hs
        change [b,a] = t at eqn
        exact sep (Or.inl (by rw [eqn])))
    (by
      intro q hq cp
      rw [nodes] at hq
      rcases Finset.mem_insert.mp hq with rfl | h
      · decide
      · obtain rfl := Finset.mem_singleton.mp h
        exact (sep cp).elim)
  apply out.mono
  rintro w (rfl | rfl | rfl)
  · right
    refine ⟨[leafA], ⟨by decide, ?_⟩, rfl⟩
    rintro ⟨q,_,he⟩
    have := congrArg List.length he
    simp [s] at this
  · right
    refine ⟨[leafA,leafC], ⟨by decide, ?_⟩, rfl⟩
    rintro ⟨q,_,he⟩
    exact (by decide : leafC ≠ leafA) (List.cons.inj he).1
  · left
    rfl

theorem completion : HasPositiveCompletion (input : Set (Word Bool)) := by
  have cert := family_certificate [a,a,b] (by
    change ¬ (([a,a,b] : Word Bool) <+: [b,a] ∨ ([b,a] : Word Bool) <+: [a,a,b])
    decide)
  simpa [input] using cert.toPositive

theorem not_prefix : ¬ InformationTheory.IsPrefixFree (input : Set (Word Bool)) := by
  intro h
  exact (by decide : [a] ≠ [a,b,a]) (h _ (by decide) _ (by decide) ⟨[b,a],rfl⟩)

theorem not_suffix : ¬ (∀ x ∈ input, ∀ y ∈ input, x <:+ y → x = y) := by
  intro h
  exact (by decide : [a] ≠ [a,b,a]) (h _ (by decide) _ (by decide) ⟨[a,b],rfl⟩)

end ThreeWordCodes.GraftExample
