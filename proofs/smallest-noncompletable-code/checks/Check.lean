module

meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command
import SmallestNoncompletable

open SmallestNoncompletable ThreeWordCodes

-- The statement, its definitions, and the main steps.
#print SimultaneousMinimality
#print totalLength
#print maxLength
#print Xfinset
#print HasPositiveCompletion
#print IsMaximalCode
#check @simultaneous_minimality
#check @completion_of_small
#check @X_no_finite_maximal_completion
#check @X_invariants
#check @Xfinset_uniquelyDecodable
#check @small_code_completion
#check @prop5
#check @completion_of_totalLength_le_ten
#check @lemma7
#check @completion_of_reducible
#check @tree_reduction
#check @no_finite_maximal_completion
#check @no_binary_code
#check @Ser.factorization_of_weak
#check @Ser.weak_factorization
#check @Search.run_sound
#check @Search.profiles_run
#print axioms SmallestNoncompletable.simultaneous_minimality

-- The theorem applied to the binary alphabet: `X` itself is not completable, while removing
-- any of its four words gives a completable code.
example : ∀ M : Finset (List Bool), Xfinset false true ⊆ M →
    ¬ IsMaximalCode (M : Set (List Bool)) :=
  X_no_finite_maximal_completion (by decide)

example : HasPositiveCompletion ((({[false, false], [false, true, false, true],
    [true, false, false, false]} : Finset (List Bool))) : Set (List Bool)) := by
  refine completion_of_small _ ?_ (Or.inl (by decide))
  have hX := Xfinset_uniquelyDecodable (a := false) (b := true) (by decide)
  have sub : ∀ w ∈ (({[false, false], [false, true, false, true], [true, false, false, false]} :
      Finset (List Bool)) : Set (List Bool)), w ∈ (Xfinset false true : Set (List Bool)) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    simp only [Xfinset, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  exact fun L₁ L₂ h₁ h₂ e => hX L₁ L₂ (fun w hw => sub w (h₁ w hw)) (fun w hw => sub w (h₂ w hw)) e

-- Reject any new axiom in the transitive dependencies of the public results.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``SmallestNoncompletable.simultaneous_minimality,
      ``SmallestNoncompletable.completion_of_small,
      ``SmallestNoncompletable.X_no_finite_maximal_completion,
      ``SmallestNoncompletable.X_invariants,
      ``SmallestNoncompletable.Xfinset_uniquelyDecodable,
      ``SmallestNoncompletable.small_code_completion,
      ``SmallestNoncompletable.prop5,
      ``SmallestNoncompletable.completion_of_totalLength_le_ten,
      ``SmallestNoncompletable.lemma7,
      ``SmallestNoncompletable.completion_of_reducible,
      ``SmallestNoncompletable.tree_reduction,
      ``SmallestNoncompletable.no_finite_maximal_completion,
      ``SmallestNoncompletable.no_binary_code,
      ``SmallestNoncompletable.Search.run_sound,
      ``SmallestNoncompletable.Search.profiles_run] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
