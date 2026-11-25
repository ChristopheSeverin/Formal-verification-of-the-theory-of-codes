module

public import ThreeWordCodes.PureReduction

/-! # The border and crossed cases are exhaustive for a minimal obstruction

A counterexample on any finite alphabet yields a shortest binary counterexample.
It has both end letters at both ends, independent entries in pairs, and a proper
comparison in each direction. The two compared pairs either coincide or cross.
-/

@[expose] public section
namespace ThreeWordCodes

private def Obstruction (v : Fin 3 → Word Bool) := NamedCode v ∧ ¬ Completable v
private def Minimal (v : Fin 3 → Word Bool) := Obstruction v ∧
  ∀ w, Obstruction w → totalWordLength v ≤ totalWordLength w

private theorem shortest {u : Fin 3 → Word Bool} (bad : Obstruction u) : ∃ v, Minimal v := by
  classical
  let want (n : ℕ) := ∃ v, Obstruction v ∧ totalWordLength v=n
  have existsN : ∃ n, want n := ⟨_,u,bad,rfl⟩
  obtain ⟨v,no,sz⟩ := Nat.find_spec existsN
  exact ⟨v,no,fun w fail => sz ▸ Nat.find_min' existsN ⟨w,fail,rfl⟩⟩

private theorem reverse_bad {v : Fin 3 → Word Bool} (h : Obstruction v) :
    Obstruction (fun i => (v i).reverse) :=
  ⟨h.1.reverse,fun proof => h.2 (by simpa using proof.reverse)⟩

private theorem reverse_min {v : Fin 3 → Word Bool} (h : Minimal v) :
    Minimal (fun i => (v i).reverse) := by
  refine ⟨reverse_bad h.1,fun w bad => ?_⟩
  simpa [totalWordLength] using h.2 _ (reverse_bad bad)

private theorem terminal_letters {v : Fin 3 → Word Bool} (h : Minimal v) :
    ∃ f : Bool → Bool, Function.Surjective f ∧ LeftReductionTrace v (fun c => [f c]) :=
  literal_trace_of_minimal_decoding h.1.1 h.1.2 (fun _ d _ _ cd no => h.2 d ⟨cd,no⟩)

def ProperPrefix {A : Type*} (u v : Word A) : Prop := u <+: v ∧ u.length < v.length
def ProperSuffix {A : Type*} (u v : Word A) : Prop := u <:+ v ∧ u.length < v.length

private theorem comparison {v : Fin 3 → Word Bool} (bad : Obstruction v) :
    ∃ i j, ProperPrefix (v i) (v j) := by
  have notFree : ¬ InformationTheory.IsPrefixFree (Set.range v) :=
    fun yes => bad.2 (completable_prefix bad.1.entries_injective bad.1.entry_ne_nil yes)
  change ¬ (∀ x ∈ Set.range v, ∀ y ∈ Set.range v, x <+: y → x=y) at notFree
  push Not at notFree
  obtain ⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,hp,ne⟩ := notFree
  exact ⟨i,j,hp,lt_of_not_ge (fun le => ne (hp.eq_of_length_le le))⟩

/-- Conditions available to both classification arguments. The final field is
the induction hypothesis on every strictly shorter binary code. -/
structure ClassificationInput (v : Fin 3 → Word Bool) : Prop where
  code : NamedCode v
  firstLetters : ∀ c, ∃ i, (v i).head? = some c
  lastLetters : ∀ c, ∃ i, (v i).getLast? = some c
  divisors : ∀ (c : Bool) (m : ℕ), (∀ i, m ∣ (v i).count c) → m ∣ 1
  shorter : ∀ w : Fin 3 → Word Bool, totalWordLength w < totalWordLength v → NamedCode w → Completable w

def HasBorder (v : Fin 3 → Word Bool) : Prop :=
  ∃ i j, ProperPrefix (v i) (v j) ∧ ProperSuffix (v i) (v j)

def HasCrossedComparisons (v : Fin 3 → Word Bool) : Prop :=
  ∃ i j k l, ProperPrefix (v i) (v j) ∧ ProperSuffix (v k) (v l) ∧
    ¬ (i=k ∧ j=l) ∧ ¬ (i=l ∧ j=k)

/-- The remaining classification problems of Sections 4 and 5 suffice for the
page-one theorem, including alphabets larger than the support of the input. -/
theorem border_and_crossed_suffice.{u}
    (border : ∀ v, ClassificationInput v → HasBorder v → Completable v)
    (crossed : ∀ v, ClassificationInput v → HasCrossedComparisons v → Completable v) :
    ThreeWordTheorem.{u} := by
  apply binary_suffices
  intro X card hc
  obtain ⟨w,range,code⟩ := enumerate_three X card hc
  rw [←range]
  by_contra fail
  obtain ⟨v,min⟩ := shortest (u:=w) ⟨code,fun h => fail h.2⟩
  obtain ⟨first,last,div,_⟩ := invariants_of_literal_traces (terminal_letters min)
    (terminal_letters (reverse_min min))
  have input : ClassificationInput v := ⟨min.1.1,first,last,div,by
    intro s lt code
    by_contra no
    exact (Nat.not_le_of_lt lt) (min.2 _ ⟨code,no⟩)⟩
  obtain ⟨i,j,prefixPair⟩ := comparison min.1
  obtain ⟨k,l,rev,sz⟩ := comparison (reverse_bad min.1)
  have suffixPair : ProperSuffix (v k) (v l) := ⟨List.reverse_prefix.mp rev,by simpa using sz⟩
  apply min.1.2
  by_cases same : i=k ∧ j=l
  · obtain ⟨rfl,rfl⟩ := same
    exact border v input ⟨_,_,prefixPair,suffixPair⟩
  · apply crossed v input
    refine ⟨i,j,k,l,prefixPair,suffixPair,same,?_⟩
    rintro ⟨rfl,rfl⟩
    exact (Nat.not_lt_of_ge prefixPair.2.le) suffixPair.2

end ThreeWordCodes
