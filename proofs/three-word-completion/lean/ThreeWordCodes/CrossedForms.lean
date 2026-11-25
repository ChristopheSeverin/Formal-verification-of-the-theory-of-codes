module

public import ThreeWordCodes.Classification
public import ThreeWordCodes.Alphabet

/-! # Exhaustive crossed comparison shapes in Section 5

A prefix and a suffix involving two different pairs of a three-word code
share exactly one name. If the common word is the longer one, the two cuts
either leave a nonempty middle or overlap. Exact juxtaposition gives two parses.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A : Type*}

inductive CrossedShape
  | sharedShort | intermediate | disjoint | overlap
  deriving DecidableEq

def crossedWords (shape : CrossedShape) (t u v : Word A) : Option Bool → Word A :=
  match shape with
  | .sharedShort => addToken (pair t (t++u)) (v++t)
  | .intermediate => addToken (pair t (v++t)) (v++t++u)
  | .disjoint => addToken (pair u v) (u++t++v)
  | .overlap => addToken (pair (u++t) (t++v)) (u++t++v)

def InCrossedTable (f : Fin 3 → Word A) : Prop :=
  ∃ shape : CrossedShape, ∃ t u v : Word A, t≠[] ∧ u≠[] ∧ v≠[] ∧
    ∃ order : Option Bool ≃ Fin 3, (fun x => f (order x)) = crossedWords shape t u v

theorem order_three_entries {f : Fin 3 → Word A} {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (v : Option Bool → Word A) (hi : f i=v (some false)) (hj : f j=v (some true)) (hk : f k=v none) :
    ∃ order : Option Bool ≃ Fin 3, (fun x => f (order x)) = v := by
  have all : ∀ i j k : Fin 3, i≠j → i≠k → j≠k → Function.Bijective (threeNames i j k) := by decide
  let order := Equiv.ofBijective _ (all i j k ij ik jk)
  refine ⟨order,?_⟩
  funext x
  rcases x with _ | (_ | _) <;> assumption

private theorem middle_ne {f : Fin 3 → Word A} (code : NamedCode f) (i j k : Fin 3) :
    f k ≠ f i ++ f j := by
  intro eqn
  have he : spell f [k] = spell f [i,j] := by simpa using eqn
  have bad := congrArg List.length (code he)
  simp at bad

/-- This exhaustive normal form only uses unique decoding and the two proper
comparisons. No minimality or realization theorem is needed. -/
theorem crossed_table_exhaustive (f : Fin 3 → Word Bool) (code : NamedCode f)
    (crossed : HasCrossedComparisons f) :
    InCrossedTable f ∨ InCrossedTable (fun i => (f i).reverse) := by
  obtain ⟨i,j,k,l,pre,suf,same,opposite⟩ := crossed
  obtain ⟨⟨u,pu⟩,lengthP⟩ := pre
  obtain ⟨⟨v,sv⟩,lengthS⟩ := suf
  have nzU : u≠[] := by
    rintro rfl
    rw [List.append_nil] at pu
    rw [pu] at lengthP
    exact Nat.lt_irrefl _ lengthP
  have nzV : v≠[] := by
    rintro rfl
    simp only [List.nil_append] at sv
    rw [sv] at lengthS
    exact Nat.lt_irrefl _ lengthS
  have ij : i≠j := by rintro rfl; exact Nat.lt_irrefl _ lengthP
  have kl : k≠l := by rintro rfl; exact Nat.lt_irrefl _ lengthS
  by_cases ik : i=k
  · subst k
    have jl : j≠l := fun he => same ⟨rfl,he⟩
    exact Or.inl ⟨.sharedShort,f i,u,v,code.entry_ne_nil _,nzU,nzV,
      order_three_entries ij kl jl _ rfl pu.symm sv.symm⟩
  by_cases il : i=l
  · subst l
    have kj : k≠j := fun he => opposite ⟨rfl,he.symm⟩
    apply Or.inl
    refine ⟨.intermediate,f k,u,v,code.entry_ne_nil _,nzU,nzV,order_three_entries kl kj ij _ rfl sv.symm ?_⟩
    change f j = v++f k++u
    rw [sv,pu]
  by_cases jk : j=k
  · subst k
    have il' : i≠l := il
    apply Or.inr
    refine ⟨.intermediate,(f i).reverse,v.reverse,u.reverse,by simpa using code.entry_ne_nil i,
      by simpa using nzV,by simpa using nzU,order_three_entries (f:=fun z => (f z).reverse) ij il' kl _ rfl ?_ ?_⟩
    · simpa [crossedWords,addToken,pair] using congrArg List.reverse pu.symm
    · change (f l).reverse = u.reverse ++ (f i).reverse ++ v.reverse
      rw [←sv,←pu,List.reverse_append,List.reverse_append]
  have jl : j=l := by
    have cover : ∀ i j k l : Fin 3, i≠j → k≠l → i≠k → i≠l → j≠k → j=l := by decide
    exact cover _ _ _ _ ij kl ik il jk
  subst l
  have joined := pu.trans sv.symm
  rcases List.append_eq_append_iff.mp joined with ⟨t,pv,ut⟩ | ⟨t,pv,vt⟩
  · have nt : t≠[] := by
      rintro rfl
      exact middle_ne code i k j (by simp_all)
    apply Or.inl
    refine ⟨.disjoint,t,f i,f k,nt,code.entry_ne_nil _,code.entry_ne_nil _,
      order_three_entries ik ij (Ne.symm jk) _ rfl rfl ?_⟩
    change f j = f i ++ t ++ f k
    rw [←sv,pv]
  · have nt : t≠[] := by
      rintro rfl
      exact middle_ne code i k j (by simp_all)
    apply Or.inl
    refine ⟨.overlap,t,v,u,nt,nzV,nzU,order_three_entries ik ij (Ne.symm jk) _ pv vt ?_⟩
    change f j = v ++ t ++ u
    rw [←pv,pu]

theorem ClassificationInput.reverse {f : Fin 3 → Word Bool} (v : ClassificationInput f) :
    ClassificationInput (fun k => (f k).reverse) := by
  refine ⟨v.code.reverse,by simpa using v.lastLetters,by simpa using v.firstLetters,
    by simpa using v.divisors,?_⟩
  intro w sz code
  have bound : totalWordLength (fun k => (w k).reverse) < totalWordLength f := by
    simpa [totalWordLength] using sz
  simpa using (v.shorter _ bound code.reverse).reverse

/-- A version of the main reduction exposing the four rows of the crossed
table as well as the border family. -/
theorem border_and_four_rows_suffice.{u}
    (border : ∀ v, ClassificationInput v → HasBorder v → Completable v)
    (rows : ∀ v, ClassificationInput v → InCrossedTable v → Completable v) : ThreeWordTheorem.{u} := by
  apply border_and_crossed_suffice border
  intro v h crossed
  rcases crossed_table_exhaustive v h.code crossed with d | d
  · exact rows v h d
  · simpa using (rows _ h.reverse d).reverse

end ThreeWordCodes
