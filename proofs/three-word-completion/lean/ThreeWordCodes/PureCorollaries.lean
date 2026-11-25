module

public import ThreeWordCodes.PurePowerTheorem

/-! # Proposition 6 for finite sets and for decoded triples -/

@[expose] public section
namespace ThreeWordCodes
variable {A B I : Type*}

/-- Proposition 6 in the finite-set interface of the main theorem. -/
theorem three_word_pure_power_completion [Fintype A] (X : Finset (Word A)) (card : X.card=3)
    (code : InformationTheory.IsUniquelyDecodable (X : Set (Word A))) (letter : A) (n : ℕ)
    (pure : List.replicate n letter ∈ X) : HasPositiveCompletion (X : Set (Word A)) := by
  obtain ⟨v,range,names⟩ := enumerate_three X card code
  have contained : List.replicate n letter ∈ Set.range v := by rw [range]; exact pure
  obtain ⟨j,word⟩ := contained
  exact range ▸ (BinaryGaps.pure_power_completion A v names ⟨j,letter,n,word⟩).2

noncomputable def threeOrder : Option Bool ≃ Fin 3 := Equiv.ofBijective (threeNames 0 1 2) (by decide)

/-- Reindex a three-name alphabet without changing which entry is a power. -/
theorem named_pure_power_completion [Fintype A] (order : I ≃ Fin 3) {v : I → Word A}
    (code : NamedCode v) (pure : ∃ i a n, v i=List.replicate n a) : Completable v := by
  obtain ⟨i,a,n,entry⟩ := pure
  let w (j : Fin 3) := v (order.symm j)
  have done := BinaryGaps.pure_power_completion A w (code.reindex order.symm.injective)
    ⟨order i,a,n,by simpa [w] using entry⟩
  simpa [w] using done.reindex order.injective

/-- A named code with two different entries cannot read on a commuting pair. -/
theorem pair_basis_of_coded_reading [Fintype A] (g : Bool → Word A) (outer : Option Bool → Word Bool)
    (code : NamedCode (fun i => spell g (outer i))) : Completable g := by
  have ne : g false++g true ≠ g true++g false := by
    intro commutes
    obtain ⟨r,n,m,x,y⟩ := (commuting_iff_common_power _ _).mp commutes
    obtain ⟨p,hp⟩ := powers_of_generators x y (outer none)
    obtain ⟨q,hq⟩ := powers_of_generators x y (outer (some false))
    exact code.noncommuting_entries (by decide : (none : Option Bool) ≠ some false)
      (by simp only [hp,hq]; exact wordPow_comm r p q)
  have name : pair (g false) (g true)=g := by funext i; cases i <;> rfl
  exact name ▸ noncommuting_pair_completion _ _ ne

/-- An injective triple that reads on a completable family inherits a
completion if one reading is a power of a single token name. -/
theorem pure_reading_completion [Fintype A] [Fintype B] [Nonempty B]
    (order : I ≃ Fin 3) {v : B → Word A} (base : Completable v) (d : I → Word B)
    {f : I → Word A} (read : (fun i => spell v (d i))=f) (code : NamedCode f)
    (power : ∃ j b n, d j=List.replicate n b) : Completable f := by
  have named := (base.1.preserves_equations d).namedCode_iff.mpr (read.symm ▸ code)
  exact read ▸ base.substitute (named_pure_power_completion order named power)

end ThreeWordCodes
