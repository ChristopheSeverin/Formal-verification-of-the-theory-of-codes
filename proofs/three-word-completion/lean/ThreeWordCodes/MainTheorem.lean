module

public import ThreeWordCodes.CrossedOverlapTheorem

/-! # Positive finite completion of every three-word code -/

@[expose] public section
namespace ThreeWordCodes

/-- Every three-word code over a finite alphabet extends, on the same
alphabet, to a finite maximal code with a unique positive factorization. -/
theorem three_word_theorem.{u} : ThreeWordTheorem.{u} :=
  CrossedCase.overlap_suffices CrossedCase.overlap_impossible

/-- The main theorem with its alphabet, three-word set and hypotheses explicit. -/
theorem three_word_positive_completion {A : Type*} [Fintype A] (X : Finset (Word A))
    (card : X.card=3) (code : InformationTheory.IsUniquelyDecodable (X : Set (Word A))) :
    HasPositiveCompletion (X : Set (Word A)) :=
  three_word_theorem A X card code

end ThreeWordCodes
