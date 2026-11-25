module

public import ThreeWordCodes.CrossedModel

/-! # Reversal and interchange of the lateral pieces in rows I, III and IV -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open Border (pieces P Q Z)
variable {A : Type*}

private def lateral : Option Bool → Option Bool
  | none => Q
  | some false => P
  | some true => Z

private def entries (r : CrossedShape) (i : Option Bool) : Option Bool :=
  if r=.sharedShort then lateral i else i.map (!·)

private theorem raw (t u v : Word A) (k : Option Bool) :
    pieces t.reverse v.reverse u.reverse k=(pieces t u v (lateral k)).reverse := by rcases k with _|(_|_) <;> rfl

private theorem row_reverse (r : CrossedShape) (symm : r≠.intermediate) (t u v : Word A) :
    (fun k => (crossedWords r t u v (entries r k)).reverse)=crossedWords r t.reverse v.reverse u.reverse := by
  funext k
  cases r <;> rcases k with _|(_|_) <;> simp_all [crossedWords,entries,lateral,P,Q,Z,pair,addToken,List.append_assoc]

private theorem cut_reverse (r : CrossedShape) (symm : r≠.intermediate) (t u v : Word A) (side : Bool) :
    (fun k => (crossedShortening r side t u v (entries r k)).reverse)=crossedShortening r (!side) t.reverse v.reverse u.reverse := by
  funext k
  cases r <;> cases side <;> rcases k with _|(_|_) <;>
    simp_all [crossedShortening,entries,lateral,P,Q,Z,pair,addToken]

theorem Model.reverse {r t u v} (m : Model r t u v) (symm : r≠.intermediate) :
    Model r t.reverse v.reverse u.reverse := by
  have inv : ∀ k,lateral (lateral k)=k := by decide
  have eInv : ∀ k,entries r (entries r k)=k := by cases r <;> decide
  have ej := Function.LeftInverse.injective eInv
  have inj := Function.LeftInverse.injective inv
  obtain ⟨k,letter⟩ := m.letter
  refine ⟨fun k => ?_,⟨lateral k,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [raw,List.reverse_ne_nil_iff] using m.nonempty (lateral k)
  · rw [raw,inv,letter]; rfl
  · intro c d all
    apply m.divisors c d
    intro k
    simpa only [raw,inv,List.count_reverse] using all (lateral k)
  · have ends := m.last
    cases r <;> simp_all [firstPair,lastPair,Border.pieces,P,Q,Z,pair,addToken,ne_comm]
  · have ends := m.first
    cases r <;> simp_all [firstPair,lastPair,Border.pieces,P,Q,Z,pair,addToken,ne_comm]
  · intro k l ne comm
    apply m.noncommuting (lateral k) (lateral l) (inj.ne ne)
    simpa only [raw,List.reverse_append,List.reverse_reverse] using (congrArg List.reverse comm).symm
  · intro good
    apply m.ambiguous
    have h := good.reverse.reindex (f:=lateral) inj
    simpa only [raw,inv,List.reverse_reverse] using h
  · exact row_reverse r symm t u v ▸ m.code.reverse.reindex ej
  · intro side good
    apply m.cuts (!side)
    have h := good.reverse.reindex (f:=entries r) ej
    simpa only [cut_reverse r symm t.reverse v.reverse u.reverse side,List.reverse_reverse] using h

end ThreeWordCodes.CrossedCase
