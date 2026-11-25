module

public import ThreeWordCodes.CrossedOverlapMargins

/-! # The two uniform-gap cases in the overlapping row -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem overlap_two (m n : ℕ) (pm : 0<m) (cop : (n+1).Coprime (m+1)) :
    let t := mixed 0 (List.replicate m 2) 1
    let v := mixed 1 (List.replicate n 2) 0
    NamedCode (pieces ([a]++t) (t++v) v) := by
  intro t v
  let f := pieces (Border.marks m) [a] (Border.marks n++[a])
  let codeword : Option Bool → Word (Option Bool) | none => [Z] | some false => [P] | some true => [Q,P,Z]
  have independent : NamedCode f := by
    have base := residue_with_prefix [] m n pm cop
    have swapped : NamedCode (pieces (Border.marks m) [a] ([a]++Border.marks n)) :=
      by_contra fun neg => swap_first_two neg base
    have rev := swapped.reverse
    rw [reverse_pieces] at rev
    simpa [f,Border.marks] using rev
  have marked : NamedCode codeword := by
    let pad : Option Bool → Word (Option Bool) | some true => [P,Z] | _ => []
    have shape : codeword=fun k => k::pad k := by funext k; rcases k with _|(_|_) <;> rfl
    rw [shape]; exact first_marked_code pad
  have atWord : GroupCoordinates.change 1 1 (groupWord ([a]++t))=groupWord (Border.marks m) := by
    change GroupCoordinates.change 1 1 (groupWord (mixed 1 (List.replicate m 2) 1))=_
    simpa [run] using gap_two_image 1 m 1 (by decide) (by decide)
  have T : GroupCoordinates.change 1 1 (groupWord t)=groupWord ([a]++Border.marks m) := by
    simpa [t,run] using gap_two_image 0 m 1 (by decide) (by decide)
  have V : GroupCoordinates.change 1 1 (groupWord v)=groupWord (Border.marks n++[a]) := by
    simpa [v,run] using gap_two_image 1 n 0 (by decide) (by decide)
  have eqn : SameEquations (pieces ([a]++t) (t++v) v) (fun k => spell f (codeword k)) := by
    apply sameEquations_of_group_change (GroupCoordinates.change 1 1) (GroupCoordinates.change_involutive 1 1).injective
    rintro (_|(_|_))
    · simpa only [codeword,spell_cons,spell_nil,List.append_nil,f,pieces,Z,addToken] using V
    · simpa only [codeword,spell_cons,spell_nil,List.append_nil,f,pieces,P,addToken,pair] using atWord
    · change GroupCoordinates.change 1 1 (groupWord (t++v))=groupWord (spell f [Q,P,Z])
      rw [groupWord_append,map_mul,T,V,←groupWord_append]
      simp [f,pieces,Q,P,Z,addToken,pair]
  exact eqn.namedCode_iff.mpr (independent.substitution marked)

theorem overlap_many (G E : List ℕ) (r s q : ℕ) (pm : 0<G.length) (cop : (E.length+1).Coprime (G.length+1))
    (ends : (r=0 ∧ q=1) ∨ (r=1 ∧ q=0)) (bound : s≤1)
    (m : Model .overlap (mixed 0 G r) [a] (mixed s E q)) : False := by
  let L := G++(r+s)::E
  have joint : mixed 0 G r++mixed s E q=mixed 0 L q := join_mixed G E 0 r s q
  have old := Border.cycle_ambiguity (show ¬NamedCode (pieces ([a]++mixed 0 G r) (mixed 0 G r++mixed s E q) [a]) from m.cuts true)
  rw [joint,prepend_a] at old
  have len : L.length+1=(E.length+1)+(G.length+1) := by simp [L]; omega
  have cp : (L.length+1).Coprime (G.length+1) := len.symm ▸ Nat.coprime_add_self_left.mpr cop
  obtain ⟨g,gu,lu,one,_,_,_⟩ := uniform_gaps_of_ambiguity (g:=G) (e:=L) old (by omega) (by omega) cp
  have join := lu (r+s) (by simp [L])
  have gr : G=List.replicate G.length g := List.eq_replicate_iff.mpr ⟨rfl,gu⟩
  have er : E=List.replicate E.length g := List.eq_replicate_iff.mpr ⟨rfl,fun x h => lu x (by simp [L,h])⟩
  have lr : L=List.replicate L.length g := List.eq_replicate_iff.mpr ⟨rfl,lu⟩
  rcases (show g=1 ∨ g=2 by omega) with rfl|rfl
  · have good := m.code
    change NamedCode (pieces ([a]++mixed 0 G r) (mixed 0 G r++mixed s E q) (([a]++mixed 0 G r)++mixed s E q)) at good
    rw [List.append_assoc,joint] at good
    exact overlap_unit G.length L.length r q ends (by simpa only [←gr,←lr] using good)
  · obtain rfl : r=1 := by omega
    obtain rfl : s=1 := by omega
    obtain rfl : q=0 := by omega
    have cut := m.cuts false
    change ¬NamedCode (pieces ([a]++mixed 0 G 1) (mixed 0 G 1++mixed 1 E 0) (mixed 1 E 0)) at cut
    exact cut (by simpa only [←gr,←er] using overlap_two G.length E.length pm cop)

end ThreeWordCodes.CrossedCase
