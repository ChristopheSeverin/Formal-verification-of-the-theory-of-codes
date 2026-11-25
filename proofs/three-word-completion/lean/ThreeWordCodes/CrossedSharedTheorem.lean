module

public import ThreeWordCodes.CrossedAlternating
public import ThreeWordCodes.CrossedReadings

/-! # Complete exclusion of the shared-short row (I) -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

/-- The join fixes g=s+i. Opposite initials and the margin bounds leave
gap one or the single gap-two configuration (i,h,s)=(1,0,1). -/
theorem joined_many (column : Column) {i h s : ℕ} {G E : List ℕ}
    (many : 0<G.length) (cop : (E.length+1).Coprime (G.length+1))
    (ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0)) (s1 : s≤1)
    (amb : ¬NamedCode (pieces [a] (mixed i G 0) (mixed h E s++mixed i G 0)))
    (two : i=1 → h=0 → s=1 → G=List.replicate G.length 2 → E=List.replicate E.length 2 → False) :
    ¬NamedCode (columnWords column (mixed i G 0) (mixed h E s++mixed i G 0) [a]) := by
  obtain ⟨g,e,_,bh⟩ := joined_uniform many cop amb
  rcases (show s+i=1 ∨ s+i=2 by omega) with unit|double
  · rw [unit] at g e
    exact joined_one column i h s G E ends unit g e
  · rw [double] at g e
    exact (two (by omega) (by omega) (by omega) g e).elim

private theorem ambiguity_from_reading {p q : Word Bool} (read : ∃ s,spell (pair p (p++[a])) s=[a]++q) :
    ¬NamedCode (pieces p (p++[a]) (q++p)) := by
  obtain ⟨s,form⟩ := read
  let f := pieces p (p++[a]) (q++p)
  intro code
  have word : spell f [Q,Z]=spell f (P::(s.map some++[P])) := by
    simp only [spell_cons,spell_nil,List.append_nil,spell_append,f,spelled_old,form,pieces,P,Q,Z,addToken,pair,List.append_assoc]
  exact (by decide : Q≠P) (List.cons.inj (code word)).1

theorem shared_left (p q : Word Bool) (m : Model .sharedShort p [a] q) : False := by
  obtain ⟨i,G,h,E,s,pf,qf,opposite,cop⟩ := lateral_shapes m rfl m.first m.last
  have old := m.cuts false
  change ¬NamedCode (pieces p [a] (q++p)) at old
  have test := m.cuts true
  change ¬NamedCode (pieces p (p++[a]) q) at test
  have good := m.code
  change NamedCode (pieces p (p++[a]) (q++p)) at good
  have pad := test
  rw [pf,qf,show mixed i G 0++[a]=mixed i G 1 from append_pure G i 0 1] at pad
  change ¬NamedCode (extended i G 0 h E s) at pad
  have someZero : i=0 ∨ h=0 := opposite.imp And.left And.right
  obtain ⟨_,s1,i1,h1⟩ := normalized_lengthening_margins pad someZero (Or.inl rfl)
  have ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0) := by omega
  by_cases onlyOne : G=[]
  · subst G
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have p_is_b : p=[b] := pf
      rw [p_is_b] at good test
      exact (append_b_preserves_test q).mpr test good
    · have ab : p=[a,b] := pf
      have firstQ : q.head?=some b := by rw [qf]; rfl
      rw [ab] at test
      apply ambiguity_from_reading (p:=p) (q:=q) ?_ good
      rw [ab]
      exact read_before_b q firstQ test
  · have swapped : ¬NamedCode (pieces [a] p (q++p)) := by
      let s (k : Option Bool) := k.map (!·)
      have e : (fun k => pieces [a] p (q++p) (s k))=pieces p [a] (q++p) := by
        funext k; rcases k with _|(_|_) <;> rfl
      exact fun code => old (e ▸ code.reindex (f:=s) (by decide))
    change NamedCode (columnWords .shared p (q++p) [a]) at good
    rw [pf,qf] at good swapped
    apply joined_many .shared (List.length_pos_iff.mpr onlyOne) cop ends s1 swapped ?_ good
    rintro rfl rfl rfl ge ee
    exact pad (by simpa only [←ge,←ee] using pa_test_two G.length E.length (List.length_pos_iff.mpr onlyOne) cop)

theorem shared_impossible (t u v : Word Bool) : ¬Model .sharedShort t u v := by
  intro m
  obtain ⟨k,unit⟩ := m.letter
  rcases k with _|(_|_)
  · change v=[a] at unit
    subst v
    exact shared_left t.reverse u.reverse (m.reverse (by decide))
  · change t=[a] at unit
    exact shared_central u v (unit ▸ m)
  · change u=[a] at unit
    exact shared_left t v (unit ▸ m)

end ThreeWordCodes.CrossedCase
