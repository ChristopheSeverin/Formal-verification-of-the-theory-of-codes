module

public import ThreeWordCodes.CrossedIntermediateTests

/-! # Excluding the intermediate row for both lateral letter positions -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem intermediate_left (p q : Word Bool) (m : Model .intermediate p [a] q) : False := by
  obtain ⟨i,G,h,E,s,pf,qf,opposite,cop⟩ := lateral_shapes m rfl m.first m.last
  have base := m.ambiguous
  change ¬NamedCode (pieces p [a] q) at base
  have old := m.cuts false
  change ¬NamedCode (pieces p (q++p) [a]) at old
  have joined := Border.cycle_ambiguity old
  have test := m.cuts true
  change ¬NamedCode (pieces p q (q++p++[a])) at test
  have good := m.code
  change NamedCode (columnWords .intermediate p (q++p) [a]) at good
  rw [pf,qf] at test joined good
  obtain ⟨ends,s1⟩ := intermediate_margins i h s G E opposite test
  by_cases empty : G=[]
  · subst G
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have word : p=[b] := pf
      exact intermediate_b _ _ (word ▸ m)
    · have ab : p=[a,b] := pf
      have pure := swap_first_two base
      rw [ab,qf] at pure
      have pos := (left_marker_layout 1 0 s E).mp pure
      let word := mixed 0 E s
      have bad : ¬NamedCode (pieces [a,b] word (word++([a,b]++[a]))) := by
        change ¬NamedCode (pieces [a,b] word (word++[a,b]++[a])) at test
        rwa [List.append_assoc] at test
      have shift := shifted_products [a,b] word (by decide) (by simp [word,mixed]) (by change some a≠some b; decide) bad
      have all := alternating_tail_of_shift word ([a,b]++[a]) E s rfl pos shift
      rcases (show s=0 ∨ s=1 by omega) with rfl|rfl
      · exact joined_one .intermediate 1 0 0 [] E (Or.inr ⟨rfl,rfl⟩) rfl rfl all good
      · have wordform : word=[b]++(wordPow [a,b] E.length++[a]) := by
          change mixed 0 E 1=_
          calc mixed 0 E 1 = mixed 0 (List.replicate E.length 1) 1 := congrArg (fun l => mixed 0 l 1) all
               _ = Border.body E.length 1++[a] := (append_pure _ 0 0 1).symm
               _ = _ := by rw [body_ab,List.append_assoc]
        rw [wordform] at bad
        exact bad (alternating_intermediate_test E.length)
  · apply joined_many .intermediate (List.length_pos_iff.mpr empty) cop ends s1 joined ?_ good
    rintro rfl rfl rfl ge ee
    exact test (by simpa only [←ge,←ee] using joined_test_two G.length E.length)

theorem reverse_reading_conflict (u : Word Bool) (parsed : ∃ s,spell abReaders s=u++[a]) :
    ¬NamedCode (pieces [b,a] [a,b,a] ([a,b,a]++u)) := by
  obtain ⟨s,read⟩ := parsed
  let f := pieces [b,a] [a,b,a] ([a,b,a]++u)
  intro good
  have rel : spell f [Z,Q]=spell f (Q::(s.map some++[P])) := by
    simp only [spell_cons,spell_nil,List.append_nil,spell_append,f,spelled_old,pieces,addToken,pair,P,Q,Z]
    change ([a,b,a]++u)++[a,b,a]=[a,b,a]++(spell abReaders s++[b,a])
    rw [read,List.append_assoc,List.append_assoc]
    rfl
  exact (by decide : Z≠Q) (List.cons.inj (good rel)).1

theorem intermediate_right (t u : Word Bool) (m : Model .intermediate t u [a]) : False := by
  let p := t.reverse
  let q := u.reverse
  have pt : b∈t := m.has_marker (k:=Z) (l:=P) (by decide) rfl
  have qu : b∈u := m.has_marker (k:=Z) (l:=Q) (by decide) rfl
  have cp : (u.count b).Coprime (t.count b) :=
    m.marker_coprime (k:=Z) (l:=Q) (s:=P) (by decide) (by decide) (by decide) rfl
  have actualLast : t.getLast?≠u.getLast? := m.last
  have actualFirst : t.head?≠some a := m.first
  have first : p.head?≠q.head? := by simpa only [p,q,List.head?_reverse] using actualLast
  have last : p.getLast?≠some a := by simpa only [p,List.getLast?_reverse] using actualFirst
  obtain ⟨i,G,h,E,s,pf,qf,opposite,cop⟩ := lateral_pair (p:=p) (q:=q) (by simpa [p] using pt)
    (by simpa [q] using qu) (by simpa [p,q] using cp) first last
  have test := m.cuts false
  change ¬NamedCode (pieces t ([a]++t) u) at test
  have pad : ¬NamedCode (pieces p (p++[a]) q) := by simpa [p,q] using reverse_ambiguity test
  have small := m.cuts true
  change ¬NamedCode (pieces t [a] ([a]++t++u)) at small
  have newer : ¬NamedCode (pieces p [a] (q++p++[a])) := by simpa [p,q,List.append_assoc] using reverse_ambiguity small
  have joined : ¬NamedCode (pieces [a] p (q++p)) := by
    intro code
    apply swap_first_two newer
    let f := pieces [a] p (q++p)
    let extra : Option Bool → Word (Option Bool) | none => [P] | some _ => []
    have eqn : (fun i => f i++spell f (extra i))=pieces [a] p (q++p++[a]) := by
      funext k; rcases k with _|(_|_) <;> simp [f,extra,pieces,pair,addToken,P]
    exact eqn ▸ code.pad_right extra
  have good : NamedCode (columnWords .reversed p (q++p) [a]) := by
    have orig := m.code
    change NamedCode (pieces t ([a]++t) ([a]++t++u)) at orig
    have rev := orig.reverse
    rw [reverse_pieces] at rev
    simpa [p,q,columnWords,List.append_assoc] using rev
  rw [pf,qf,show mixed i G 0++[a]=mixed i G 1 from append_pure G i 0 1] at pad
  change ¬NamedCode (extended i G 0 h E s) at pad
  obtain ⟨_,s1,i1,h1⟩ := normalized_lengthening_margins pad (opposite.imp And.left And.right) (Or.inl rfl)
  have ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0) := by omega
  by_cases empty : G=[]
  · subst G
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have pb : t.reverse=[b] := pf
      have tb : t=[b] := by simpa using congrArg List.reverse pb
      exact intermediate_b _ _ (tb ▸ m)
    · have pab : t.reverse=[a,b] := pf
      have tb : t=[b,a] := by simpa using congrArg List.reverse pab
      have tail : u.getLast?=some b := by
        rw [←List.head?_reverse]; change q.head?=some b; rw [qf]; rfl
      rw [tb] at test
      exact reverse_reading_conflict u (read_after_b u tail test) (tb ▸ m.code)
  · rw [pf,qf] at good joined
    apply joined_many .reversed (List.length_pos_iff.mpr empty) cop ends s1 joined ?_ good
    rintro rfl rfl rfl ge ee
    exact pad (by simpa only [←ge,←ee] using pa_test_two G.length E.length (List.length_pos_iff.mpr empty) cop)

theorem intermediate_impossible (t u v : Word Bool) : ¬Model .intermediate t u v := by
  intro m
  obtain ⟨k,unit⟩ := m.letter
  rcases k with _|(_|_)
  · change v=[a] at unit
    exact intermediate_right t u (unit ▸ m)
  · change t=[a] at unit
    exact intermediate_central u v (unit ▸ m)
  · change u=[a] at unit
    exact intermediate_left t v (unit ▸ m)

/-- Row IV is the only remaining configuration in the proof by minimal obstruction. -/
theorem overlap_suffices.{u} (rowIV : ∀ t u v,¬Model .overlap t u v) : ThreeWordTheorem.{u} :=
  two_crossed_rows_suffice (fun t u v _ => intermediate_impossible t u v) rowIV

end ThreeWordCodes.CrossedCase
