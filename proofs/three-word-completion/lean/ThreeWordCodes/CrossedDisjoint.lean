module

public import ThreeWordCodes.CrossedCentral
public import ThreeWordCodes.CrossedReversal

/-! # Disjoint comparisons with a lateral letter -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

/-- In row III with u=a, the first cut fixes every gap of t v. The second
cut bounds its new initial margin even if t has only one marker. -/
theorem disjoint_left (t v : Word Bool) (m : Model .disjoint t [a] v) : False := by
  have vh : v.head?≠some a := Ne.symm m.first
  have vl : v.getLast?≠some a := Ne.symm m.last
  obtain ⟨g,vf⟩ := Border.body_form (w:=v) (m.nonempty Z) vh vl
  obtain ⟨h,e,q,tf⟩ := mixed_of_contains_marker (m.has_marker (k:=Q) (l:=P) (by decide) rfl)
  change t=mixed h e q at tf
  have cop := m.marker_coprime (k:=Q) (l:=P) (s:=Z) (by decide) (by decide) (by decide) rfl
  change (t.count b).Coprime (v.count b) at cop
  rw [tf,vf,mixed_count,mixed_count] at cop
  let H := e++q::g
  have pairForm : t++v=mixed h H 0 := by rw [tf,vf,join_mixed,Nat.add_zero]
  have whole : ([a]++t)++v=mixed (h+1) H 0 := by rw [List.append_assoc,pairForm,prepend_a]
  have short : [a]++t=mixed (h+1) e q := tf ▸ prepend_a h e q
  have good := m.code
  have longer := m.cuts false
  have smaller := m.cuts true
  change NamedCode (pieces [a] v (([a]++t)++v)) at good
  change ¬NamedCode (pieces [a] v (t++v)) at longer
  change ¬NamedCode (pieces [a] v ([a]++t)) at smaller
  rw [whole,vf] at good
  rw [pairForm,vf] at longer
  rw [short,vf] at smaller
  change NamedCode (layout 0 g 0 (h+1) H 0) at good
  change ¬NamedCode (layout 0 g 0 h H 0) at longer
  change ¬NamedCode (layout 0 g 0 (h+1) e q) at smaller
  by_cases empty : g=[]
  · subst g; exact (right_marker_layout 0 _ _ _).mpr (fun _ _ => Nat.zero_le _) good
  have pg := List.length_pos_iff.mpr empty
  have len : H.length+1=(e.length+1)+(g.length+1) := by simp [H]; omega
  have cp : (H.length+1).Coprime (g.length+1) := len.symm ▸ Nat.coprime_add_self_left.mpr cop
  obtain ⟨c,allG,allH,_⟩ := uniform_gaps_of_ambiguity longer (by omega) (by omega) cp
  obtain ⟨v,mem⟩ := List.exists_mem_of_ne_nil g empty
  have bound : h+1≤c := by
    by_cases onlyOne : e=[]
    · subst e
      have tiny := one_marker_gaps (k:=h+1) (l:=q) (fun code => swapped_ambiguity smaller code.1) v mem
      have identity := allG v mem
      omega
    · have diff : g.length≠e.length := by intro eqn; rw [←eqn,Nat.coprime_self] at cop; omega
      obtain ⟨d,uniform,_,_,_,left,_⟩ := uniform_gaps_of_distinct_counts smaller pg
        (List.length_pos_iff.mpr onlyOne) diff cop
      have same := (uniform v mem).symm.trans (allG v mem)
      omega
  have ge : g=List.replicate g.length c := List.eq_replicate_iff.mpr ⟨rfl,allG⟩
  have he : H=List.replicate H.length c := List.eq_replicate_iff.mpr ⟨rfl,allH⟩
  exact (uniform_repeat_ambiguity c 0 g.length 0 (h+1) H.length 0 (by omega) (by omega))
    (by simpa only [←ge,←he] using good)

theorem disjoint_right (t u : Word Bool) (m : Model .disjoint t u [a]) : False :=
  disjoint_left t.reverse u.reverse (m.reverse (by decide))

end ThreeWordCodes.CrossedCase
