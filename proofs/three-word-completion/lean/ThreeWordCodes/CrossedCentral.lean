module

public import ThreeWordCodes.CrossedModel

/-! # The common word is the model letter in crossed rows I and II -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem Model.has_marker {r t u v} (m : Model r t u v) {k l : Option Bool} (ne : k≠l)
    (letter : pieces t u v k=[a]) : b∈pieces t u v l := by
  rcases decompose (pieces t u v l) with ⟨n,pure⟩ | ⟨i,g,j,word⟩
  · apply False.elim
    apply m.noncommuting k l ne
    rw [letter,pure]
    change run 1++run n=run n++run 1
    rw [←run_add,←run_add,Nat.add_comm]
  · exact List.count_pos_iff.mp (by rw [word,mixed_count]; omega)

theorem Model.marker_coprime {r t u v} (m : Model r t u v) {k l s : Option Bool} (kl : k≠l) (ks : k≠s)
    (ls : l≠s) (letter : pieces t u v k=[a]) :
    ((pieces t u v l).count b).Coprime ((pieces t u v s).count b) := by
  have cover : ∀ k l s : Option Bool,k≠l → k≠s → l≠s → ∀ w,w=k ∨ w=l ∨ w=s := by decide
  apply Nat.dvd_one.mp
  apply m.divisors b
  intro w
  rcases cover k l s kl ks ls w with rfl|rfl|rfl
  · simp [letter,a,b]
  · exact Nat.gcd_dvd_left .. 
  · exact Nat.gcd_dvd_right ..

theorem left_marker_layout (c i j : ℕ) (g : List ℕ) :
    ¬NamedCode (layout c [] 0 i g j) ↔ ∀ d∈g,c≤d :=
  (ambiguity_left_margin c (mixed i g j)).trans (gaps_spec c i g j)

theorem right_marker_layout (c i j : ℕ) (g : List ℕ) :
    ¬NamedCode (layout 0 [] c i g j) ↔ ∀ d∈g,c≤d :=
  (ambiguity_right_margin c (mixed i g j)).trans (gaps_spec c i g j)

theorem prepend_a (h : ℕ) (g : List ℕ) (j : ℕ) : [a]++mixed h g j=mixed (h+1) g j := rfl

private theorem data_of_central {r u v} (m : Model r [a] u v) (initial : (some a)≠v.head?)
    (final : (some a)≠u.getLast?) :
    ∃ i g e q,u=mixed i g 0 ∧ v=mixed 0 e q ∧ (e.length+1).Coprime (g.length+1) := by
  obtain ⟨i,g,j,uf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Q) (by decide) rfl)
  obtain ⟨h,e,q,vf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Z) (by decide) rfl)
  change u=mixed i g j at uf
  change v=mixed h e q at vf
  have vh := Border.head_b (w:=v) (m.nonempty Z) initial.symm
  have ul : u.getLast?=some b := by
    have nh : u.reverse.head?≠some a := by simpa using final.symm
    have ne : u≠[] := m.nonempty Q
    simpa using Border.head_b (w:=u.reverse) (by simpa using ne) nh
  obtain rfl : h=0 := head_zero (vf ▸ vh)
  obtain rfl : j=0 := last_zero (uf ▸ ul)
  have cop := m.marker_coprime (k:=P) (l:=Z) (s:=Q) (by decide) (by decide) (by decide) rfl
  change (v.count b).Coprime (u.count b) at cop
  exact ⟨i,g,e,q,uf,vf,by simpa [uf,vf,mixed_count] using cop⟩

private theorem distinct_of_coprime {g e : List ℕ} (pg : 0<g.length) (cop : (e.length+1).Coprime (g.length+1)) :
    g.length≠e.length := by
  intro eqn
  rw [←eqn,Nat.coprime_self] at cop
  omega

/-- Row I with central letter. A single-marker side keeps its gap test
after padding the other side. With two long sides the two shortenings
bound both margins of the prescribed row, giving competing tilings. -/
theorem shared_central (u v : Word Bool) (m : Model .sharedShort [a] u v) : False := by
  obtain ⟨i,g,e,q,uf,vf,cop⟩ := data_of_central m m.first m.last
  have U : [a]++u=mixed (i+1) g 0 := uf ▸ prepend_a i g 0
  have V : v++[a]=mixed 0 e (q+1) := vf ▸ append_pure e 0 q 1
  have x := m.code
  have y := m.cuts false
  have z := m.cuts true
  change NamedCode (pieces [a] ([a]++u) (v++[a])) at x
  change ¬NamedCode (pieces [a] u (v++[a])) at y
  change ¬NamedCode (pieces [a] ([a]++u) v) at z
  rw [U,V] at x
  rw [uf,V] at y
  rw [U,vf] at z
  change NamedCode (layout (i+1) g 0 0 e (q+1)) at x
  change ¬NamedCode (layout i g 0 0 e (q+1)) at y
  change ¬NamedCode (layout (i+1) g 0 0 e q) at z
  by_cases empty : g=[]
  · subst g
    exact (left_marker_layout ..).mpr ((left_marker_layout ..).mp z) x
  by_cases small : e=[]
  · subst e
    apply (swapped_ambiguity (show ¬NamedCode (layout 0 [] (q+1) (i+1) g 0) from
      (right_marker_layout ..).mpr ((right_marker_layout ..).mp (swapped_ambiguity y)))) x
  have pg := List.length_pos_iff.mpr empty
  have pe := List.length_pos_iff.mpr small
  have ne := distinct_of_coprime pg cop
  obtain ⟨c,ug,ue,_,_,_,right⟩ := uniform_gaps_of_distinct_counts y pg pe ne cop
  obtain ⟨d,dg,_,left,_⟩ := uniform_gaps_of_distinct_counts z pg pe ne cop
  obtain ⟨a,mem⟩ := List.exists_mem_of_ne_nil g empty
  have same : d=c := (dg a mem).symm.trans (ug a mem)
  have ge : g=List.replicate g.length c := List.eq_replicate_iff.mpr ⟨rfl,ug⟩
  have ee : e=List.replicate e.length c := List.eq_replicate_iff.mpr ⟨rfl,ue⟩
  exact (uniform_repeat_ambiguity c (i+1) g.length 0 0 e.length (q+1) (by omega) (by omega))
    (by simpa only [←ge,←ee] using x)

/-- Row II with central letter. The longer word includes the join of the
two mixed bodies. Its gap determines the maximum padding of the first. -/
theorem intermediate_central (u v : Word Bool) (m : Model .intermediate [a] u v) : False := by
  obtain ⟨i,g,e,q,uf,vf,cop⟩ := data_of_central m m.first m.last
  let H := e++(q+1+i)::g
  have first : v++[a]=mixed 0 e (q+1) := vf ▸ append_pure e 0 q 1
  have combined : (v++[a])++u=mixed 0 H 0 := by rw [first,uf,join_mixed]
  have x := m.code
  have y := m.cuts false
  have z := m.cuts true
  change NamedCode (pieces [a] (v++[a]) (v++[a]++u)) at x
  change ¬NamedCode (pieces [a] (v++[a]) u) at y
  change ¬NamedCode (pieces [a] v (v++[a]++u)) at z
  rw [combined,first] at x
  rw [first,uf] at y
  rw [combined,vf] at z
  change NamedCode (layout 0 e (q+1) 0 H 0) at x
  change ¬NamedCode (layout 0 e (q+1) i g 0) at y
  change ¬NamedCode (layout 0 e q 0 H 0) at z
  by_cases empty : e=[]
  · subst e
    have inner := (right_marker_layout ..).mp y
    apply ((right_marker_layout ..).mpr ?_) x
    intro s hs
    rcases (show s=q+1+i ∨ s∈g from by simpa [H] using hs) with rfl|mem
    · omega
    · exact inner s mem
  have len : H.length+1=(g.length+1)+(e.length+1) := by simp [H]; omega
  have cp : (H.length+1).Coprime (e.length+1) := len.symm ▸ Nat.coprime_add_self_left.mpr cop.symm
  have pe := List.length_pos_iff.mpr empty
  obtain ⟨c,ev,all,_⟩ := uniform_gaps_of_ambiguity z (by omega) (by omega) cp
  have join := all (q+1+i) (by simp [H])
  have ee : e=List.replicate e.length c := List.eq_replicate_iff.mpr ⟨rfl,ev⟩
  have full : H=List.replicate H.length c := List.eq_replicate_iff.mpr ⟨rfl,all⟩
  exact (uniform_repeat_ambiguity c 0 e.length (q+1) 0 H.length 0 (by omega) (by omega))
    (by simpa only [←ee,←full] using x)

end ThreeWordCodes.CrossedCase
