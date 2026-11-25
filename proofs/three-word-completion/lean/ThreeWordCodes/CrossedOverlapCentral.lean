module

public import ThreeWordCodes.CrossedIntermediateTheorem

/-! # The overlapping row with the common piece equal to a letter -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)
variable {A : Type*}

/-- Padding the third word on the left with the second word preserves its code property. -/
theorem pad_third (x y z : Word A) (good : NamedCode (pieces x y z)) : NamedCode (pieces x y (y++z)) := by
  let g := pieces x y z
  let pad : Option Bool → Word (Option Bool) | none => [Q] | some _ => []
  have form : (fun k => spell g (pad k)++g k)=pieces x y (y++z) := by
    funext k; rcases k with _|(_|_) <;> simp [g,pad,pieces,addToken,pair,Q]
  exact form ▸ good.pad_left pad

/-- If K starts and ends in b, ambiguity of ba,K,aK forces K to alternate. -/
theorem alternating_auxiliary (E : List ℕ) (bad : ¬NamedCode (pieces [b,a] (mixed 0 E 0) ([a]++mixed 0 E 0))) :
    E=List.replicate E.length 1 := by
  let q := mixed 0 E.reverse 0
  have rev : ¬NamedCode (pieces [a,b] q (q++[a])) := by
    simpa [q,reverse_mixed] using reverse_ambiguity bad
  have small : ¬NamedCode (pieces [a] [a,b] q) :=
    Border.cycle_ambiguity (fun h => rev (pad_third [a,b] q [a] h))
  have pos := (left_marker_layout 1 0 0 E.reverse).mp small
  have shift := extra_suffix_equation [a,b] q [a] (by decide) (by simp [q,mixed]) (by change some a≠some b; decide) rev
  have unit := alternating_tail_of_shift q [a] E.reverse 0 rfl pos shift
  simpa using congrArg List.reverse unit

theorem central_overlap_forms {u v : Word Bool} (m : Model .overlap [a] u v) :
    ∃ G E,u=mixed 0 G 0 ∧ v=mixed 0 E 0 ∧ (E.length+1).Coprime (G.length+1) := by
  obtain ⟨i,G,j,uf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Q) (by decide) rfl)
  obtain ⟨h,E,s,vf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Z) (by decide) rfl)
  change u=mixed i G j at uf
  change v=mixed h E s at vf
  have front : u.head?≠some a := m.first
  have endv : some a≠v.getLast? := m.last
  obtain rfl : i=0 := head_zero (uf ▸ Border.head_b (m.nonempty Q) front)
  have nz : v≠[] := m.nonempty Z
  have back : v.reverse.head?=some b := Border.head_b (by simpa using nz) (by simpa using endv.symm)
  obtain rfl : s=0 := last_zero (vf ▸ (show v.getLast?=some b by simpa using back))
  have cut := m.cuts true
  change ¬NamedCode (pieces (u++[a]) ([a]++v) u) at cut
  have test := Border.cycle_ambiguity cut
  rw [uf,vf,prepend_a,show mixed 0 G j++[a]=mixed 0 G (j+1) from append_pure G 0 j 1] at test
  have margins := normalized_lengthening_margins (i:=0) (g:=G) (j:=j) (h:=h+1) (e:=E) (q:=0)
    test (Or.inl rfl) (Or.inr rfl)
  obtain rfl : j=0 := margins.1
  obtain rfl : h=0 := by omega
  have cop : (v.count b).Coprime (u.count b) :=
    m.marker_coprime (k:=P) (l:=Z) (s:=Q) (by decide) (by decide) (by decide) rfl
  exact ⟨G,E,uf,vf,by simpa only [uf,vf,mixed_count] using cop⟩

private theorem central_overlap_gaps (G E : List ℕ) (cop : (E.length+1).Coprime (G.length+1))
    (small : ¬NamedCode (pieces (mixed 0 G 0++[a]) ([a]++mixed 0 E 0) (mixed 0 E 0)))
    (large : ¬NamedCode (pieces (mixed 0 G 0++[a]) ([a]++mixed 0 E 0) (mixed 0 G 0))) :
    G=List.replicate G.length 1 ∧ E=List.replicate E.length 1 := by
  by_cases empty : G=[]
  · subst G
    exact ⟨rfl,alternating_auxiliary E (swap_last_ambiguity small)⟩
  by_cases emptyE : E=[]
  · subst E
    have reverse := reverse_ambiguity (Border.cycle_ambiguity large)
    have std : ¬NamedCode (pieces [b,a] (mixed 0 G.reverse 0) ([a]++mixed 0 G.reverse 0)) := by
      simpa only [List.reverse_append,reverse_mixed,List.reverse_nil,show mixed 0 [] 0=[b] from rfl,List.reverse_cons,List.cons_append,List.nil_append] using Border.cycle_ambiguity reverse
    have one := alternating_auxiliary G.reverse std
    exact ⟨by simpa using congrArg List.reverse one,rfl⟩
  let u := mixed 0 G 0
  let v := mixed 0 E 0
  have old : ¬NamedCode (pieces [a] u ([a]++v)) := by
    intro h
    apply large
    let g := pieces [a] u ([a]++v)
    let pad : Option Bool → Word (Option Bool) | some false => [Q] | _ => []
    have changeFirst : (fun k => spell g (pad k)++g k)=pieces (u++[a]) u ([a]++v) := by
      funext k; rcases k with _|(_|_) <;> simp [pad,g,pieces,pair,addToken,Q]
    have first := changeFirst ▸ h.pad_left pad
    exact by_contra fun neg => swap_last_ambiguity neg first
  have new := Border.cycle_ambiguity large
  rw [show u=mixed 0 G 0 from rfl,show v=mixed 0 E 0 from rfl,prepend_a] at old
  rw [show mixed 0 G 0++[a]=mixed 0 G 1 from append_pure G 0 0 1,prepend_a] at new
  have pg := List.length_pos_iff.mpr empty
  have pe := List.length_pos_iff.mpr emptyE
  have diff : G.length≠E.length := by intro eqn; rw [←eqn,Nat.coprime_self] at cop; omega
  obtain ⟨c,cap,gu,eu⟩ := uniform_lengthening_bound_unordered (i:=0) (h:=1) (j:=0) (q:=0)
    (Or.inl rfl) (Or.inl rfl) old new pg pe diff cop
  obtain ⟨d,gd,_,_,_,le,_⟩ := uniform_gaps_of_distinct_counts (i:=0) (h:=1) old pg pe diff cop
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil G empty
  have same := (gu x hx).symm.trans (gd x hx)
  have one : c=1 := by omega
  exact ⟨List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (gu x hx).trans one⟩,
    List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (eu x hx).trans one⟩⟩

theorem overlap_central (u v : Word Bool) (m : Model .overlap [a] u v) : False := by
  obtain ⟨G,E,uf,vf,cop⟩ := central_overlap_forms m
  obtain ⟨gu,eu⟩ := central_overlap_gaps G E cop (uf ▸ vf ▸ m.cuts false) (uf ▸ vf ▸ m.cuts true)
  have U : u=Border.body G.length 1 := uf.trans (congrArg (fun l => mixed 0 l 0) gu)
  have V : v=Border.body E.length 1 := vf.trans (congrArg (fun l => mixed 0 l 0) eu)
  have x : u++[a]=wordPow [b,a] (G.length+1) := by rw [U]; exact Border.body_trailing G.length 1
  have y : [a]++v=wordPow [a,b] (E.length+1) := by rw [V]; exact Border.uniform_power 1 E.length
  have z : u++[a]++v=wordPow [b,a] (G.length+1+E.length)++[b] := by
    rw [x,V,head_body_ab,wordPow_add [b,a] (G.length+1) E.length,List.append_assoc]
  have good := m.code
  change NamedCode (pieces (u++[a]) ([a]++v) (u++[a]++v)) at good
  rw [x,y] at good
  rw [x] at z
  rw [z] at good
  exact alternating_ambiguity [b] [a] _ _ _ (by omega) good

end ThreeWordCodes.CrossedCase
