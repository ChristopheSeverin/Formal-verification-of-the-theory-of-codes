module

public import ThreeWordCodes.CrossedDisjoint
public import ThreeWordCodes.Crossed

/-! # Complete exclusion of the disjoint row (III) -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem swap_last_ambiguity {A : Type*} {u v w : Word A} (bad : ¬NamedCode (pieces u v w)) :
    ¬NamedCode (pieces u w v) := by
  let perm : Option Bool → Option Bool
    | none => Q
    | some false => P
    | some true => Z
  have e : (fun k => pieces u w v (perm k))=pieces u v w := by funext k; rcases k with _|(_|_) <;> rfl
  exact fun h => bad (e ▸ h.reindex (f:=perm) (by decide))

theorem initial_zero {i g j h e q} (diff : (mixed i g j).head?≠(mixed h e q).head?) : i=0 ∨ h=0 := by
  cases i <;> cases h <;> simp_all [mixed,run,List.replicate_succ]

theorem final_zero {i g j h e q} (diff : (mixed i g j).getLast?≠(mixed h e q).getLast?) : j=0 ∨ q=0 :=
  initial_zero (g:=g.reverse) (e:=e.reverse) (j:=i) (q:=h) (by simpa only [←reverse_mixed,List.head?_reverse] using diff)

private theorem test {u v : Word Bool} (m : Model .disjoint [a] u v)
    {i g j h e q} (uf : u=mixed i g j) (vf : v=mixed h e q) : ¬NamedCode (extended i g j h e q) := by
  have bad := m.cuts true
  change ¬NamedCode (pieces u v (u++[a])) at bad
  have cmp := swap_last_ambiguity bad
  rw [uf,vf,show mixed i g j++[a]=mixed i g (j+1) from append_pure g i j 1] at cmp
  exact cmp

private theorem disjoint_margins {u v : Word Bool} (m : Model .disjoint [a] u v)
    {i g j h e q} (uf : u=mixed i g j) (vf : v=mixed h e q) : j=0 ∧ q=1 := by
  have front := m.first
  have back := m.last
  change u.head?≠v.head? at front
  change u.getLast?≠v.getLast? at back
  rw [uf,vf] at front back
  obtain ⟨j0,q1,_,_⟩ := normalized_lengthening_margins (test m uf vf) (initial_zero front) (final_zero back)
  refine ⟨j0,?_⟩
  subst j
  rcases q with _|q
  · apply False.elim
    apply back
    simp only [←List.head?_reverse,reverse_mixed]; rfl
  · omega

private theorem central_uniform {g e : List ℕ} (cop : (e.length+1).Coprime (g.length+1))
    (old : ¬NamedCode (layout 1 g 0 0 e 1)) (new : ¬NamedCode (extended 1 g 0 0 e 1))
    (oldRev : ¬NamedCode (layout 1 e.reverse 0 0 g.reverse 1))
    (newRev : ¬NamedCode (extended 1 e.reverse 0 0 g.reverse 1)) :
    g=List.replicate g.length 1 ∧ e=List.replicate e.length 1 := by
  by_cases empty : e=[]
  · subst e
    exact ⟨(singleton_third_details old new (Or.inr rfl) (Or.inl rfl)).2 (by decide) (by decide) (by decide),rfl⟩
  by_cases small : g=[]
  · subst g
    have re := (singleton_third_details (g:=e.reverse) oldRev newRev (Or.inr rfl) (Or.inl rfl)).2
      (by decide) (by decide) (by decide)
    exact ⟨rfl,by simpa using congrArg List.reverse re⟩
  have pg := List.length_pos_iff.mpr small
  have pe := List.length_pos_iff.mpr empty
  have ne : g.length≠e.length := by intro eqn; rw [←eqn,Nat.coprime_self] at cop; omega
  obtain ⟨c,cap,gu,eu⟩ := uniform_lengthening_bound_unordered (Or.inr rfl) (Or.inl rfl) old new pg pe ne cop
  obtain ⟨d,gd,_,le,_⟩ := uniform_gaps_of_distinct_counts old pg pe ne cop
  obtain ⟨s,mem⟩ := List.exists_mem_of_ne_nil g small
  have same := (gu s mem).symm.trans (gd s mem)
  have one : c=1 := by omega
  exact ⟨List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (gu x hx).trans one⟩,
    List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (eu x hx).trans one⟩⟩

theorem disjoint_central (u v : Word Bool) (m : Model .disjoint [a] u v) : False := by
  obtain ⟨i,g,j,uf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Q) (by decide) rfl)
  obtain ⟨h,e,q,vf⟩ := mixed_of_contains_marker (m.has_marker (k:=P) (l:=Z) (by decide) rfl)
  change u=mixed i g j at uf
  change v=mixed h e q at vf
  have rev : Model .disjoint [a] v.reverse u.reverse := m.reverse (by decide)
  have ru : u.reverse=mixed j g.reverse i := by rw [uf,reverse_mixed]
  have rv : v.reverse=mixed q e.reverse h := by rw [vf,reverse_mixed]
  obtain ⟨rfl,rfl⟩ := disjoint_margins m uf vf
  obtain ⟨rfl,rfl⟩ := disjoint_margins rev rv ru
  have cop := m.marker_coprime (k:=P) (l:=Z) (s:=Q) (by decide) (by decide) (by decide) rfl
  change (v.count b).Coprime (u.count b) at cop
  rw [vf,uf,mixed_count,mixed_count] at cop
  have old := m.ambiguous
  change ¬NamedCode (pieces [a] u v) at old
  rw [uf,vf] at old
  have back := rev.ambiguous
  change ¬NamedCode (pieces [a] v.reverse u.reverse) at back
  rw [rv,ru] at back
  obtain ⟨gu,ev⟩ := central_uniform cop old (test m uf vf) back (test rev rv ru)
  have U : u=wordPow [a,b] (g.length+1) :=
    uf.trans ((congrArg (fun G => mixed 1 G 0) gu).trans (Border.uniform_power 1 g.length))
  have V : v=wordPow [b,a] (e.length+1) := by
    calc v = mixed 0 (List.replicate e.length 1) 1 := vf.trans (congrArg (fun E => mixed 0 E 1) ev)
         _ = _ := (append_pure (List.replicate e.length 1) 0 0 1).symm.trans (Border.body_trailing e.length 1)
  have W : u++[a]++v=wordPow [a,b] ((g.length+1)+(e.length+1))++[a] := by
    have rotate : [a]++wordPow [b,a] (e.length+1)=wordPow [a,b] (e.length+1)++[a] := (rotate_power [a] [b] _).symm
    rw [U,V,List.append_assoc,rotate,wordPow_add [a,b] (g.length+1) (e.length+1),List.append_assoc]
  have good := m.code
  change NamedCode (pieces u v (u++[a]++v)) at good
  rw [W,U,V] at good
  exact alternating_ambiguity [a] [b] _ _ _ (by omega) good

/-- Row III is impossible for each position of the model letter. -/
theorem disjoint_impossible (t u v : Word Bool) : ¬Model .disjoint t u v := by
  intro m
  obtain ⟨k,single⟩ := m.letter
  rcases k with _|(_|_)
  · change v=[a] at single
    exact disjoint_right t u (single ▸ m)
  · change t=[a] at single
    exact disjoint_central u v (single ▸ m)
  · change u=[a] at single
    exact disjoint_left t v (single ▸ m)

/-- Row III and the central-letter cases of I and II are already excluded. -/
theorem three_crossed_rows_suffice.{u}
    (rowI : ∀ t u v,t≠[a] → ¬Model .sharedShort t u v)
    (rowII : ∀ t u v,t≠[a] → ¬Model .intermediate t u v)
    (rowIV : ∀ t u v,¬Model .overlap t u v) : ThreeWordTheorem.{u} := by
  apply crossed_models_suffice
  intro r t u v m
  cases r with
  | sharedShort =>
    by_cases literal : t=[a]
    · exact shared_central u v (literal ▸ m)
    · exact rowI t u v literal m
  | intermediate =>
    by_cases literal : t=[a]
    · exact intermediate_central u v (literal ▸ m)
    · exact rowII t u v literal m
  | disjoint => exact disjoint_impossible t u v m
  | overlap => exact rowIV t u v m

end ThreeWordCodes.CrossedCase
