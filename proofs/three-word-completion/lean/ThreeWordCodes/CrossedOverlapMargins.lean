module

public import ThreeWordCodes.CrossedOverlapCentral

/-! # The margins and alternating identities in the overlapping row -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem overlap_margins (G E : List ℕ) (r s q : ℕ) (diff : (mixed 0 G r).getLast?≠(mixed s E q).getLast?)
    (amb : ¬NamedCode (pieces ([a]++mixed 0 G r) (mixed 0 G r++mixed s E q) (mixed s E q))) :
    ((r=0 ∧ q=1) ∨ (r=1 ∧ q=0)) ∧ s≤1 := by
  let p := mixed r G.reverse 0
  let v := mixed q E.reverse s
  have initial : p.head?≠v.head? := by simpa only [p,v,←reverse_mixed,List.head?_reverse] using diff
  let g := pieces (p++[a]) v (v++p)
  have fail : ¬NamedCode g := by
    simpa [g,p,v,reverse_mixed] using swap_last_ambiguity (reverse_ambiguity amb)
  have np : p≠[] := by simp [p,mixed]
  have nv : v≠[] := by simp [v,mixed]
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,pieces,pair,addToken,np,nv]
  have only (k : Option Bool) (e : (g k).head?=(g P).head?) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,pieces,addToken,pair,P,Border.append_head_of_nonempty np,Border.append_head_of_nonempty nv]
  obtain ⟨l,t,eqn⟩ := extra_suffix_equation (p++[a]) v p (by simp) nv
    (by rwa [Border.append_head_of_nonempty np]) fail
  obtain ⟨tail,rfl⟩ := forced_head (g:=g) (w:=p++spell g t) nz P only l (by simp [np])
    (by change (p++_).head?=(p++[a]).head?; simp only [Border.append_head_of_nonempty np]) eqn
  change (p++[a])++spell g tail=p++spell g t at eqn
  rw [List.append_assoc] at eqn
  have step := (List.append_cancel_left eqn).symm
  have close := margin_shift (g:=g) r q (by
    rintro (_|(_|_))
    · exact ⟨q,_,0,Or.inr rfl,join_mixed E.reverse G.reverse q s r 0⟩
    · exact ⟨r,G.reverse,1,Or.inl rfl,append_pure G.reverse r 0 1⟩
    · exact ⟨q,E.reverse,s,Or.inr rfl,rfl⟩) t tail step
  have zero := final_zero diff
  refine ⟨by omega,?_⟩
  by_contra! large
  let f := pieces ([a]++mixed 0 G r) (mixed 0 G r++mixed s E q) (mixed s E q)
  let lens : Option Bool → ℕ | none => s | some false => 1 | some true => 0
  have hi : Function.Injective lens := by
    rintro (_|(_|_)) (_|(_|_)) e <;> simp_all [lens]
    omega
  apply amb (BinaryGaps.distinct_starts f lens ?_ hi).1
  rintro (_|(_|_))
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

theorem lateral_overlap_forms {t v : Word Bool} (m : Model .overlap t [a] v) :
    ∃ G E r s q,t=mixed 0 G r ∧ v=mixed s E q ∧ ((r=0 ∧ q=1) ∨ (r=1 ∧ q=0)) ∧
      s≤1 ∧ (E.length+1).Coprime (G.length+1) := by
  obtain ⟨i,G,r,tf⟩ := mixed_of_contains_marker (m.has_marker (k:=Q) (l:=P) (by decide) rfl)
  obtain ⟨s,E,q,vf⟩ := mixed_of_contains_marker (m.has_marker (k:=Q) (l:=Z) (by decide) rfl)
  change t=mixed i G r at tf
  change v=mixed s E q at vf
  have ft : some a≠t.head? := m.first
  obtain rfl : i=0 := head_zero (tf ▸ Border.head_b (m.nonempty P) ft.symm)
  have last : t.getLast?≠v.getLast? := m.last
  have cut := m.cuts false
  change ¬NamedCode (pieces ([a]++t) (t++v) v) at cut
  rw [tf,vf] at last cut
  obtain ⟨ends,bound⟩ := overlap_margins G E r s q last cut
  have cop : (v.count b).Coprime (t.count b) :=
    m.marker_coprime (k:=Q) (l:=Z) (s:=P) (by decide) (by decide) (by decide) rfl
  exact ⟨G,E,r,s,q,tf,vf,ends,bound,by simpa only [tf,vf,mixed_count] using cop⟩

/-- For unit gaps the initial a either completes an alternating power or
moves across the whole product by the rotation identity. -/
theorem overlap_unit (m n r q : ℕ) (ends : (r=0 ∧ q=1) ∨ (r=1 ∧ q=0)) :
    let t := mixed 0 (List.replicate m 1) r
    let y := mixed 0 (List.replicate n 1) q
    ¬NamedCode (pieces ([a]++t) y ([a]++y)) := by
  intro t y
  rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have x : [a]++t=wordPow [a,b] (m+1) := Border.uniform_power 1 m
    have Y : y=wordPow [b,a] (n+1) := (append_pure _ 0 0 1).symm.trans (Border.body_trailing n 1)
    have rot : [a]++wordPow [b,a] (n+1)=wordPow [a,b] (n+1)++[a] := (rotate_power [a] [b] _).symm
    rw [x,Y,rot]
    exact alternating_ambiguity [a] [b] (m+1) (n+1) (n+1) (by omega)
  · let f := pieces ([a]++t) y ([a]++y)
    have X : [a]++t=wordPow [a,b] (m+1)++[a] := by
      change [a]++mixed 0 (List.replicate m 1) 1=_
      rw [←append_pure (List.replicate m 1) 0 0 1,←List.append_assoc]; exact congrArg (·++[a]) (Border.uniform_power 1 m)
    have W : [a]++y=wordPow [a,b] (n+1) := Border.uniform_power 1 n
    have XY : ([a]++t)++y=wordPow [a,b] ((m+1)+(n+1)) := by
      rw [X,List.append_assoc,W,wordPow_add [a,b] (m+1) (n+1)]
    intro code
    have eqn : spell f [P,Q,Z]=spell f [Z,P,Q] := by
      change ([a]++t)++(y++(([a]++y)++[]))=([a]++y)++(([a]++t)++(y++[]))
      rw [List.append_nil,List.append_nil,←List.append_assoc,XY,W]
      exact wordPow_comm ..
    exact (by decide : P≠Z) (List.cons.inj (code eqn)).1

end ThreeWordCodes.CrossedCase
