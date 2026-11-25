module

public import ThreeWordCodes.AlternatingCoordinates
public import ThreeWordCodes.MarkerPositions
public import ThreeWordCodes.OneMarker
public import ThreeWordCodes.Alphabet

/-! # Signed coordinates with a nonuniform list of gaps, and the singleton Q case -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private abbrev x : FreeGroup Bool := GroupCoordinates.a
private abbrev y : FreeGroup Bool := GroupCoordinates.b

private def expr (i : ℤ) (g : List ℤ) (q : ℤ) : FreeGroup Bool :=
  match g with
  | [] => x^i*y*x^q
  | c::s => x^i*y*expr c s q

private theorem shift (k i q : ℤ) (s : List ℤ) : x^k * expr i s q = expr (k+i) s q := by
  cases s <;> simp only [expr,zpow_add,mul_assoc]

private theorem as_expr (i : ℕ) (g : List ℕ) (q : ℕ) :
    groupWord (mixed i g q) = expr i (g.map Nat.cast) q := by
  induction g generalizing i with
  | nil =>
    change groupWord (run i ++ ([b] ++ run q)) = _
    rw [groupWord_append,groupWord_append,groupWord_run,groupWord_run,groupWord_singleton]
    simp [expr,mul_assoc,x,y,GroupCoordinates.b,b]
  | cons c s ih =>
    have eqn : mixed i (c::s) q = (run i ++ [b]) ++ mixed c s q := by
      simp [mixed,gapTail,List.append_assoc]
    rw [eqn,groupWord_append,groupWord_append,groupWord_run,groupWord_singleton,ih]
    simp [expr,y,GroupCoordinates.b,b]

private theorem transform (l r i q : ℤ) (g : List ℤ) :
    GroupCoordinates.change l r (expr i g q) = expr (l-i) (g.map (l+r-·)) (r-q) := by
  induction g generalizing i with
  | nil =>
    simp only [expr,List.map_nil,map_mul,map_zpow,GroupCoordinates.change_a,GroupCoordinates.change_b,
      inv_zpow,←zpow_neg,x,y]
    group
  | cons c s ih =>
    simp only [List.map_cons,expr,map_mul,map_zpow,GroupCoordinates.change_a,GroupCoordinates.change_b,
      ih,inv_zpow,←zpow_neg]
    change x^(-i) * (x^l*y*x^r) * expr (l-c) _ _ = x^(l-i)*y*expr (l+r-c) _ _
    rw [show x^(-i)*(x^l*y*x^r)=(x^(l-i)*y)*x^r by group,mul_assoc,shift]
    congr 2
    omega

/-- The transformation sends each gap g to l+r-g, with independent changes
l-i and r-q at the ends. Its positive form applies when these differences exist. -/
theorem gap_coordinate_change (l r i : ℕ) (g : List ℕ) (q : ℕ)
    (hi : i≤l) (hq : q≤r) (hg : ∀ t∈g, t≤l+r) :
    GroupCoordinates.change l r (groupWord (mixed i g q)) =
      groupWord (mixed (l-i) (g.map (l+r-·)) (r-q)) := by
  rw [as_expr,as_expr,transform]
  simp only [Nat.cast_sub hi,Nat.cast_sub hq,List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  simp [Nat.cast_sub (hg z hz)]

/-- If Q has a single marker, the normalized lengthening P,Pa,Q admits a
positive letter model preserving every equation. This includes arbitrary
nonuniform gaps in P before the structural constraints are applied. -/
theorem singleton_third_details {i g j h q}
    (old : ¬ NamedCode (layout i g j h [] q)) (new : ¬ NamedCode (extended i g j h [] q))
    (left : i=0 ∨ h=0) (right : j=0 ∨ q=0) :
    HasLetterRealization (extended i g j h [] q) ∧
      (i≠h → ¬(h=0 ∧ q=0) → ¬(h=1 ∧ q=1) → g=List.replicate g.length 1) := by
  obtain ⟨rfl,bq,bi,bh⟩ := normalized_lengthening_margins new left right
  let f := extended i g 0 h [] q
  by_cases same : i=h
  · have iz : i=0 := by omega
    have hz : h=0 := by omega
    subst i h
    exact ⟨single_bar_lengthening g 0 q,fun diff => (diff rfl).elim⟩
  by_cases literal : h=0 ∧ q=0
  · obtain ⟨rfl,rfl⟩ := literal
    exact ⟨⟨f,fun _ _ => Iff.rfl,none,b,rfl⟩,fun _ diff => (diff ⟨rfl,rfl⟩).elim⟩
  have ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0) := by omega
  have upper (z : ℕ) (mem : z∈g) : z≤2 := by
    by_contra! large
    exact new (large_gap_locates_bodies i g h q 2 (by omega) ⟨_,mem,large⟩)
  let S := g.map (2-·)
  let T := mixed (1-i) S 0
  let V := mixed (1-h) [] (1-q)
  let d := addToken (pair (T++[a]) T) V
  let F := GroupCoordinates.change 1 1
  have im (l : ℕ) (ls : List ℕ) (r : ℕ) (hl : l≤1) (hr : r≤1) (good : ∀ z∈ls, z≤2) :
      F (groupWord (mixed l ls r)) = groupWord (mixed (1-l) (ls.map (2-·)) (1-r)) :=
    gap_coordinate_change 1 1 l ls r hl hr good
  have P : mixed (1-i) S 1 = T ++ [a] := (append_pure S (1-i) 0 1).symm
  have eqns : SameEquations f d := by
    apply sameEquations_of_group_change F (GroupCoordinates.change_involutive 1 1).injective
    rintro (_ | (_ | _))
    · exact im h [] q bh bq (by simp)
    · exact (im i g 0 bi (by omega) upper).trans (congrArg groupWord P)
    · exact im i g 1 bi le_rfl upper
  by_cases full : h=1 ∧ q=1
  · obtain ⟨rfl,rfl⟩ := full
    exact ⟨⟨d,eqns,none,b,rfl⟩,fun _ _ diff => (diff ⟨rfl,rfl⟩).elim⟩
  have bad : ¬ NamedCode (layout (1-i) S 0 (1-h) [] (1-q)) := by
    intro good
    apply new
    apply eqns.namedCode_iff.mpr
    let core := layout (1-i) S 0 (1-h) [] (1-q)
    let pad (k : Option Bool) : Word (Option Bool) := if k=some false then [some true] else []
    have recover : (fun k => spell core (pad k) ++ core k) = d := by
      funext k
      rcases k with _ | (_ | _) <;> simp [core,pad,d,layout,addToken,pair,V,T]
    exact recover ▸ good.pad_left pad
  have oldSpace := one_marker_gaps (fun hc => swapped_ambiguity old hc.1)
  have newSpace := one_marker_gaps (fun hc => swapped_ambiguity bad hc.1)
  have uniform : g = List.replicate g.length 1 := by
    apply List.eq_replicate_iff.mpr ⟨rfl,?_⟩
    intro z hz
    have lo := oldSpace z hz
    have hi := newSpace (2-z) (List.mem_map.mpr ⟨z,hz,rfl⟩)
    omega
  refine ⟨?_,fun _ _ _ => uniform⟩
  rw [uniform]
  exact alternating_lengthening g.length 0 ends bq

theorem singleton_third_lengthening {i g j h q}
    (old : ¬NamedCode (layout i g j h [] q)) (new : ¬NamedCode (extended i g j h [] q))
    (left : i=0 ∨ h=0) (right : j=0 ∨ q=0) : HasLetterRealization (extended i g j h [] q) :=
  (singleton_third_details old new left right).1

end ThreeWordCodes.BinaryGaps
