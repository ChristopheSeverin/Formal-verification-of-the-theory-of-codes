module

public import ThreeWordCodes.UniformGaps

/-! # The terminal-reduction alternative in Lemma 2

A left step removes a nonempty token u from the front of u r. Sets automatically
merge coincidences. A complete left reduction ends at a prefix-free set.
Reversing each input word gives the corresponding right-reduction condition.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

def LeftStep (X Y : Finset (Word Bool)) : Prop :=
  ∃ u r : Word Bool, ∃ keep : Finset (Word Bool), u ∈ keep ∧ u≠[] ∧ r≠[] ∧
    u++r ∉ keep ∧ X=insert (u++r) keep ∧ Y=insert r keep

def LeftEndsInLetters (X : Finset (Word Bool)) : Prop :=
  ∀ Y, Relation.ReflTransGen LeftStep X Y →
    InformationTheory.IsPrefixFree (Y : Set (Word Bool)) → Y = {[a],[b]}

def BothReductionsEndInLetters (X : Finset (Word Bool)) : Prop :=
  LeftEndsInLetters X ∧ LeftEndsInLetters (X.image List.reverse)

private theorem inherited {X Y : Finset (Word Bool)} (h : LeftEndsInLetters X) (step : LeftStep X Y) :
    LeftEndsInLetters Y := fun Z chain => h Z (Relation.ReflTransGen.head step chain)

private def triple (x y z : Word Bool) : Finset (Word Bool) := {x,y,z}

private theorem step_last (x y u r : Word Bool) (inside : u=x ∨ u=y) (nu : u≠[]) (nr : r≠[])
    (nx : u++r≠x) (ny : u++r≠y) : LeftStep (triple x y (u++r)) (triple x y r) := by
  refine ⟨u,r,{x,y},by simpa using inside,nu,nr,by simp [nx,ny],?_,?_⟩ <;>
    ext z <;> simp only [triple,Finset.mem_insert,Finset.mem_singleton] <;> tauto

private theorem swap_triple (x y z : Word Bool) : triple x y z = triple x z y := by
  ext w
  simp only [triple,Finset.mem_insert,Finset.mem_singleton]
  tauto

private theorem trivial_terminal {x y z : Word Bool} (xy : x≠y) (xz : x≠z) (yz : y≠z)
    (p : InformationTheory.IsPrefixFree ((triple x y z : Finset _) : Set (Word Bool)))
    (endAt : LeftEndsInLetters (triple x y z)) : False := by
  have eqn := congrArg Finset.card (endAt _ .refl p)
  simp [triple,xy,xz,yz,a,b] at eqn

private theorem forced_read (v : Bool → Word Bool) (inj : Function.Injective v)
    (nz : ∀ c, v c≠[]) (free : InformationTheory.IsPrefixFree (Set.range v))
    (w : Word Bool) (terminal : LeftEndsInLetters (triple (v false) (v true) w)) :
    ∃ s, w <+: spell v s := by
  classical
  by_contra no
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    have notPrefix (c : Bool) : ¬ w <+: v c := by
      intro p
      exact no ⟨[c],by simpa using p⟩
    have nx (c : Bool) : w≠v c := fun eqn => notPrefix c (eqn ▸ (by simp))
    by_cases can : ∃ c, v c <+: w
    · obtain ⟨c,r,eqn⟩ := can
      have nr : r≠[] := by rintro rfl; exact nx c (by simpa using eqn.symm)
      have next : LeftEndsInLetters (triple (v false) (v true) r) := by
        apply inherited terminal
        rw [←eqn]
        exact step_last _ _ _ _ (by cases c <;> simp) (nz c) nr
          (eqn ▸ nx false) (eqn ▸ nx true)
      have bad : ¬ ∃ s, r <+: spell v s := by
        rintro ⟨s,t,he⟩
        exact no ⟨c::s,t,by simp [←eqn,List.append_assoc,he]⟩
      have length := congrArg List.length eqn
      have pc := List.length_pos_iff.mpr (nz c)
      simp only [List.length_append] at length
      exact ih _ (by omega) r next bad rfl
    · push Not at can
      apply trivial_terminal (fun he => Bool.false_ne_true (inj he)) (Ne.symm (nx false)) (Ne.symm (nx true)) _ terminal
      intro x hx y hy pr
      change x ∈ triple (v false) (v true) w at hx
      change y ∈ triple (v false) (v true) w at hy
      simp only [triple,Finset.mem_insert,Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | rfl | exact free _ ⟨_,rfl⟩ _ ⟨_,rfl⟩ pr | exact (notPrefix _ pr).elim | exact (can _ pr).elim

private theorem mixed_not_a (i : ℕ) (g : List ℕ) (j : ℕ) : mixed i g j ≠ [a] := by
  intro eqn
  have one := congrArg (List.count b) eqn
  simp [mixed_count,a,b] at one

private theorem cut_margin (i : ℕ) (g : List ℕ) (j : ℕ) (w : Word Bool)
    (counts : (g.length+1) ≠ w.count b)
    (term : LeftEndsInLetters (triple [a] w (mixed i g j))) :
    LeftEndsInLetters (triple [a] w (mixed 0 g j)) := by
  induction i with
  | zero => exact term
  | succ i ih =>
    apply ih
    apply inherited term
    have start : [a] ++ mixed i g j = mixed (i+1) g j := rfl
    rw [←start]
    exact step_last _ _ _ _ (Or.inl rfl) (by simp) (by simp [mixed])
      (mixed_not_a (i+1) g j) (fun eqn => counts (by simpa only [start,mixed_count] using congrArg (List.count b) eqn))

private theorem directed_terminal {i g j h e q} (different : g.length ≠ e.length)
    (term : LeftEndsInLetters (triple [a] (mixed i g j) (mixed h e q))) :
    ∃ s, mixed 0 e q <+: spell (stripped g j) s := by
  have y := cut_margin h e q (mixed i g j) (by rw [mixed_count]; omega) term
  rw [swap_triple] at y
  have x := cut_margin i g j (mixed 0 e q) (by rw [mixed_count]; omega) y
  rw [swap_triple] at x
  have initialName (u : Bool) : (stripped g j u).head? = some u := by cases u <;> rfl
  have unique {c d : Bool} (pr : stripped g j c <+: stripped g j d) : c=d := by
    obtain ⟨r,eqn⟩ := pr
    have start (x : Bool) : (stripped g j x ++ r).head? = some x := by cases x <;> rfl
    simpa only [start,initialName,Option.some.injEq] using congrArg List.head? eqn
  apply forced_read (stripped g j) _ _ _ (mixed 0 e q) x
  · intro c d eqn
    exact unique (by rw [eqn])
  · intro c
    cases c <;> simp [stripped,pair,mixed,run]
  · rintro _ ⟨c,rfl⟩ _ ⟨d,rfl⟩ pr
    exact congrArg _ (unique pr)

/-- The alternative hypothesis in Lemma 2 as a statement about all maximal
left and right shortening sequences, with duplicate words merged. -/
theorem uniform_gaps_of_terminal_reductions {i g j h e q}
    (term : BothReductionsEndInLetters ({[a],mixed i g j,mixed h e q} : Finset (Word Bool)))
    (two : 2 ≤ g.length+1) (long : g.length < e.length)
    (cop : (e.length+1).Coprime (g.length+1)) :
    ∃ c : ℕ, (∀ z ∈ g, z=c) ∧ (∀ z ∈ e, z=c) ∧ i≤c ∧ j≤c ∧ h≤c ∧ q≤c := by
  have reverseSet : (triple [a] (mixed i g j) (mixed h e q)).image List.reverse =
      triple [a] (mixed j g.reverse i) (mixed q e.reverse h) := by
    simp [triple,reverse_mixed]
  have backward := directed_terminal (by simpa using long.ne) (reverseSet ▸ term.2)
  exact uniform_gaps_of_readings (directed_terminal long.ne term.1) backward two long cop

theorem terminal_gaps_of_words (u v : Word Bool)
    (term : BothReductionsEndInLetters ({[a],u,v} : Finset (Word Bool)))
    (two : 2≤u.count b) (long : u.count b<v.count b) (cop : (v.count b).Coprime (u.count b)) :
    ∃ i j h q c : ℕ, ∃ g e : List ℕ, u=mixed i g j ∧ v=mixed h e q ∧
      (∀ z ∈ g, z=c) ∧ (∀ z ∈ e, z=c) ∧ i≤c ∧ j≤c ∧ h≤c ∧ q≤c := by
  obtain ⟨i,g,j,rfl⟩ := mixed_of_contains_marker (w:=u) (List.count_pos_iff.mp (by omega))
  obtain ⟨h,e,q,rfl⟩ := mixed_of_contains_marker (w:=v) (List.count_pos_iff.mp (by omega))
  simp only [mixed_count] at two long cop
  obtain ⟨c,all⟩ := uniform_gaps_of_terminal_reductions term two (by omega) cop
  exact ⟨i,j,h,q,c,g,e,rfl,rfl,all⟩

end ThreeWordCodes.BinaryGaps
