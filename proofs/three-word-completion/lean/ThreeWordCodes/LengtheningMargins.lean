module

public import ThreeWordCodes.Bars

/-! # Endpoint restrictions for P, Pa, Q in Lemma 4 -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {I : Type*}

def extended (i : ℕ) (g : List ℕ) (j h : ℕ) (e : List ℕ) (q : ℕ) :=
  addToken (pair (mixed i g j) (mixed i g (j+1))) (mixed h e q)

theorem distinct_starts [Fintype I] (v : I → Word Bool) (n : I → ℕ)
    (shape : ∀ k, ∃ t, v k = run (n k) ++ b :: t) (inj : Function.Injective n) :
    Completable v := by
  have cmp {x y : I} (hp : v x <+: v y) : x=y := by
    obtain ⟨t,ex⟩ := shape x
    obtain ⟨s,ey⟩ := shape y
    rw [ex,ey] at hp
    exact inj (marked_prefix hp).1
  apply completable_prefix
  · intro x y eqn
    exact cmp (by rw [eqn])
  · intro k
    obtain ⟨t,h⟩ := shape k
    simp [h]
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ p
    exact congrArg v (cmp p)

theorem lengthening_end_residue {i g j h e q} (amb : ¬ NamedCode (extended i g j h e q)) :
    q = j ∨ q = j+1 := by
  by_contra! distinct
  let v := extended i g j h e q
  let r (k : Option Bool) := (v k).reverse
  let n : Option Bool → ℕ
    | none => q
    | some false => j
    | some true => j+1
  have diff : Function.Injective n := by
    rintro (_ | (_ | _)) (_ | (_ | _)) eqn <;> simp_all [n,Ne.symm distinct.1,Ne.symm distinct.2]
  have hc := distinct_starts r n (by
    rintro (_ | (_ | _)) <;> simp only [r,v,n,extended,addToken,pair,reverse_mixed] <;> exact ⟨_,rfl⟩) diff
  exact amb (by simpa [r,v] using hc.1.reverse)

private theorem initial_extra (i : ℕ) (g : List ℕ) (j : ℕ) (tail : Word Bool) :
    initial (mixed i g j ++ tail) = i := by
  simp only [mixed,List.append_assoc,List.cons_append,initial_b]

/-- For every nonempty product of P, Pa and Q the initial margin is that of
its first token. -/
private theorem initial_choice {i g j h e q} (k : Option Bool) (s : Word (Option Bool)) :
    initial (spell (extended i g j h e q) (k::s)) = if k.isNone then h else i := by
  cases k with
  | none => apply initial_extra
  | some x => cases x <;> apply initial_extra

private theorem tail_step {i g j h e q} {s t : Word (Option Bool)}
    (he : spell (extended i g j h e q) s = a :: spell (extended i g j h e q) t) :
    i = h+1 ∨ h = i+1 := by
  let v := extended i g j h e q
  have has (k : Option Bool) : b ∈ v k := by
    rcases k with _ | (_ | _) <;> simp [v,extended,addToken,pair,mixed]
  cases s with
  | nil => contradiction
  | cons x s =>
    cases t with
    | nil =>
      have mem : b ∈ spell v (x::s) := List.mem_append_left _ (has x)
      rw [show spell v (x::s) = [a] from he] at mem
      simp [a,b] at mem
    | cons y t =>
      have eqn := congrArg initial he
      change initial (spell v (x::s)) = initial (spell v (y::t)) + 1 at eqn
      simp only [v,initial_choice] at eqn
      cases x <;> cases y <;> simp_all

/-- If the initial margins differ in an ambiguity they differ by precisely one. -/
theorem lengthening_start_gap {i g j h e q} (amb : ¬ NamedCode (extended i g j h e q)) (diff : i ≠ h) :
    i = h+1 ∨ h = i+1 := by
  let v := extended i g j h e q
  have nz (k : Option Bool) : v k ≠ [] := by
    rcases k with _ | (_ | _) <;> simp [v,extended,addToken,pair,mixed]
  change ¬ (∀ ⦃s t⦄, spell v s = spell v t → s=t) at amb
  push Not at amb
  obtain ⟨s,t,eqn,ne⟩ := amb
  obtain ⟨x,y,s,t,ne,eqn⟩ := first_mismatched_names nz s t ne eqn
  have first := congrArg initial eqn
  simp only [v,initial_choice] at first
  have only : (x=some false ∧ y=some true) ∨ (x=some true ∧ y=some false) := by
    rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;> simp_all [Ne.symm diff]
  have plus : mixed i g (j+1) = mixed i g j ++ [a] := (append_pure g i j 1).symm
  have cancel (s t : Word (Option Bool))
      (he : spell v ((some false)::s) = spell v ((some true)::t)) :
      spell v s = a :: spell v t := by
    change mixed i g j ++ spell v s = mixed i g (j+1) ++ spell v t at he
    rw [plus,List.append_assoc] at he
    exact List.append_cancel_left he
  rcases only with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact tail_step (cancel s t eqn)
  · exact tail_step (cancel t s eqn.symm)

/-- The normalized original triple a,P,Q has both letters at each end.
After lengthening, P ends in b and Q has at most one trailing a. -/
theorem normalized_lengthening_margins {i g j h e q}
    (amb : ¬ NamedCode (extended i g j h e q)) (left : i=0 ∨ h=0) (right : j=0 ∨ q=0) :
    j=0 ∧ q≤1 ∧ i≤1 ∧ h≤1 := by
  have endPair := lengthening_end_residue amb
  by_cases same : i=h
  · omega
  · have bound := lengthening_start_gap amb same
    omega

theorem one_marker_lengthening {i j h e q} (amb : ¬ NamedCode (extended i [] j h e q))
    (right : j=0 ∨ q=0) : HasLetterRealization (extended i [] j h e q) := by
  have endPair := lengthening_end_residue amb
  have zero : j=0 := by omega
  subst j
  exact single_marker_lengthening i _ amb

end ThreeWordCodes.BinaryGaps
