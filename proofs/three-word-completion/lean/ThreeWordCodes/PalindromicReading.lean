module

public import ThreeWordCodes.PalindromicSingleGap
public import ThreeWordCodes.GapSelection

/-! # The canonical gaps between consecutive ba tokens

The list ns counts whole x tokens between consecutive ba tokens in the
reading of z x. The corresponding abstract gaps of the manuscript are n+1.
-/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

def Reading (s : ℕ) (ns : List ℕ) (z : Word Bool) : Prop :=
  z ++ x s = spell (pair (x s) c) (mixed 0 ns 0)

theorem Reading.unique {s : ℕ} {ns ms : List ℕ} {z : Word Bool} (r : Reading s ns z)
    (r' : Reading s ms z) : ns=ms := by
  obtain ⟨hi,nz,pf⟩ := reader_prefix s 0
  have base : NamedCode (pair (x s) c) := by
    simpa [readers] using (completable_prefix hi nz pf).1
  exact (mixed_injective (base (r.symm.trans r'))).2.1

private theorem spell_turn (s : ℕ) (p : Word Bool) :
    x s ++ spell (pair (x s) c) p = spell (fun i => ((pair (x s) c) i).reverse) p ++ x s := by
  induction p with
  | nil => simp
  | cons i p ih =>
    have next : x s ++ pair (x s) c i = (pair (x s) c i).reverse ++ x s := by
      cases i with
      | false => simp [pair]
      | true => exact shift s
    simpa only [spell_cons,List.append_assoc] using
      (congrArg (· ++ spell (pair (x s) c) p) next).trans (by
        simp only [List.append_assoc,ih])

theorem Reading.reverse {s : ℕ} {ns : List ℕ} {z : Word Bool} (r : Reading s ns z) :
    Reading s ns.reverse z.reverse := by
  have reversed : x s ++ z.reverse = spell (fun i => ((pair (x s) c) i).reverse) (mixed 0 ns.reverse 0) := by
    rw [spell_reverse,reverse_mixed,List.reverse_reverse]
    simpa using congrArg List.reverse r
  apply List.append_cancel_left (as:=x s)
  change x s ++ (z.reverse ++ x s) = x s ++ spell (pair (x s) c) (mixed 0 ns.reverse 0)
  rw [←List.append_assoc,reversed,spell_turn]

theorem mixed_snoc (ns : List ℕ) (q : ℕ) :
    mixed 0 (ns++[q]) 0 = mixed 0 ns 0 ++ run q ++ [b] := by
  rw [append_pure]
  simpa [mixed,gapTail,run,List.append_assoc] using (join_mixed ns [] 0 q 0 0).symm

/-- Every residual reading has at least one gap, and its last gap is positive. -/
theorem reading_exists {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) :
    ∃ ns : List ℕ, ∃ q : ℕ, Reading s (ns++[q+1]) z := by
  obtain ⟨p,form⟩ := middle_reading code bad
  obtain ⟨i,ns,q,body⟩ := mixed_of_contains_marker (w:=b::p) (by simp)
  have first : i=0 := by
    cases i with
    | zero => rfl
    | succ i => exact Bool.noConfusion (List.cons.inj body).1
  subst i
  have eqn : mixed 0 (ns++[q+1]) 0=(b::p)++[a,b] := by
    rw [mixed_snoc,body,show mixed 0 ns q=mixed 0 ns 0 ++ run q from by simpa using (append_pure ns 0 0 q).symm]
    rw [show run (q+1)=run q++[a] from run_add q 1]
    simp [List.append_assoc]
  refine ⟨ns,q,?_⟩
  change z++x s=spell _ _
  rw [eqn,form,spell_append]
  simp [pair,List.append_assoc,shift]

/-- Reverse the effect of deleting the final x. The last ba token is
invisible and the preceding x contributes its initial ab to z. -/
theorem Reading.last_positive {s q : ℕ} {ns : List ℕ} {z : Word Bool}
    (r : Reading s (ns++[q+1]) z) :
    z=spell (pair (x s) c) (mixed 0 ns 0) ++ wordPow (x s) q ++ c.reverse := by
  apply List.append_cancel_right (bs:=x s)
  change z++x s=_
  change z++x s=spell (pair (x s) c) (mixed 0 (ns++[q+1]) 0) at r
  rw [r,mixed_snoc]
  simp [run,spell_replicate,pair,wordPow_succ (x s) q,List.append_assoc,shift]

theorem Reading.equations {s : ℕ} {ns : List ℕ} {z : Word Bool} (r : Reading s ns z) (k l : ℕ) :
    SameEquations (oneMarker (k+1) (l+1) (mixed 0 (ns.map (1+·)) 0)) (triple s k l z) := by
  apply equations_from_image
  apply mul_right_cancel (b:=groupWord (x s))
  have names : spell (pair [a] [b,a]) (mixed 0 ns 0) = mixed 0 (ns.map (1+·)) 0 ++ [a] := by
    rw [show mixed 0 (ns.map (1+·)) 0 ++ [a]=mixed 0 (ns.map (1+·)) 1 from append_pure _ 0 0 1]
    exact spell_gap_names 1 0 ns
  have both := basis_middle s (mixed 0 ns 0)
  rw [names,groupWord_append,map_mul,show basis s (groupWord [a])=groupWord (x s) from basis_a s,←r,groupWord_append] at both
  exact both

/-- A positive terminal gap makes every earlier marker visible in the
forward reading. Hence every earlier gap fits the right exponent. -/
theorem before_last_bound {s k l q : ℕ} {pre : List ℕ} {z : Word Bool} (r : Reading s (pre++[q+1]) z)
    (code : NamedCode (triple s k l z)) (bad : ¬Completable (triple s k l z)) : ∀ n∈pre,l≤n := by
  obtain ⟨⟨p,read⟩,_,_,_⟩ := two_proper_readings code bad
  let v := pair (x s) c
  have complete : spell v (mixed 0 pre 0) <+: z := by
    rw [r.last_positive]; exact ⟨_,(List.append_assoc ..).symm⟩
  have eqn : spell v (spell (tokens l) p) = spell (readers s l) p := by
    rw [←spell_substitution]
    have changeBasis : (fun i => spell v (tokens l i))=readers s l := by
      funext i; cases i <;> simp [tokens,readers,pair,v,run,spell_replicate]
    rw [changeBasis]
  obtain ⟨hi,nz,pf⟩ := reader_prefix s 0
  have facts : Function.Injective v ∧ (∀ i,v i≠[]) ∧ InformationTheory.IsPrefixFree (Set.range v) := by
    simpa [v,readers] using And.intro hi (And.intro nz pf)
  have sub : mixed 0 pre 0 <+: spell (tokens l) p := by
    apply prefix_reflection facts.1 facts.2.1 facts.2.2
    rw [eqn]
    exact complete.trans read
  exact (gaps_spec l 0 pre 0).mp (spaced_of_prefix_product l p sub)

end ThreeWordCodes.Palindromic
