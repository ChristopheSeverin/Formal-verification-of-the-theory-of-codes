module

public import ThreeWordCodes.GapCoordinates
public import ThreeWordCodes.Residues

/-! # Lengthening the letter in a normalized ambiguous triple

The two singleton-marker cases and the coprime multiple-marker case yield a
letter model in every normalized configuration that can arise.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def bars (n : ℕ) := wordPow [b,a] n
private theorem alt_words (n : ℕ) :
    mixed 0 (List.replicate n 1) 0 = bars n ++ [b] ∧
    mixed 0 (List.replicate n 1) 1 = bars (n+1) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have cons (q : ℕ) : mixed 0 (List.replicate (n+1) 1) q =
        [b,a] ++ mixed 0 (List.replicate n 1) q := by
      simp [mixed,gapTail,run,List.replicate_succ]
    obtain ⟨u,v⟩ := ih
    simp only [cons,u,v,bars,wordPow_succ' [b,a] n,wordPow_succ' [b,a] (n+1),List.append_assoc,true_and]

private theorem residues_differ {m n : ℕ} (pn : 0<n) (cop : (m+1).Coprime (n+1)) :
    n%(n+1) ≠ m%(n+1) := by
  intro eqn
  have divisible : n+1 ∣ m+1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [Nat.add_mod,←eqn,←Nat.add_mod,Nat.mod_self]
  have one : n+1=1 := (Nat.gcd_eq_right divisible).symm.trans cop.gcd_eq_one
  omega

private def perm : Option Bool → Option Bool
  | some false => some false
  | some true => none
  | none => some true

private theorem common_start_code (n m : ℕ) (pn : 0<n) (cop : (m+1).Coprime (n+1)) :
    NamedCode (extended 0 (List.replicate n 1) 0 0 (List.replicate m 1) 0) := by
  let tail (x : Bool) := if x then m else n
  have inj : Function.Injective (fun c => tail c%(n+1)) := by
    have ne := residues_differ pn cop
    intro c d eqn
    cases c <;> cases d <;> simp_all [tail]
  let v := residueWords (n+1) (fun _ : Bool => []) tail
  have base : NamedCode v := (residue_completion (n+1) (by omega) _ _ inj).1
  let abstract (k : Option Bool) := (v (perm k)).reverse
  have code : NamedCode abstract := base.reverse.reindex (show Function.Injective perm by decide)
  let alphabet := pair [b,a] [b]
  have cd : NamedCode alphabet := (noncommuting_pair_completion _ _ (by decide : [b,a]++[b] ≠ [b]++[b,a])).1
  have power (t : ℕ) : spell alphabet (run t) = bars t :=
    spell_replicate alphabet a t
  have actual : (fun k => spell alphabet (abstract k)) =
      extended 0 (List.replicate n 1) 0 0 (List.replicate m 1) 0 := by
    have p (t : ℕ) : spell alphabet (run t ++ [b]) = bars t ++ [b] := by
      rw [spell_append,power]; rfl
    funext k
    rcases k with _ | (_ | _)
    · change spell alphabet (b :: run m).reverse = _
      rw [show (b :: run m).reverse = run m ++ [b] by simp [run],p]
      exact (alt_words m).1.symm
    · change spell alphabet (b :: run n).reverse = _
      rw [show (b :: run n).reverse = run n ++ [b] by simp [run],p]
      exact (alt_words n).1.symm
    · change spell alphabet (run (n+1)).reverse = _
      rw [show (run (n+1)).reverse = run (n+1) by simp [run],power]
      exact (alt_words n).2.symm
  exact actual ▸ cd.substitution code

theorem marker_power (n : ℕ) : mixed 0 (List.replicate n 0) 0 = wordPow [b] (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change b :: mixed 0 (List.replicate n 0) 0 = _
    rw [ih,wordPow_succ' [b] (n+1)]
    rfl

/-- This is the whole P, Pa, Q step for a normalized mixed pair. The marker
counts are taken in their actual order. Only the two possible commuting pairs
that would contradict pairwise noncommutation of the output are required. -/
theorem normalized_binary_lengthening {i g j h e q}
    (old : ¬ NamedCode (layout i g j h e q)) (new : ¬ NamedCode (extended i g j h e q))
    (left : i=0 ∨ h=0) (right : j=0 ∨ q=0) (cop : (e.length+1).Coprime (g.length+1))
    (pq : mixed i g j ++ mixed h e q ≠ mixed h e q ++ mixed i g j)
    (paq : mixed i g (j+1) ++ mixed h e q ≠ mixed h e q ++ mixed i g (j+1)) :
    HasLetterRealization (extended i g j h e q) := by
  by_cases ge : g=[]
  · subst g
    exact one_marker_lengthening new right
  by_cases ee : e=[]
  · subst e
    exact singleton_third_lengthening old new left right
  have pg := List.length_pos_iff.mpr ge
  have pe := List.length_pos_iff.mpr ee
  have ne : g.length ≠ e.length := by
    intro eqn
    rw [eqn,Nat.coprime_self] at cop
    omega
  obtain ⟨rfl,bq,bi,bh⟩ := normalized_lengthening_margins new left right
  obtain ⟨c,bound,gu,eu⟩ := uniform_lengthening_bound_unordered left right old new pg pe ne cop
  have eg : g = List.replicate g.length c := List.eq_replicate_iff.mpr ⟨rfl,gu⟩
  have ee : e = List.replicate e.length c := List.eq_replicate_iff.mpr ⟨rfl,eu⟩
  have unit : c=1 := by
    by_contra no
    have zero : c=0 := by omega
    obtain ⟨c',all,_,i',_,h',q'⟩ := uniform_gaps_of_distinct_counts old pg pe ne cop
    obtain ⟨head,mem⟩ := List.exists_mem_of_ne_nil g ge
    have zero' : c'=0 := (all head mem).symm.trans ((gu head mem).trans zero)
    have iz : i=0 := by omega
    have hz : h=0 := by omega
    have qz : q=0 := by omega
    apply pq
    rw [eg,ee,zero,iz,hz,qz,marker_power,marker_power]
    exact wordPow_comm ..
  subst c
  by_cases same : i=h
  · have hz : h=0 := by omega
    have iz : i=0 := by omega
    subst i h
    rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
    · exfalso
      exact new (by simpa only [←eg,←ee] using common_start_code g.length e.length pg cop)
    · exfalso
      apply paq
      rw [eg,ee,(alt_words _).2,(alt_words _).2]
      exact wordPow_comm ..
  · have ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0) := by omega
    simpa only [←eg,←ee] using alternating_lengthening g.length e.length ends bq

end ThreeWordCodes.BinaryGaps
