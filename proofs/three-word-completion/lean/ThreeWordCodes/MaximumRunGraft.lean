module

public import ThreeWordCodes.BlockRuns

/-! # Selecting a run of maximum blocks after a different block -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

theorem separated_run (m : ℕ) (F : List ℕ) (r : ℕ) :
    separated m (List.replicate (r+1) F) = blockPattern m F r ++ [m] := by
  induction r with
  | zero => simp [blockPattern]
  | succ r ih =>
    rw [List.replicate_succ,separated_cons,ih]
    simp [blockPattern,wordPow_succ',List.append_assoc]

private theorem end_mem {m : ℕ} {p : List ℕ} (ending : EndsAt m p) : m∈p := by
  obtain ⟨z,rfl⟩ := ending
  simp

private theorem drop_first_block {m : ℕ} {p B tail : List ℕ} (fresh : m∉B) (ending : EndsAt m p)
    (pref : p <+: B++m::tail) :
    ∃ rest, p=(B++[m])++rest ∧ rest <+: tail ∧ (rest=[] ∨ EndsAt m rest) := by
  have start : B++[m] <+: B++m::tail := ⟨tail,by simp⟩
  have inside : B++[m] <+: p := by
    rcases List.prefix_or_prefix_of_prefix start pref with ready | early
    · exact ready
    rcases List.prefix_concat_iff.mp early with full | before
    · rw [full]
    · exact (fresh (before.sublist.subset (end_mem ending))).elim
  obtain ⟨rest,read⟩ := inside
  obtain ⟨q,eqn⟩ := pref
  have sized : rest++q=tail := List.append_cancel_left (as:=B++[m])
    (by simpa only [←read,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using eqn)
  refine ⟨rest,read.symm,⟨q,sized⟩,?_⟩
  obtain ⟨t,ending⟩ := ending
  induction rest using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton rs n _ =>
    have form : ((B++[m])++rs)++[n]=t++[m] := by simpa only [List.append_assoc] using read.trans ending
    have same : n=m := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? form
    exact Or.inr ⟨rs,by rw [same]⟩

private theorem prefixes_in_run (m : ℕ) (F : List ℕ) (r : ℕ) (p : List ℕ) (fresh : m∉F)
    (ending : p=[] ∨ EndsAt m p) (pref : p <+: blockPattern m F r) :
    ∃ j≤r, p=separated m (List.replicate j F) := by
  rcases ending with rfl | ending
  · exact ⟨0,Nat.zero_le _,rfl⟩
  induction r generalizing p with
  | zero =>
    have base : p <+: F := by simpa [blockPattern] using pref
    exact (fresh (base.sublist.subset (end_mem ending))).elim
  | succ r ih =>
    have form : blockPattern m F (r+1)= F++m::blockPattern m F r := by simp [blockPattern,wordPow_succ']
    obtain ⟨rest,eqn,sub,ends⟩ := drop_first_block fresh ending (form ▸ pref)
    rcases ends with rfl | next
    · exact ⟨1,by omega,by simpa using eqn⟩
    obtain ⟨j,le,hj⟩ := ih rest sub next
    exact ⟨j+1,by omega,by simp [List.replicate_succ,eqn,hj]⟩

theorem permitted_prefix {m : ℕ} {D F : List ℕ} {r : ℕ} {p : List ℕ}
    (dFresh : m∉D) (fFresh : m∉F)
    (pref : CutPrefix m p (D++m::blockPattern m F r)) :
    ∃ j≤r,p=separated m (D::List.replicate j F) := by
  obtain ⟨rest,eqn,sub,ends⟩ := drop_first_block dFresh pref.2.2 pref.1
  obtain ⟨j,le,form⟩ := prefixes_in_run m F r rest fFresh ends sub
  exact ⟨j,le,by simp [eqn,form]⟩

/-- Assume that the initial run has r+1 maximum blocks F. All later runs in
past are shorter. After the next different block D the full run appears once
more. These data give the complete selection of leaves. -/
theorem maximum_run_certificate (h m : ℕ) (F D : List ℕ) (r : ℕ)
    (past : List (List ℕ × ℕ)) (later : List ℕ) (pos : 0<h)
    (different : D≠F) (dLong : ∀ x∈D,m<x) (fFresh : m∉F) (nonempty : F≠[])
    (bounded : ∀ p∈past,p.1≠F ∧ p.2<r+1)
    (recognize : RecognizesBlock F ((List.replicate (r+1) F ++ BlockRuns.after F past) ++ [D,F])) :
    let history := List.replicate (r+1) F ++ BlockRuns.after F past
    HasFiniteCertificate ({[a],mixed (m+1) [] h,
      mixed 0 ((separated m history ++ D++m::(blockPattern m F r ++ later)).map (h+·)) 0} :
        Set (Word Bool)) := by
  let history := List.replicate (r+1) F ++ BlockRuns.after F past
  let U := separated m history
  let R := blockPattern m F r
  have hne : history≠[] := by simp [history]
  have dne : m∉D := fun hm => Nat.lt_irrefl _ (dLong m hm)
  have rn : R≠[] := by simp [R,blockPattern,nonempty]
  have ending : EndsAt m U := by
    have decomp := List.dropLast_concat_getLast hne
    change EndsAt m (separated m history)
    conv => arg 2; rw [←decomp,separated_append,separated_singleton]
    exact ⟨_,(List.append_assoc ..).symm⟩
  have starts : R <+: U := by
    change blockPattern m F r <+: separated m (List.replicate (r+1) F ++ BlockRuns.after F past)
    rw [separated_append,separated_run,List.append_assoc]
    exact ⟨_,rfl⟩
  have unique : OccursOnlyInitially R U := by
    apply pattern_starts_at_root m F r history fFresh nonempty
    · intro B hB
      exact recognize B (List.mem_append_left _ hB)
    · exact BlockRuns.initial_run (Nat.succ_pos _) past bounded
  have next (p : List ℕ) (cut : CutPrefix m p (D++m::R)) : OccursOnlyInitially R (U++p) := by
    obtain ⟨j,le,which⟩ := permitted_prefix dne fFresh cut
    let host := history++D::List.replicate j F
    have form : U++p=separated m host := by rw [which,separated_append]
    rw [form]
    apply pattern_starts_at_root m F r host fFresh nonempty
    · intro B hB
      apply recognize B
      rcases List.mem_append.mp hB with old | add
      · exact List.mem_append_left _ old
      rcases List.mem_cons.mp add with rfl | fromF
      · simp
      · obtain rfl := List.eq_of_mem_replicate fromF
        simp
    · have shape : host=List.replicate (r+1) F ++ BlockRuns.after F (past++[(D,j)]) := by
        simp [host,history,List.append_assoc]
      rw [shape]
      apply BlockRuns.initial_run (Nat.succ_pos _)
      intro e he
      rcases List.mem_append.mp he with old | add
      · exact bounded e old
      · obtain rfl := List.mem_singleton.mp add
        exact ⟨different,by simpa using le⟩
  obtain ⟨n,lead,eqn⟩ : ∃ n : ℕ, ∃ lead : List ℕ, D++[m]=n::lead := by
    cases D with
    | nil => exact ⟨m,[],rfl⟩
    | cons n ds => exact ⟨n,ds++[m],rfl⟩
  have startMin : m≤n := by
    have mem : n∈D++[m] := by rw [eqn]; simp
    rcases List.mem_append.mp mem with inD | same
    · exact (dLong n inD).le
    · exact (List.mem_singleton.mp same) ▸ le_rfl
  have eqLook : D++m::R=n::(lead++R) := by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using congrArg (·++R) eqn
  have result := initial_pattern_certificate h m n U lead R later pos startMin rn ending starts unique
    (fun p hp => next p (eqLook ▸ hp))
  change HasFiniteCertificate ({[a],mixed (m+1) [] h,
    mixed 0 (((U++D)++m::(R++later)).map (h+·)) 0} : Set (Word Bool))
  have put : (U++D)++m::(R++later)=U++n::((lead++R)++later) := by
    simpa only [List.append_assoc,List.cons_append] using congrArg (fun v => U++(v++later)) eqLook
  rw [put]
  exact result

end ThreeWordCodes.BinaryGaps
