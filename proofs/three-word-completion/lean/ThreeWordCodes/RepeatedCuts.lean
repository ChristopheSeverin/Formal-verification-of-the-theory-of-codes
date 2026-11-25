module

public import ThreeWordCodes.LongBlocks

/-! # Repeated blocks separated by a new gap value -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def EndsShort (d : ℕ) (xs : List ℕ) : Prop := ∃ pre z, xs=pre++[z] ∧ z≤d

private noncomputable def repeats (d m : ℕ) (P : List ℕ) : List (List ℕ) := by
  classical
  let short := P.inits.filter fun q => q.length < P.length ∧ (q=[] ∨ EndsShort d q)
  exact P :: short.map (fun q => P++m::q)

private theorem mem_repeats {d m : ℕ} {P w : List ℕ} :
    w∈repeats d m P ↔ w=P ∨ ∃ q, q <+: P ∧ q.length<P.length ∧ (q=[] ∨ EndsShort d q) ∧ P++m::q=w := by
  classical
  simp [repeats,List.mem_inits,and_assoc]

private theorem keep_ending {d : ℕ} {pre post : List ℕ} (ending : EndsShort d (pre++post)) :
    post=[] ∨ EndsShort d post := by
  induction post using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton init t _ =>
    obtain ⟨front,z,eqn,le⟩ := ending
    have e : (pre++init)++[t]=front++[z] := by simpa using eqn
    have same : t=z := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? e
    exact Or.inr ⟨init,t,rfl,same ▸ le⟩

private theorem repeat_ending {d m : ℕ} {P w : List ℕ} (pos : m≤d)
    (short : EndsShort d P) (mem : w∈repeats d m P) : EndsShort d w := by
  rcases mem_repeats.mp mem with rfl | ⟨q,_,_,qEnd,rfl⟩
  · exact short
  · rcases qEnd with rfl | ⟨pre,z,rfl,le⟩
    · exact ⟨P,m,rfl,pos⟩
    · exact ⟨P++m::pre,z,by simp,le⟩

private theorem initial_only {d m : ℕ} {P w pre tail : List ℕ} (fresh : m∉P)
    (mem : w∈repeats d m P) (occurs : w=pre++(P++tail)) : pre=[] := by
  rcases mem_repeats.mp mem with rfl | ⟨q,_,short,_,rfl⟩
  · have lens := congrArg List.length occurs
    simp only [List.length_append] at lens
    exact List.length_eq_zero_iff.mp (by omega)
  · by_contra nonempty
    have positive := List.length_pos_iff.mpr nonempty
    have lens := congrArg List.length occurs
    simp only [List.length_append,List.length_cons] at lens
    have index := congrArg (fun v : List ℕ => v[P.length]?) occurs
    rw [List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero] at index
    rw [List.getElem?_append_right (show pre.length ≤ P.length by omega),
      List.getElem?_append_left (show P.length-pre.length < P.length by omega)] at index
    exact fresh (List.mem_of_getElem? index.symm)

private theorem repeat_aligned {d m : ℕ} {P p q : List ℕ} (fresh : m∉P)
    (hp : p∈repeats d m P) (hq : q∈repeats d m P) (pr : p <:+ q) : p=q := by
  obtain ⟨pre,eqn⟩ := pr
  have starts : P <+: p := by
    rcases mem_repeats.mp hp with rfl | ⟨s,_,_,_,rfl⟩
    · rfl
    · exact ⟨_,rfl⟩
  obtain ⟨s,e⟩ := starts
  have empty := initial_only fresh hq (by simpa only [e] using eqn.symm : q=pre++(P++s))
  simpa only [empty,List.nil_append] using eqn

/-- If P ends short and does not contain the separator m, an initial reading
P, m, P admits a graft. The later gaps can be arbitrary. Only proper
prefixes of the second P ending short need to be selected. -/
theorem repeated_block_certificate (h d m : ℕ) (P later : List ℕ) (pos : 0<h) (sep : m≤d)
    (fresh : m∉P) (ending : ∃ pre z, P=pre++[z] ∧ z≤d) :
    HasFiniteCertificate ({[a],mixed (d+1) [] h,mixed 0 ((P++m::(P++later)).map (h+·)) 0} :
      Set (Word Bool)) := by
  let cuts := repeats d m P
  have ne : P≠[] := by obtain ⟨pre,z,rfl,_⟩ := ending; simp
  have positive := List.length_pos_iff.mpr ne
  apply gap_selection_certificate h d cuts P m (P++later) pos (mem_repeats.mpr (Or.inl rfl))
    (fun _ hw => repeat_ending sep ending hw) (fun _ hp _ hq => repeat_aligned fresh hp hq)
  · intro _
    exact mem_repeats.mpr (Or.inr ⟨[],List.nil_prefix,positive,Or.inl rfl,rfl⟩)
  · intro host hw pre z post eqn _ cmp
    have no : ¬P <+: post := by
      rintro ⟨tail,form⟩
      have place : host=(pre++[z])++(P++tail) := by simpa only [form,List.append_assoc,List.singleton_append] using eqn
      have absurd := initial_only fresh hw place
      simp at absurd
    have pIn : P <+: P++later := ⟨_,rfl⟩
    have proper : post <+: P := by
      rcases cmp with early | late
      · exact (List.prefix_or_prefix_of_prefix early pIn).resolve_right no
      · exact (no (pIn.trans late)).elim
    have lt : post.length<P.length := by
      have le := proper.length_le
      by_contra notlt
      have same := proper.eq_of_length (by omega)
      exact no (same ▸ List.prefix_refl _)
    have endingIn : EndsShort d ((pre++[z])++post) := by
      simpa only [List.append_assoc,List.singleton_append,←eqn] using (repeat_ending sep ending hw)
    exact mem_repeats.mpr (Or.inr ⟨post,proper,lt,keep_ending endingIn,rfl⟩)

/-- A run of long gaps forced before a separator absent from the host
excludes both directions of prefix comparison. -/
theorem new_separator_certificate (h d n m : ℕ) (front longTail later : List ℕ)
    (pos : 0<h) (rise : d<n) (above : ∀ x∈longTail,d<x) (absent : m∉front++[d]) :
    HasFiniteCertificate ({[a],mixed (d+1) [] h,
      mixed 0 (((front++[d])++n::(longTail++m::later)).map (h+·)) 0} : Set (Word Bool)) := by
  let cut := front++[d]
  apply gap_selection_certificate h d [cut] cut n (longTail++m::later) pos (by simp)
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨front,d,rfl,le_rfl⟩
  · simp
  · omega
  · intro host hh pre z post eqn le cmp
    obtain rfl := List.mem_singleton.mp hh
    have marked := ends_after_split eqn (rise.trans_le le)
    have noM : m∉post := by
      intro mem
      apply absent
      change m∈cut
      rw [eqn]
      simp [mem]
    have demand : longTail++[m] <+: longTail++m::later := ⟨later,by simp⟩
    have miss : ¬ (longTail++[m] <+: post) := fun cmp => noM (cmp.sublist.subset (by simp))
    have before : post <+: longTail++[m] := by
      rcases cmp with early | late
      · exact (List.prefix_or_prefix_of_prefix early demand).resolve_right miss
      · exact (miss (demand.trans late)).elim
    rcases List.prefix_concat_iff.mp before with full | sub
    · exact (noM (by simp [full])).elim
    · exact (Nat.lt_irrefl _ (above d (sub.sublist.subset marked))).elim

end ThreeWordCodes.BinaryGaps
