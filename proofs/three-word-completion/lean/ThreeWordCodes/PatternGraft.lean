module

public import ThreeWordCodes.GapSelection

/-! # Grafting with a pattern that occurs only at the start of each leaf -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

def EndsAt (m : ℕ) (w : List ℕ) : Prop := ∃ v, w=v++[m]
def CutPrefix (m : ℕ) (w look : List ℕ) : Prop := w <+: look ∧ w.length<look.length ∧ EndsAt m w
def OccursOnlyInitially (pattern w : List ℕ) : Prop :=
  ∀ pre tail, w=pre++(pattern++tail) → pre=[]

noncomputable def selectedPrefixes (m : ℕ) (U look : List ℕ) : List (List ℕ) := by
  classical
  let good := look.inits.filter fun p => p.length<look.length ∧ EndsAt m p
  exact U::good.map (U++·)

theorem selected_spec {m U look w} : w∈selectedPrefixes m U look ↔
    w=U ∨ ∃ p, CutPrefix m p look ∧ w=U++p := by
  classical
  simp only [selectedPrefixes,List.mem_cons,List.mem_map,List.mem_filter,decide_eq_true_eq,List.mem_inits]
  constructor
  · rintro (rfl | ⟨p,⟨pr,lt,ends⟩,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p,⟨pr,lt,ends⟩,rfl⟩
  · rintro (rfl | ⟨p,⟨pr,lt,ends⟩,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p,⟨pr,lt,ends⟩,rfl⟩

/-- The next gaps are n, the remaining leading gaps, and a distinguished
pattern R. Select every shorter prefix ending at the separator. A matching
of the entire demand would put R strictly after the start of a selected leaf. -/
theorem initial_pattern_certificate (h m n : ℕ) (U lead R later : List ℕ)
    (pos : 0<h) (lower : m≤n) (nonempty : R≠[]) (endsU : EndsAt m U) (starts : R <+: U)
    (uniqueU : OccursOnlyInitially R U)
    (uniqueCuts : ∀ p, CutPrefix m p (n::(lead++R)) → OccursOnlyInitially R (U++p)) :
    HasFiniteCertificate ({[a], mixed (m+1) [] h,
      mixed 0 ((U++n::((lead++R)++later)).map (h+·)) 0} : Set (Word Bool)) := by
  let look := n::(lead++R)
  let cuts := selectedPrefixes m U look
  have selected : U∈cuts := selected_spec.mpr (Or.inl rfl)
  have ends (w : List ℕ) (hw : w∈cuts) : EndsAt m w := by
    rcases selected_spec.mp hw with rfl | ⟨p,⟨_,_,before,rfl⟩,rfl⟩
    · exact endsU
    · exact ⟨U++before,by simp⟩
  have begins (w : List ℕ) (hw : w∈cuts) : R <+: w := by
    rcases selected_spec.mp hw with rfl | ⟨p,_,rfl⟩
    · exact starts
    · exact starts.trans ⟨p,rfl⟩
  have unique (w : List ℕ) (hw : w∈cuts) : OccursOnlyInitially R w := by
    rcases selected_spec.mp hw with rfl | ⟨p,ok,rfl⟩
    · exact uniqueU
    · exact uniqueCuts p ok
  have limit : 0 < (lead++R).length := by simp [List.length_pos_iff,nonempty]
  apply gap_selection_certificate h m cuts U n ((lead++R)++later) pos selected
  · intro w hw
    obtain ⟨pre,last⟩ := ends w hw
    exact ⟨pre,m,last,le_rfl⟩
  · intro p hp q hq suf
    obtain ⟨pre,eqn⟩ := suf
    obtain ⟨tail,form⟩ := begins p hp
    have empty := unique q hq pre tail (by rw [form,eqn])
    simpa only [empty,List.nil_append] using eqn
  · intro bound
    have same : n=m := by omega
    exact selected_spec.mpr (Or.inr ⟨[n],⟨List.cons_prefix_cons.mpr ⟨rfl,List.nil_prefix⟩,
      by simpa only [look,List.length_singleton,List.length_cons,List.length_nil,Nat.succ_lt_succ_iff] using limit,⟨[],by simp [same]⟩⟩,rfl⟩)
  · intro host hh pre z post eqn le cmp
    have no : ¬ (lead++R <+: post) := by
      rintro ⟨tail,form⟩
      have occurs : host=(pre++z::lead)++(R++tail) := by
        rw [eqn,←form]
        simp [List.append_assoc]
      have impossible := unique host hh _ _ occurs
      simp at impossible
    have base : lead++R <+: (lead++R)++later := ⟨later,rfl⟩
    have before : post <+: lead++R := by
      rcases cmp with early | late
      · exact (List.prefix_or_prefix_of_prefix early base).resolve_right no
      · exact (no (base.trans late)).elim
    have small : post.length < (lead++R).length := by
      have le := before.length_le
      by_contra wrong
      exact no (before.eq_of_length (by omega) ▸ List.prefix_refl _)
    have ending : EndsAt m (n::post) := by
      obtain ⟨start,last⟩ := ends host hh
      induction post using List.reverseRecOn with
      | nil =>
        have both := congrArg List.getLast? (eqn.symm.trans last)
        simp only [List.getLast?_concat,Option.some.injEq] at both
        exact ⟨[],by simp [show n=m by omega]⟩
      | append_singleton p t _ =>
        have endEq : (pre++z::p)++[t]=start++[m] := by simpa using eqn.symm.trans last
        have same : t=m := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? endEq
        exact ⟨n::p,by simp [same]⟩
    apply selected_spec.mpr
    exact Or.inr ⟨n::post,⟨List.cons_prefix_cons.mpr ⟨rfl,before⟩,by simpa [look] using small,ending⟩,rfl⟩

end ThreeWordCodes.BinaryGaps
