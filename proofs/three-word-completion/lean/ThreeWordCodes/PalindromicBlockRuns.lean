module

public import ThreeWordCodes.PalindromicPattern
public import ThreeWordCodes.MaximumRunGraft

/-! # Selecting a returning run of maximum blocks -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem root_of_runs (m : ℕ) (F : List ℕ) (r : ℕ) (bs : List (List ℕ))
    (ne : F≠[]) (above : ∀ n∈F,m<n) (top : ∀ B∈bs,blockWeight B≤blockWeight F)
    (one : ∀ pre tail, bs=pre++(List.replicate (r+1) F++tail) → pre=[]) :
    OnlyAtStart (blockPattern m F r) (separated m bs) := by
  intro pre W tail form dom
  have rigid := dominated_run F r bs ne above top pre W tail form dom
  rw [rigid] at form
  exact pattern_starts_at_root m F r bs (fun hm => Nat.lt_irrefl _ (above m hm)) ne
    (recognizes_of_weight top) one pre tail form

private theorem pattern_suffix (m : ℕ) (F : List ℕ) (r : ℕ) : F <:+ blockPattern m F r := by
  cases r with
  | zero => simp [blockPattern]
  | succ r =>
    rw [blockPattern,wordPow_succ]
    exact ⟨F++wordPow (m::F) r++[m],by simp [List.append_assoc]⟩

/-- The next long run occurs after a block different from F, while every
return to F within the selected history is shorter than the initial run. -/
theorem block_run_completion (s k l m : ℕ) (F D : List ℕ) (r : ℕ)
    (past : List (List ℕ × ℕ)) (later : List ℕ) (z : Word Bool)
    (different : D≠F) (ne : F≠[]) (bound : max k l≤m) (short : m≤k+l)
    (bounded : ∀ e∈past,e.1≠F ∧ e.2<r+1) :
    let history := List.replicate (r+1) F ++ BlockRuns.after F past
    let U := separated m history
    let R := blockPattern m F r
    let all := history++[D,F]
    (∀ B∈all,∀ n∈B,m<n) → (∀ B∈all,blockWeight B≤blockWeight F) →
    (∀ n∈U++D++m::(R++later),l≤n) → Reading s (U++D++m::(R++later)) z → z.getLast?=some b →
    Completable (triple s k l z) := by
  intro history U R all long top low read ending
  have hne : history≠[] := by simp [history]
  have above := long F (by simp [all])
  have fresh : m∉F := fun hm => Nat.lt_irrefl _ (above m hm)
  have dne : m∉D := fun hm => Nat.lt_irrefl _ (long D (by simp [all]) m hm)
  have rn : R≠[] := by simp [R,blockPattern,ne]
  have last : l<R.getLast rn := by
    obtain ⟨p,hp⟩ := pattern_suffix m F r
    have eqn : R.getLast?=F.getLast? := by
      change (blockPattern m F r).getLast?=_
      rw [←hp,List.getLast?_append,List.getLast?_eq_getLast_of_ne_nil ne,Option.some_or]
    rw [List.getLast?_eq_getLast_of_ne_nil rn,List.getLast?_eq_getLast_of_ne_nil ne,Option.some.injEq] at eqn
    have := above _ (List.getLast_mem ne)
    omega
  have ends : EndsAt m U := by
    have eqn := List.dropLast_concat_getLast hne
    change EndsAt m (separated m history)
    rw [←eqn,separated_append,separated_singleton]
    exact ⟨_,(List.append_assoc ..).symm⟩
  have starts : R <+: U := by
    change blockPattern m F r <+: separated m (List.replicate (r+1) F++BlockRuns.after F past)
    rw [separated_append,separated_run,List.append_assoc]
    exact ⟨_,rfl⟩
  have root : OnlyAtStart R U := root_of_runs m F r history ne above
    (fun B hb => top B (List.mem_append_left _ hb)) (BlockRuns.initial_run (Nat.succ_pos _) past bounded)
  have next (p : List ℕ) (shortPref : ShortPrefix m p (D++m::R)) : OnlyAtStart R (U++p) := by
    have atLeast : ∀ n∈D++m::R,m≤n := by
      intro n hn
      rcases List.mem_append.mp hn with inD | within
      · exact (long D (by simp [all]) n inD).le
      rcases List.mem_cons.mp within with rfl | inR
      · rfl
      have allR (t : ℕ) : ∀ n∈blockPattern m F t,m≤n := by
        induction t with
        | zero => exact fun n hn => (above n (by simpa [blockPattern] using hn)).le
        | succ t ih =>
          have form : blockPattern m F (t+1)=F++m::blockPattern m F t := by simp [blockPattern,wordPow_succ']
          intro n hn
          rcases List.mem_append.mp (form ▸ hn) with f | later
          · exact (above n f).le
          · rcases List.mem_cons.mp later with rfl | next
            · rfl
            · exact ih n next
      exact allR r n inR
    obtain ⟨pre,lastN,snoc,le⟩ := shortPref.2.2
    have ge := atLeast lastN (shortPref.1.sublist.subset (by simp [snoc]))
    have exactEnd : EndsAt m p := ⟨pre,by rwa [show m=lastN by omega]⟩
    obtain ⟨j,small,which⟩ := permitted_prefix dne fresh ⟨shortPref.1,shortPref.2.1,exactEnd⟩
    let host := history++D::List.replicate j F
    have hostEq : U++p=separated m host := by rw [which,separated_append]
    rw [hostEq]
    apply root_of_runs m F r host ne above
    · intro B hb
      apply top B
      rcases List.mem_append.mp hb with old | add
      · exact List.mem_append_left _ old
      rcases List.mem_cons.mp add with rfl | f
      · simp [all]
      · obtain rfl := List.eq_of_mem_replicate f
        simp [all]
    · have decomposition : host=List.replicate (r+1) F++BlockRuns.after F (past++[(D,j)]) := by
        simp [host,history,List.append_assoc]
      rw [decomposition]
      apply BlockRuns.initial_run (Nat.succ_pos _)
      intro e he
      rcases List.mem_append.mp he with old | add
      · exact bounded e old
      · obtain rfl := List.mem_singleton.mp add
        exact ⟨different,by simpa using small⟩
  obtain ⟨n,lead,ld⟩ : ∃ n : ℕ, ∃ lead : List ℕ,D++[m]=n::lead := by
    cases D with
    | nil => exact ⟨m,[],rfl⟩
    | cons n t => exact ⟨n,t++[m],rfl⟩
  have demand : D++m::R=n::(lead++R) := by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using congrArg (·++R) ld
  have raw : U++D++m::(R++later)=U++(n::(lead++R))++later := by
    rw [←demand]; simp [List.append_assoc]
  obtain ⟨p,ep⟩ := ends
  exact pattern_completion s k l m U n lead R later z (raw ▸ read) (by omega) short (raw ▸ low) rn last
    ⟨p,m,ep,le_rfl⟩ starts root (fun p hp => next p (demand.symm ▸ hp)) ending

end ThreeWordCodes.Palindromic
