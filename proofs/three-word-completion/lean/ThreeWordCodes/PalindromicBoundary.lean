module

public import ThreeWordCodes.PalindromicGraft

/-! # The literal shape of an obstruction to Proposition 7 -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem alternating_run (n : ℕ) (u : Word Bool) (short : u=[] ∨ u=[b]) :
    (wordPow c n ++ u).IsChain (·≠·) := by
  induction n with
  | zero => rcases short with rfl | rfl <;> simp
  | succ n ih =>
    rw [wordPow_succ']
    change (b::a::(wordPow c n ++ u)).IsChain (·≠·)
    apply List.isChain_cons_cons.mpr ⟨by decide,?_⟩
    cases n with
    | zero => rcases short with rfl | rfl <;> decide
    | succ n =>
      rw [wordPow_succ'] at ih ⊢
      exact List.isChain_cons_cons.mpr ⟨by decide,ih⟩

private theorem after_two (s k l : ℕ) (t : Word Bool) (n : ℕ)
    (code : NamedCode (triple s k l (wordPow c (n+2) ++ t))) :
    Completable (triple s k l (wordPow c (n+2) ++ t)) := by
  induction t using List.twoStepInduction generalizing n with
  | nil => exact alternating_third_completion _ _ _ _ code (alternating_run _ _ (Or.inl rfl))
  | singleton i =>
    cases i with
    | false => exact power_graft_completion _ _ _ _ [a] (by unfold Comparable c; decide)
    | true => exact alternating_third_completion _ _ _ _ code (alternating_run _ _ (Or.inr rfl))
  | cons_cons i j t ih _ =>
    by_cases starts : i=b ∧ j=a
    · obtain ⟨rfl,rfl⟩ := starts
      have form : wordPow c (n+2) ++ b::a::t=wordPow c ((n+1)+2)++t := by
        rw [show n+1+2=(n+2)+1 by omega,wordPow_succ c (n+2),List.append_assoc]; rfl
      rw [form] at code ⊢
      exact ih (n+1) code
    · apply power_graft_completion
      rintro (⟨u,eqn⟩ | ⟨u,eqn⟩)
      · exact starts ⟨(List.cons.inj eqn).1,(List.cons.inj (List.cons.inj eqn).2).1⟩
      · exact starts ⟨(List.cons.inj eqn).1.symm,(List.cons.inj (List.cons.inj eqn).2).1.symm⟩

/-- In either orientation, an initial bab settles the whole family. -/
theorem initial_bab_completion (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (start : [b,a,b] <+: z) : Completable (triple s k l z) := by
  obtain ⟨t,rfl⟩ := start
  cases t with
  | nil => exact alternating_third_completion _ _ _ _ code (by decide)
  | cons i t =>
    cases i with
    | false => exact after_two s k l t 0 code
    | true => exact forbidden_factor_completion _ _ _ _ (Or.inl ⟨[b,a],t,rfl⟩)

theorem final_bab_completion (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (stop : [b,a,b] <:+ z) : Completable (triple s k l z) := by
  apply flip_back
  exact initial_bab_completion s l k z.reverse (triple_reverse s k l z ▸ code.reverse) stop.reverse

private theorem starts_baa {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) : [b,a,a] <+: z := by
  obtain ⟨start,_,dbl,noBB,_⟩ := residual_word code bad
  cases z with
  | nil => contradiction
  | cons i z =>
    obtain rfl : i=b := by simpa using start
    cases z with
    | nil => exact (False.elim ((by decide : ¬ [a,a] <:+: [b]) dbl))
    | cons j z =>
      cases j with
      | true => exact (noBB ⟨[],z,rfl⟩).elim
      | false =>
        cases z with
        | nil => exact (False.elim ((by decide : ¬ [a,a] <:+: [b,a]) dbl))
        | cons i z =>
          cases i with
          | true => exact (bad (initial_bab_completion _ _ _ _ code ⟨z,rfl⟩)).elim
          | false => exact ⟨z,rfl⟩

theorem double_boundaries {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) : [b,a,a] <+: z ∧ [a,a,b] <:+ z := by
  have rev := starts_baa (triple_reverse s k l z ▸ code.reverse) (fun ok => bad (flip_back ok))
  exact ⟨starts_baa code bad,by simpa using rev.reverse⟩

private theorem end_of_product (s : ℕ) {p : Word Bool} (ne : p≠[]) :
    c <:+ spell (pair (x s) c) p := by
  induction p using List.reverseRecOn with
  | nil => contradiction
  | append_singleton p i _ =>
    rw [spell_append,spell_cons,spell_nil,List.append_nil]
    apply List.IsSuffix.trans _ (List.suffix_append ..)
    cases i with
    | true => exact List.suffix_refl _
    | false =>
      change c <:+ pal (s+1)
      rw [←enlarge s 1]
      exact List.suffix_append ..

private theorem partial_palindrome (s : ℕ) {t : Word Bool} (pr : t <+: pal s)
    (ends : t.getLast?=some b) : ∃ n,t=wordPow [a,b] (n+1) := by
  induction s with
  | zero =>
    rcases List.prefix_concat_iff.mp (show t <+: []++[a] from pr) with rfl | nil
    · contradiction
    · rw [List.eq_nil_of_prefix_nil nil] at ends; contradiction
  | succ s ih =>
    have snoc : pal (s+1)=(wordPow [a,b] (s+1))++[a] := rfl
    rcases List.prefix_concat_iff.mp (snoc ▸ pr) with eqn | earlier
    · rw [eqn,List.getLast?_concat] at ends; contradiction
    have penult : wordPow [a,b] (s+1)=pal s++[b] := by rw [wordPow_succ]; simp [pal,List.append_assoc]
    rcases List.prefix_concat_iff.mp (penult ▸ earlier) with whole | before
    · exact ⟨s,whole.trans penult.symm⟩
    · exact ih before

/-- Each surviving third word is ba followed by complete x,ba tokens and a
final ab. This supplies a positive spelling for the signed-coordinate model. -/
theorem middle_reading {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) :
    ∃ p : Word Bool, z=c ++ spell (pair (x s) c) p ++ c.reverse := by
  let v := pair (x s) c
  obtain ⟨initial,final⟩ := double_boundaries code bad
  obtain ⟨read,_,_,_⟩ := two_proper_readings code bad
  obtain ⟨p,pr⟩ := prefix_on_x_c s l read
  rcases cut_reading p pr with full | ⟨u,i,t,nt,pref,proper,form⟩
  · exact (bad (complete_on_x_c _ _ _ _ code full)).elim
  have fin : z.getLast?=some b := (residual_word code bad).2.1
  have endT : t.getLast?=some b := by
    simpa only [form,List.getLast?_append,List.getLast?_eq_getLast_of_ne_nil nt,Option.some_or] using fin
  have noBab : ¬[b,a,b] <:+ z := fun en => bad (final_bab_completion _ _ _ _ code en)
  have two : t=c.reverse := by
    cases i with
    | true =>
      change t <+: [b]++[a] at pref
      rcases List.prefix_concat_iff.mp pref with full | shorter
      · exact (proper full).elim
      rcases List.prefix_concat_iff.mp (show t <+: []++[b] from shorter) with rfl | nil
      · by_cases empty : u=[]
        · have h : [a,a,b] <:+ [b] := by simpa [form,empty] using final
          exact ((by decide : ¬ [a,a,b] <:+ [b]) h).elim
        · obtain ⟨before,suf⟩ := end_of_product s empty
          exact (noBab ⟨before,by rw [form,←suf,List.append_assoc]; rfl⟩).elim
      · exact (nt (List.eq_nil_of_prefix_nil nil)).elim
    | false =>
      obtain ⟨j,rfl⟩ := partial_palindrome (s+1) pref endT
      cases j with
      | zero => rfl
      | succ j =>
        apply False.elim (noBab _)
        have snoc : wordPow [a,b] (j+1+1) = wordPow [a,b] j ++ [a,b,a,b] := by
          rw [wordPow_succ,wordPow_succ]; simp
        exact ⟨spell v u ++ wordPow [a,b] j ++ [a],by simp [form,snoc,v]⟩
  cases u with
  | nil =>
    rw [form,two] at initial
    exact (False.elim ((by decide : ¬[b,a,a] <+: c.reverse) initial))
  | cons i u =>
    cases i with
    | true => exact ⟨u,by simp [form,two,pair,List.append_assoc]⟩
    | false =>
      obtain ⟨after,head⟩ := x_head s
      obtain ⟨before,eqn⟩ := initial
      simp [form,pair,head,a,b] at eqn

end ThreeWordCodes.Palindromic
