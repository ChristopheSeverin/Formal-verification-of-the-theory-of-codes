module

public import ThreeWordCodes.AlternatingThird

/-! # Completing Proposition 7 when either end of the third word is a -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps
variable {A I : Type*}

theorem cut_reading {v : I → Word A} {z : Word A} (p : Word I) (pref : z <+: spell v p) :
    (∃ u,spell v u=z) ∨ ∃ u i t,t≠[] ∧ t <+: v i ∧ t≠v i ∧ z=spell v u++t := by
  induction p generalizing z with
  | nil => exact Or.inl ⟨[],(List.eq_nil_of_prefix_nil pref).symm⟩
  | cons i p ih =>
    have token : v i <+: spell v (i::p) := ⟨_,rfl⟩
    rcases List.prefix_or_prefix_of_prefix pref token with finishes | consumed
    · by_cases nil : z=[]
      · exact Or.inl ⟨[],nil.symm⟩
      by_cases full : z=v i
      · exact Or.inl ⟨[i],by simp [full]⟩
      · exact Or.inr ⟨[],i,z,nil,finishes,full,rfl⟩
    · obtain ⟨t,form⟩ := consumed
      obtain ⟨s,rest⟩ := pref
      have sub : t <+: spell v p := ⟨s,List.append_cancel_left (as:=v i)
        (by simpa only [←form,spell_cons,List.append_assoc] using rest)⟩
      rcases ih sub with ⟨u,eqn⟩ | ⟨u,j,w,nonempty,mid,proper,eqn⟩
      · exact Or.inl ⟨i::u,by simp [eqn,form]⟩
      · exact Or.inr ⟨i::u,j,w,nonempty,mid,proper,by simp [←form,eqn,List.append_assoc]⟩

theorem prefix_on_x_c (s l : ℕ) {z : Word Bool} (read : ∃ p,z <+: spell (readers s l) p) :
    ∃ p,z <+: spell (pair (x s) c) p := by
  let v := pair (x s) c
  let names := pair [a] (b :: List.replicate l a)
  have eqn : (fun i => spell v (names i))=readers s l := by
    funext i
    cases i <;> simp [readers,v,names,pair,a,b,spell_replicate]
  obtain ⟨p,hp⟩ := read
  exact ⟨spell names p,by rw [←spell_substitution,eqn]; exact hp⟩

theorem pal_start (n : ℕ) : ∃ t, pal n=a::t := by
  cases n with
  | zero => exact ⟨[],rfl⟩
  | succ n => rw [pal,wordPow_succ']; exact ⟨_,rfl⟩

private theorem pal_rev (n : ℕ) : (pal n).reverse=pal n := by
  simp only [pal,List.reverse_append,List.reverse_singleton,back_pow]
  exact (rotate_power [a] [b] n).symm

private theorem pal_prefix (n : ℕ) (w : Word Bool) (ending : w.getLast?=some a)
    (pref : w <+: pal n) : ∃ i≤n, w=pal i := by
  induction n with
  | zero =>
    rcases List.prefix_concat_iff.mp (show w <+: []++[a] from pref) with ready | nil
    · exact ⟨0,le_rfl,ready⟩
    · rw [List.eq_nil_of_prefix_nil nil] at ending; contradiction
  | succ n ih =>
    have snoc : pal (n+1)=(pal n++[b])++[a] := by simpa [c,List.append_assoc] using (enlarge n 1).symm
    rw [snoc] at pref
    rcases List.prefix_concat_iff.mp pref with eqn | earlier
    · exact ⟨n+1,le_rfl,eqn.trans snoc.symm⟩
    rcases List.prefix_concat_iff.mp earlier with eqn | earlier
    · rw [eqn,List.getLast?_concat] at ending
      contradiction
    · obtain ⟨i,le,eqn⟩ := ih earlier
      exact ⟨i,by omega,eqn⟩

private theorem before_double (n m : ℕ) (t : Word Bool) (short : m<n) :
    ¬∃ p,pal m++a::t <+: spell (pair (pal n) c) p := by
  have snoc : ∃ after, pal n=pal m++b::after := by
    obtain ⟨j,he⟩ := Nat.exists_eq_add_of_le (show m+1≤n by omega)
    have form : n=m+(j+1) := by omega
    rw [form,←enlarge,wordPow_succ']
    exact ⟨_,rfl⟩
  obtain ⟨after,snoc⟩ := snoc
  rintro ⟨p,s,eqn⟩
  cases p with
  | nil => simp at eqn
  | cons i p =>
    cases i with
    | false =>
      change (pal m++a::t)++s = pal n ++ _ at eqn
      rw [snoc] at eqn
      simp [List.append_assoc,a,b] at eqn
    | true =>
      obtain ⟨r,head⟩ := pal_start m
      simp [head,pair,c,a,b] at eqn

/-- A third word ending in a completes. An incomplete reading would end
with a proper prefix (ab)^i a of x. Unless it was the entire third word,
the preceding token ends in a and prevents the reverse reading. -/
theorem final_a_completion (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (ending : z.getLast?=some a) : Completable (triple s k l z) := by
  by_contra bad
  obtain ⟨left,_,right,_⟩ := two_proper_readings code bad
  obtain ⟨p,pr⟩ := prefix_on_x_c s l left
  have rev := prefix_on_x_c s k right
  let v := pair (x s) c
  rcases cut_reading p pr with full | ⟨u,i,t,nt,tr,proper,form⟩
  · exact bad (complete_on_x_c s k l z code full)
  have endT : t.getLast?=some a := by
    simpa only [form,List.getLast?_append,List.getLast?_eq_getLast_of_ne_nil nt,Option.some_or] using ending
  cases i with
  | true =>
    rcases List.prefix_concat_iff.mp (show t <+: [b]++[a] from tr) with full | shorter
    · exact proper full
    rcases List.prefix_concat_iff.mp (show t <+: []++[b] from shorter) with singleton | nil
    · rw [singleton,List.getLast?_concat] at endT; contradiction
    · exact nt (List.eq_nil_of_prefix_nil nil)
  | false =>
    obtain ⟨m,le,cut⟩ := pal_prefix (s+1) t endT tr
    have lt : m<s+1 := by
      have neq : m≠s+1 := fun e => proper (show t=pal (s+1) by rw [←e]; exact cut)
      omega
    by_cases none : u=[]
    · have eqn : z=pal m := by simpa [none,cut] using form
      exact bad (eqn.symm ▸ letter_ends s k l m (eqn ▸ code))
    obtain ⟨before,letter⟩ : ∃ before, spell v u=before++[a] := by
      have decomp := List.dropLast_concat_getLast none
      have split : spell v u=spell v u.dropLast++v (u.getLast none) := by
        simpa only [spell_append,spell_cons,spell_nil,List.append_nil] using congrArg (spell v) decomp.symm
      cases e : u.getLast none with
      | false =>
        exact ⟨spell v u.dropLast++wordPow [a,b] (s+1),by simpa [e,v,pair,x,List.append_assoc] using split⟩
      | true =>
        exact ⟨spell v u.dropLast++[b],by simpa [e,v,pair,c,List.append_assoc] using split⟩
    have eqn : z.reverse = pal m++a::before.reverse := by
      change z=spell v u++t at form
      simp [form,letter,cut,pal_rev]
    exact before_double (s+1) m before.reverse lt (eqn ▸ rev)

/-- Reversal gives the second endpoint case. -/
theorem initial_a_completion (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (initial : z.head?=some a) : Completable (triple s k l z) := by
  apply flip_back
  exact final_a_completion s l k z.reverse (triple_reverse s k l z ▸ code.reverse) (by simpa using initial)

end ThreeWordCodes.Palindromic
