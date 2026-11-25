module

public import ThreeWordCodes.PalindromicObstruction

/-! # Cuts preceding a new largest gap -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

theorem grouped_basis (s h : ℕ) (p : Word Bool) :
    spell (readers s h) p=spell (pair (x s) c) (spell (tokens h) p) := by
  rw [←spell_substitution]
  have same : (fun i => spell (pair (x s) c) (tokens h i))=readers s h := by
    funext i; cases i <;> simp [tokens,readers,pair,run,spell_replicate]
  rw [same]

theorem grouped_spelling (s h : ℕ) (ns : List ℕ) (lower : ∀ n∈ns,h≤n) :
    spell (readers s h) (mixed 0 (ns.map (·-h)) 0)=(c++following s ns)++wordPow (x s) h := by
  have restore : (ns.map (·-h)).map (h+·)=ns := restore_offset h ns lower
  rw [grouped_basis,show spell (tokens h) (mixed 0 (ns.map (·-h)) 0)=_ from spell_gap_names h 0 _,
    restore,show mixed 0 ns h=mixed 0 ns 0++run h from by simpa using (append_pure ns 0 0 h).symm,
    spell_append,spell_full]
  simp [run,spell_replicate,pair]

/-- The first literal letter of the next x is visible before z ends. -/
theorem Reading.visible_prefix {s : ℕ} {z : Word Bool} (pre : List ℕ) (n m : ℕ) (rest : List ℕ)
    (r : Reading s (pre++n::rest) z) (large : m<n) :
    (c++following s pre)++wordPow (x s) m++[a] <+: z := by
  obtain ⟨e,ne⟩ := Nat.exists_eq_add_of_le (show m+1≤n by omega)
  let D := (c++following s pre)++wordPow (x s) m
  let W := wordPow (x s) e++c++following s rest
  have eqn : z++x s=D++(x s++W) := by
    simpa [D,W,following,ne,wordPow_add,wordPow_succ (x s) m,List.append_assoc] using r.spelling
  have long : 1≤W.length := by simp [W,c]; omega
  have len := congrArg List.length eqn
  simp only [List.length_append] at len
  obtain ⟨t,head⟩ := x_head s
  have sub : D++[a] <+: z++x s := ⟨t++W,by rw [eqn,head]; simp [List.append_assoc]⟩
  rcases List.prefix_or_prefix_of_prefix sub (List.prefix_append z (x s)) with done | rev
  · exact done
  · have := rev.length_le
    rw [rev.eq_of_length (by simp at this ⊢; omega)]

/-- The selected prefix may have arbitrarily many markers. Every preceding
gap is between h and m. The next gap, being larger, distinguishes the literal
tail from every nonempty proper suffix of a leaf. -/
theorem record_gap_completion (s k l h m n : ℕ) (pre rest : List ℕ) (z : Word Bool)
    (r : Reading s (pre++n::rest) z) (nonempty : pre≠[]) (above : h≤m) (small : m-h≤k) (right : h≤l)
    (bounds : ∀ g∈pre,h≤g ∧ g≤m) (large : m<n) : Completable (triple s k l z) := by
  let v := readers s h
  let cut := pre.map (·-h)
  let d := m-h
  obtain ⟨tail,form⟩ := r.visible_prefix pre n m rest large
  let t := wordPow (x s) d ++ a::tail
  have nt : t≠[] := by simp [t]
  have lastBound (j : ℕ) (hj : j∈cut) : j≤d := by
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hj
    exact Nat.sub_le_sub_right (bounds u hu).2 h
  have nc : cut≠[] := by simpa [cut] using nonempty
  let prior := cut.dropLast
  let last := cut.getLast nc
  have snoc : cut=prior++[last] := (List.dropLast_concat_getLast nc).symm
  obtain ⟨hi,nz,pf⟩ := reader_prefix s h
  have cutCert := selected_gap_certificate v hi nz pf d [cut] cut t (by simp) nt
    (by
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact ⟨prior,last,snoc,lastBound last (by simp [snoc])⟩)
    (by simp) (by
      intro j us origin
      have jle : j≤d := by
        rcases origin with ⟨_,le⟩ | ⟨p,hp,old,g,shape,le⟩
        · exact le
        · obtain rfl := List.mem_singleton.mp hp
          exact le.trans (lastBound g (by simp [shape]))
      have emission : ∃ u, spell v (mixed j us 0)=wordPow (x s) j++b::u := by
        refine ⟨a::(wordPow (x s) h++spell v (gapTail 0 us)),?_⟩
        simp [v,readers,pair,run,mixed,c,spell_replicate]
      obtain ⟨u,hu⟩ := emission
      obtain ⟨e,eqn⟩ := Nat.exists_eq_add_of_le jle
      have initial : ∃ p,wordPow (x s) e++a::tail=a::p := by
        cases e with
        | zero => exact ⟨_,rfl⟩
        | succ e =>
          obtain ⟨p,head⟩ := x_head s
          rw [wordPow_succ',head]; exact ⟨_,rfl⟩
      obtain ⟨p,hp⟩ := initial
      have headT : t=wordPow (x s) j++a::p := by rw [show t=wordPow (x s) d++a::tail from rfl,eqn,wordPow_add,List.append_assoc,hp]
      have apart : ¬Comparable t (spell v (mixed j us 0)) := by
        rw [hu,headT]
        rintro (⟨w,eq⟩ | ⟨w,eq⟩) <;> simp [List.append_assoc,a,b] at eq
      exact ⟨fun eq => apart (Or.inl (eq ▸ List.prefix_refl _)),fun cp => (apart cp).elim⟩)
  have mid : spell v (mixed (d+1) [] 0)=y s d h := by simp [v,mixed,run,gapTail,readers,pair,spell_replicate,y,List.append_assoc]
  have whole : spell v (mixed 0 cut 0)++t=z := by
    rw [show spell v (mixed 0 cut 0)=_ from grouped_spelling s h pre (fun g hg => (bounds g hg).1),←form]
    have cutSum : h+d=m := Nat.add_sub_of_le above
    simp only [t,List.append_assoc,List.singleton_append]
    rw [←List.append_assoc (wordPow (x s) h),←wordPow_add,cutSum]
  rw [mid,whole] at cutCert
  have first : z.head?=some b := by rw [←form]; rfl
  exact raise_exponents (from_certificate first cutCert) k l small right

private theorem split_initial (m : ℕ) (xs : List ℕ) :
    xs=List.replicate xs.length m ∨ ∃ j n tail,n≠m ∧ xs=List.replicate j m++n::tail := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    by_cases same : x=m
    · subst x
      rcases ih with eqn | ⟨j,n,t,ne,form⟩
      · exact Or.inl (by simpa [List.replicate_succ] using congrArg (m::·) eqn)
      · exact Or.inr ⟨j+1,n,t,ne,by simp [List.replicate_succ,form]⟩
    · exact Or.inr ⟨0,x,xs,same,rfl⟩

/-- The minimum at the first gap may repeat any number of times. -/
theorem minimum_initial_completion (s k l m : ℕ) (rest : List ℕ) (z : Word Bool)
    (r : Reading s (m::rest) z) (lower : max k l≤m) (least : ∀ n∈rest,m≤n)
    (code : NamedCode (triple s k l z)) : Completable (triple s k l z) := by
  obtain ⟨short,mem,lt⟩ := r.small_gap code
  have small : m≤k+l := (by rcases List.mem_cons.mp mem with rfl | h; exact le_rfl; exact least short h : m≤short) |>.trans lt
  rcases split_initial m rest with uniform | ⟨j,n,tail,ne,form⟩
  · have eqn : m::rest=List.replicate (rest.length+1) m := by
      rw [List.replicate_succ]; exact congrArg (m::·) uniform
    exact (constant_gap_ambiguity (eqn ▸ r) lower code).elim
  · have large := least n (by simp [form])
    let P := List.replicate (j+1) m
    have raw : m::rest=P++n::tail := by simp [P,form,List.replicate_succ]
    apply record_gap_completion s k l l m n P tail z (raw ▸ r) (by simp [P]) (by omega) (by omega) le_rfl
    · intro g hg
      rw [List.eq_of_mem_replicate hg]
      exact ⟨by omega,le_rfl⟩
    · omega

end ThreeWordCodes.Palindromic
