module

public import ThreeWordCodes.BorderBranch

/-! # The forbidden commutation in the border case -/

@[expose] public section
namespace ThreeWordCodes.Border
variable {A I : Type*}

private theorem no_extra_reading (g : I → Word A) (w : Word I) :
    ¬ NamedCode (addToken g (spell g w)) := by
  let v := addToken g (spell g w)
  have mapped (s : Word I) : spell v (s.map some)=spell g s := by
    induction s with
    | nil => rfl
    | cons i s ih => simp [v,addToken,ih]
  intro code
  have parsed : spell v [none]=spell v (w.map some) := by
    rw [mapped]; simp [v,addToken]
  have h := code parsed
  cases w <;> simp at h

/-- When the two marked readings diverge immediately after the cut, the
cut is a token boundary. Appending full copies of x then reads all of y. -/
theorem commuting_at_right_cut [Fintype A] (x z c : Word A) (i j e : ℕ)
    (diff : x.head?≠z.head?)
    (comm : c++(wordPow z (e+1)++x)=(wordPow z (e+1)++x)++c)
    (code : NamedCode (addToken (pair x z) ((wordPow x i++c)++wordPow x (j+1)))) :
    Completable (addToken (pair x z) ((wordPow x i++c)++wordPow x (j+1))) := by
  let g := pair x z
  let u := wordPow x i++c
  let y := u++wordPow x (j+1)
  let t := wordPow z (e+1)++x
  have nx := code.entry_ne_nil (some false)
  have nz := code.entry_ne_nil (some true)
  change x≠[] at nx
  change z≠[] at nz
  obtain ⟨a,as,hx⟩ := List.exists_cons_of_ne_nil nx
  obtain ⟨b,bs,hz⟩ := List.exists_cons_of_ne_nil nz
  have ab : a≠b := by simpa [hx,hz] using diff
  have nonempty : ∀ k,g k≠[] := by rintro (_|_) <;> assumption
  have mark : Function.Injective (fun k => (g k).head?) := by
    rintro (_|_) (_|_) h <;> simp_all [g,pair]
  obtain ⟨inj,prefixFree⟩ := marked_facts g nonempty mark
  by_cases readable : ∃ words,y <+: spell g words
  · obtain ⟨words,read⟩ := readable
    have firstX : [a] <+: wordPow x (j+1) := by
      rw [wordPow_succ',hx]; exact ⟨_,rfl⟩
    have firstZ : [b] <+: t := by
      dsimp [t]; rw [wordPow_succ',hz]; exact ⟨_,rfl⟩
    have nt : t≠[] := by rintro ht; rw [ht] at firstZ; simp at firstZ
    obtain ⟨h,ref⟩ := next_after_commuting nt comm
    let other := List.replicate i false ++ wordPow (List.replicate (e+1) true ++ [false]) h
    have refWord : spell g other=wordPow x i++wordPow t h := by
      simp [other,g,pair,spell_replicate,spell_wordPow,t]
    have left : u++[a] <+: spell g words := ((List.prefix_append_right_inj u).mpr firstX).trans read
    have right : u++[b] <+: spell g other := by
      rw [refWord]; dsimp [u]; rw [List.append_assoc]
      exact (List.prefix_append_right_inj _).mpr (((List.prefix_append_right_inj c).mpr firstZ).trans ref)
    obtain ⟨v,cut⟩ := read_at_branch nonempty mark ab u words other left right
    have whole : spell g (v++List.replicate (j+1) false)=y := by
      simp [cut,y,g,pair,spell_replicate]
    change NamedCode (addToken g y) at code
    rw [←whole] at code
    exact (no_extra_reading g _ code).elim
  · exact greedy_completion inj nonempty prefixFree y readable

theorem short_shift (p q : Word A) (n : ℕ) :
    short p q n ++ (q++p) = (p++q) ++ short p q n := by
  dsimp [short]
  rw [List.append_assoc,←wordPow_succ,wordPow_succ']
  simp [List.append_assoc]

theorem short_reverse (p q : Word A) (n : ℕ) :
    (short p q n).reverse=short p.reverse q.reverse n := by
  dsimp [short]
  rw [←rotate_power p q n,List.reverse_append,reverse_pow,List.reverse_append]

theorem family_reverse (p q z : Word A) (n i j : ℕ) :
    (fun k => (family p q z n i j k).reverse)=family p.reverse q.reverse z.reverse n j i := by
  funext k
  rcases k with _ | (_ | _)
  · rfl
  · exact short_reverse p q n
  · dsimp [family,addToken,pair]
    simp only [List.reverse_append,reverse_pow,short_reverse]
    rw [wordPow_succ' (short p.reverse q.reverse n) i,wordPow_succ (short p.reverse q.reverse n) j]
    simpa only [List.append_assoc] using congrArg
      (fun w => wordPow (short p.reverse q.reverse n) j++w++wordPow (short p.reverse q.reverse n) i)
      (short_shift p.reverse q.reverse n).symm

private theorem reverse_identity (p q z : Word A) (m : ℕ)
    (comm : (q++p)++(wordPow z m++p)=(wordPow z m++p)++(q++p)) :
    (q.reverse++p.reverse)++(wordPow z.reverse m++p.reverse)=
      (wordPow z.reverse m++p.reverse)++(q.reverse++p.reverse) := by
  have cut : (q++p)++wordPow z m=wordPow z m++(p++q) := by
    apply List.append_cancel_right (bs:=p)
    simpa [List.append_assoc] using comm
  have rev := congrArg List.reverse cut
  simp only [List.reverse_append,reverse_pow] at rev
  simpa only [List.append_assoc] using congrArg (·++p.reverse) rev.symm

private theorem commutes_with_short (p q z : Word A) (m n : ℕ)
    (comm : (q++p)++(wordPow z m++p)=(wordPow z m++p)++(q++p)) :
    (q++p)++(wordPow z m++short p q n)=(wordPow z m++short p q n)++(q++p) := by
  let c := q++p
  let v := wordPow z m++p
  change c++(wordPow z m++(p++wordPow c n))=(wordPow z m++(p++wordPow c n))++c
  have h : c++wordPow c n=wordPow c n++c := by rw [←wordPow_succ',wordPow_succ]
  calc _ = (c++v)++wordPow c n := by simp [v,List.append_assoc]
       _ = (v++c)++wordPow c n := by rw [show c++v=v++c from comm]
       _ = v++(wordPow c n++c) := by rw [List.append_assoc,h]
       _ = _ := by simp [v,List.append_assoc]

private def swapLast : Option Bool → Option Bool
  | none => some true
  | some true => none
  | some false => some false

private theorem cut_completion [Fintype A] (p q z : Word A) (n i j e : ℕ)
    (diff : (short p q n).head?≠z.head?)
    (comm : (q++p)++(wordPow z (e+1)++p)=(wordPow z (e+1)++p)++(q++p))
    (code : NamedCode (family p q z n i (j+1))) : Completable (family p q z n i (j+1)) := by
  let x := short p q n
  let y := (wordPow x (i+1)++(q++p))++wordPow x (j+1)
  let g := addToken (pair x z) y
  have inj : Function.Injective swapLast := by decide
  have toOld : (fun t => g (swapLast t))=family p q z n i (j+1) := by
    funext t; rcases t with _ | (_ | _) <;> rfl
  have fromOld : (fun t => family p q z n i (j+1) (swapLast t))=g := by
    funext t; rcases t with _ | (_ | _) <;> rfl
  have cg : NamedCode g := fromOld ▸ code.reindex inj
  have done := commuting_at_right_cut x z (q++p) (i+1) j e diff
    (commutes_with_short p q z _ n comm) cg
  exact toOld ▸ done.reindex inj

private theorem ambiguity_at_center (p q z : Word A) (n m : ℕ)
    (comm : (q++p)++(wordPow z m++p)=(wordPow z m++p)++(q++p)) :
    ¬NamedCode (family p q z n 0 0) := by
  let x := short p q n
  let c := q++p
  let t := wordPow z m++x
  have ct : c++t=t++c := commutes_with_short p q z _ n comm
  let names := List.replicate m (none : Option Bool)
  let v := family p q z n 0 0
  let left := names++[some false]
  let right := names++[some true]
  have hL : spell v left=t := by simp [v,left,names,family,addToken,pair,spell_replicate,t,x]
  have hR : spell v right=t++c := by
    simp [v,right,names,family,addToken,pair,spell_replicate,t,x,c,List.append_assoc]
  intro code
  have h := code (show spell v (left++right)=spell v (right++left) by
    rw [spell_append v left right,spell_append v right left,hL,hR,List.append_assoc t c t,ct])
  simp [left,right,List.append_assoc] at h

/-- Section 4's forbidden identity, over any finite alphabet. If the two
end letters differ in each direction, the identity forces a completion of
every coded triple in the border form. The index e encodes a positive power. -/
theorem forbidden_identity [Fintype A] (p q z : Word A) (n i j e : ℕ)
    (initial : (short p q n).head?≠z.head?) (final : (short p q n).reverse.head?≠z.reverse.head?)
    (comm : (q++p)++(wordPow z (e+1)++p)=(wordPow z (e+1)++p)++(q++p))
    (code : NamedCode (family p q z n i j)) : Completable (family p q z n i j) := by
  cases j with
  | succ j => exact cut_completion p q z n i j e initial comm code
  | zero =>
    cases i with
    | zero => exact (ambiguity_at_center p q z n (e+1) comm code).elim
    | succ i =>
      have eqn := family_reverse p q z n (i+1) 0
      have rev := cut_completion p.reverse q.reverse z.reverse n 0 i e
        (short_reverse p q n ▸ final) (reverse_identity p q z _ comm) (eqn ▸ code.reverse)
      simpa using (show Completable (fun k => (family p q z n (i+1) 0 k).reverse) from eqn.symm ▸ rev).reverse

end ThreeWordCodes.Border
