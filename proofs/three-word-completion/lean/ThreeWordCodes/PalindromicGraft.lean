module

public import ThreeWordCodes.PalindromicRuns

/-! # Completion from an initial or final alternating run

A maximal run of at least two copies of ba can itself serve as the graft leaf.
On the names of x and ba, every nonempty proper suffix that must be tested is
a power of the second name.
-/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

/-- Raise the two exterior exponents in y independently. -/
theorem raise_exponents {s i h : ℕ} {z : Word Bool} (done : Completable (triple s i h z))
    (k l : ℕ) (left : i≤k) (right : h≤l) : Completable (triple s k l z) := by
  let v := triple s i h z
  let pad (n : ℕ) (j : Option Bool) := if j=some true then List.replicate n (some false) else []
  let u := fun j => spell v (pad (k-i) j) ++ v j
  have mid : Completable u := done.padLeft (pad (k-i))
  have form : (fun j => u j ++ spell u (pad (l-h) j)) = triple s k l z := by
    funext j
    rcases j with _ | (_ | _)
    · simp [u,pad,v,triple,addToken]
    · simp [u,pad,v,triple,addToken,pair]
    · simp [u,pad,v,triple,addToken,pair,spell_replicate,y,List.append_assoc]
      have first : k+1=(k-i)+(i+1) := by omega
      have last : l=h+(l-h) := by omega
      rw [first,wordPow_add (x s) (k-i) (i+1),last,wordPow_add (x s) h (l-h)]
      simp [List.append_assoc]
  exact form ▸ mid.padRight (pad (l-h))

private def powerLeaves (n : ℕ) : List (Word Bool) := [[a],[a,b],List.replicate (n+2) b]

/-- The target after a fixed initial run of at least two copies of ba. -/
theorem power_graft (s n : ℕ) (t : Word Bool) (apart : ¬Comparable t c) :
    HasFiniteCertificate ({x s,x s++c,wordPow c (n+2)++t} : Set (Word Bool)) := by
  let v := readers s 0
  let L := List.replicate (n+2) b
  let E := powerLeaves n
  have vb : v b=c := by simp [v,readers,pair,b]
  have va : v a=x s := rfl
  have nt : t≠[] := by rintro rfl; exact apart (Or.inl List.nil_prefix)
  have suffixA : ¬[a] <:+ L := by
    intro pr
    have := pr.sublist.subset (show a ∈ [a] by decide)
    simp [L,a,b] at this
  have suffixAB : ¬[a,b] <:+ L := by
    intro pr
    have := pr.sublist.subset (show a ∈ [a,b] by decide)
    simp [L,a,b] at this
  have suffixL : ¬ L <:+ [a,b] := by
    intro pr
    have bound := pr.sublist.count_le b
    simp [L,a,b] at bound
  have leaf : L∈E := by simp [E,L,powerLeaves]
  have ok : SelectedGraft.Valid v E L t := by
    refine ⟨by simp [E,powerLeaves],leaf,nt,?_,?_⟩
    · intro u hu w hw cmp
      simp only [E,powerLeaves,List.mem_cons,List.not_mem_nil,or_false] at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first | rfl | exact (suffixA cmp).elim | exact (suffixAB cmp).elim | exact (suffixL cmp).elim |
          (exfalso; revert cmp; decide) | (have := cmp.length_le; simp at this)
    · intro q hq
      rcases SelectedGraft.mem_nodes.mp hq with rfl | ⟨e,he,suf,proper⟩
      · exact ⟨Ne.symm nt,fun _ => by simpa using leaf⟩
      have power : ∃ j,q=List.replicate j b := by
        simp only [E,powerLeaves,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨0,List.eq_nil_of_suffix_nil ((List.suffix_cons_iff.mp suf).resolve_left proper)⟩
        · have part := (List.suffix_cons_iff.mp suf).resolve_left proper
          exact ⟨q.length,(List.suffix_replicate_iff.mp (show q <:+ List.replicate 1 b from part)).2⟩
        · exact ⟨q.length,(List.suffix_replicate_iff.mp suf).2⟩
      obtain ⟨j,rfl⟩ := power
      cases j with
      | zero => exact ⟨Ne.symm nt,fun _ => by simpa using leaf⟩
      | succ j =>
        have first : c <+: spell v (List.replicate (j+1) b) := by
          rw [spell_replicate,vb,wordPow_succ']; exact ⟨_,rfl⟩
        have away : ¬Comparable t (spell v (List.replicate (j+1) b)) := by
          rintro (p | p)
          · exact apart (List.prefix_or_prefix_of_prefix p first)
          · exact apart (Or.inr (first.trans p))
        exact ⟨fun e => away (Or.inl (e ▸ List.prefix_refl _)),fun h => (away h).elim⟩
  obtain ⟨inj,nz,pf⟩ := reader_prefix s 0
  have cert := SelectedGraft.certificate v inj nz pf E L t ok
  have noA : ¬ L <+: [a] := by intro pr; have := pr.length_le; simp [L] at this
  have noAB : ¬ L <+: [a,b] := by
    intro pr
    have bound := pr.sublist.count_le b
    simp [L,a,b] at bound
  apply cert.mono
  rintro _ (rfl | rfl | rfl)
  · right; exact ⟨[a],⟨by simp [E,powerLeaves],noA⟩,by simp [va]⟩
  · right; exact ⟨[a,b],⟨by simp [E,powerLeaves],noAB⟩,by simp [va,vb]⟩
  · left; simp [L,spell_replicate,vb]

theorem from_certificate {s k l : ℕ} {z : Word Bool} (start : z.head?=some b)
    (cert : HasFiniteCertificate ({x s,y s k l,z} : Set (Word Bool))) :
    Completable (triple s k l z) := by
  let v := triple s k l z
  have ran : Set.range v ⊆ ({x s,y s k l,z} : Set (Word Bool)) := by
    rintro _ ⟨(_ | (_ | _)),rfl⟩ <;> simp [v,triple,addToken,pair]
  have comp := (cert.mono ran).toPositive
  obtain ⟨u,form⟩ := x_head s
  have yForm : ∃ t, y s k l=a::t := by
    rw [y,wordPow_succ',form]
    exact ⟨_,rfl⟩
  obtain ⟨q,formY⟩ := yForm
  have sepX : x s ≠ z := by intro e; simp [←e,form,a,b] at start
  have sepY : y s k l ≠ z := by intro e; simp [←e,formY,a,b] at start
  have xy : x s ≠ y s k l := by
    intro e
    rw [y,wordPow_succ',List.append_assoc,List.append_assoc] at e
    have eqn := congrArg List.length e
    simp [c] at eqn
  have inj : Function.Injective v := by
    rintro (_ | (_ | _)) (_ | (_ | _)) eqn <;>
      simp_all [v,triple,addToken,pair]
  refine ⟨(namedCode_iff_range _).mpr ⟨inj,?_⟩,comp⟩
  obtain ⟨M,_,_,encl,hm,_⟩ := comp
  exact fun p q hp hq => hm.1 p q (fun w hw => encl (hp w hw)) (fun w hw => encl (hq w hw))

theorem power_graft_completion (s k l n : ℕ) (t : Word Bool) (apart : ¬Comparable t c) :
    Completable (triple s k l (wordPow c (n+2)++t)) := by
  apply raise_exponents (i:=0) (h:=0) _ k l (Nat.zero_le _) (Nat.zero_le _)
  apply from_certificate
  · rw [wordPow_succ']; rfl
  · simpa [y] using power_graft s n t apart

end ThreeWordCodes.Palindromic
