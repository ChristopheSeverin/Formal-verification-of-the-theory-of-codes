module

public import ThreeWordCodes.PalindromicGraft
public import ThreeWordCodes.FirstShortGap

/-! # A strictly larger gap after the first cut -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem signed_first_cut (s h d : ℕ) (tail : Word Bool) :
    let C := c++wordPow (x s) h
    let U := wordPow (x s) d
    HasFiniteCertificate ({x s,y s d h,C++U++C++U++a::tail} : Set (Word Bool)) := by
  let C := c++wordPow (x s) h
  let U := wordPow (x s) d
  let v := readers s h
  let cut := b::endC a b d
  let E := [[a],a::endC a b d,cut]
  let t := U++a::tail
  have va : v a=x s := rfl
  have vb : v b=C := rfl
  have mem (u : Word Bool) : u∈E ↔ u∈firstCutLeaves a b d := by simp [E,cut,firstCutLeaves]
  have node (q : Word Bool) (hq : q∈SelectedGraft.nodes E) : q∈suffixNodes (firstCutLeaves a b d) := by
    apply mem_suffixNodes.mpr
    exact (SelectedGraft.mem_nodes.mp hq).imp id (fun ⟨u,hu,hp,ne⟩ => ⟨u,(mem u).mp hu,hp,ne⟩)
  have endImage (m : ℕ) : spell v (endC a b m)=wordPow (x s) m ++ C := by
    simp [endC,spell_replicate,va,vb]
  have nt : t≠[] := by simp [t]
  have apart (r : ℕ) (le : r≤d) : ¬Comparable t (wordPow (x s) r ++ C) := by
    obtain ⟨e,eqn⟩ := Nat.exists_eq_add_of_le le
    have before : ∃ z,wordPow (x s) e++a::tail=a::z := by
      cases e with
      | zero => exact ⟨_,rfl⟩
      | succ e =>
        obtain ⟨after,form⟩ := x_head s
        rw [wordPow_succ',form]
        exact ⟨_,rfl⟩
    obtain ⟨z,zz⟩ := before
    have start : t = wordPow (x s) r ++ a::z := by
      simp only [t,U,eqn,wordPow_add,List.append_assoc,zz]
    rw [start]
    rintro (⟨u,form⟩ | ⟨u,form⟩) <;> simp [List.append_assoc,C,c,a,b] at form
  have ok : SelectedGraft.Valid v E cut t := by
    refine ⟨by simp [E,cut],by simp [E],nt,?_,?_⟩
    · exact fun u hu w hw => firstCutSuffixFree a b d (by decide) u ((mem u).mp hu) w ((mem w).mp hw)
    · intro q hq
      rcases firstCutNode a b d q (node q hq) with rfl | ⟨r,le,rfl⟩
      · exact ⟨Ne.symm nt,fun _ => by simp [E]⟩
      · rw [endImage]
        exact ⟨fun e => apart r le (Or.inl (e ▸ List.prefix_refl _)),fun cp => (apart r le cp).elim⟩
  obtain ⟨hi,nz,pf⟩ := reader_prefix s h
  have result := SelectedGraft.certificate v hi nz pf E cut t ok
  apply result.mono
  rintro _ (rfl | rfl | rfl)
  · right
    exact ⟨[a],⟨by simp [E],by rintro ⟨u,e⟩; exact Bool.noConfusion (List.cons.inj e).1⟩,by simp [va]⟩
  · right
    exact ⟨a::endC a b d,⟨by simp [E],by rintro ⟨u,e⟩; exact Bool.noConfusion (List.cons.inj e).1⟩,
      by simp [va,endImage,wordPow_succ' (x s) d,y,C,List.append_assoc]⟩
  · left
    simp [cut,vb,endImage,t,U,C,List.append_assoc]

/-- If z begins with two copies of ba x^n followed by a, a single graft
completes the triple whenever n ≤ k+l (using the zero-based parameters). -/
theorem initial_rise_completion (s k l n : ℕ) (z : Word Bool) (small : n≤k+l)
    (starts : (c++wordPow (x s) n) ++ (c++wordPow (x s) n) ++ [a] <+: z) :
    Completable (triple s k l z) := by
  let h := min n l
  let d := n-h
  have hd : h+d=n := Nat.add_sub_of_le (Nat.min_le_left ..)
  have lh : h≤l := Nat.min_le_right .. 
  have dk : d≤k := by dsimp [d,h]; omega
  obtain ⟨tail,form⟩ := starts
  have g := signed_first_cut s h d tail
  have join : (c++wordPow (x s) h)++wordPow (x s) d=c++wordPow (x s) n := by
    rw [List.append_assoc,←wordPow_add,hd]
  change HasFiniteCertificate ({x s,y s d h,
    (((c++wordPow (x s) h)++wordPow (x s) d)++(c++wordPow (x s) h))++wordPow (x s) d++a::tail} :
      Set (Word Bool)) at g
  have target : (((c++wordPow (x s) h)++wordPow (x s) d)++(c++wordPow (x s) h))++
      wordPow (x s) d++a::tail=z := by
    rw [join,←form]
    simp only [List.append_assoc,List.singleton_append]
    rw [←List.append_assoc (wordPow (x s) h),←wordPow_add,hd]
  rw [target] at g
  apply raise_exponents (from_certificate (z:=z) _ g) k l dk lh
  rw [←form]
  rfl

end ThreeWordCodes.Palindromic
