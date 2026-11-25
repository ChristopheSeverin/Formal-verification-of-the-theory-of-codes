module

public import ThreeWordCodes.BlockReading

/-! # Equal blocks between short gaps (Lemma 3) -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private theorem first_short {g : List ℕ} {n : ℕ} (h : ∃ x ∈ g, x < n) :
    ∃ H c r, (∀ z ∈ H, n ≤ z) ∧ c < n ∧ g = H ++ c::r := by
  induction g with
  | nil => simp at h
  | cons x g ih =>
    by_cases small : x < n
    · exact ⟨[],x,g,by simp,small,rfl⟩
    · obtain ⟨z,hz,sz⟩ := h
      rcases List.mem_cons.mp hz with rfl | hz
      · contradiction
      obtain ⟨H,c,r,ok,s,he⟩ := ih ⟨z,hz,sz⟩
      exact ⟨x::H,c,r,by rw [List.forall_mem_cons]; exact ⟨by omega,ok⟩,s,congrArg (x :: ·) he⟩

private theorem first_short_unique {n c d : ℕ} {H L r s : List ℕ}
    (long : ∀ x ∈ H, n ≤ x) (other : ∀ x ∈ L, n ≤ x)
    (hc : c < n) (hd : d < n) (he : H ++ c::r = L ++ d::s) :
    H = L ∧ c = d ∧ r = s := by
  induction H generalizing L with
  | nil =>
    cases L with
    | nil => exact ⟨rfl,List.cons.inj he⟩
    | cons y L =>
      have e := (List.cons.inj he).1
      have bound := other y (by simp)
      omega
  | cons x H ih =>
    have bx := long x (by simp)
    cases L with
    | nil =>
      have e := (List.cons.inj he).1
      omega
    | cons y L =>
      obtain ⟨rfl,tail⟩ := List.cons.inj he
      obtain ⟨rfl,rest⟩ := ih (fun z hz => long z (by simp [hz])) (fun z hz => other z (by simp [hz])) tail
      exact ⟨rfl,rest⟩

private theorem period_at_short {i j c : ℕ} {g H r : List ℕ}
    (bad : ¬ NamedCode (layout i [] j 0 g 0)) (hg : g = H ++ c::r)
    (long : ∀ x ∈ H, i+j ≤ x) (small : c < i+j) : r <+: g := by
  obtain ⟨L,d,t,good,⟨s,hs⟩⟩ := BlockReading.overlap_witness bad
    ⟨c,by rw [hg]; simp,small⟩
  have aligned : H ++ c :: (r++s) = L ++ d :: (g++t) := by simpa [hg,List.append_assoc] using hs
  have ds : d < i+j := by
    by_contra! large
    have next : H ++ c :: (r++s) = (L ++ d::H) ++ c :: (r++t) := by
      simpa [hg,List.append_assoc] using aligned
    have longNext : ∀ x ∈ L ++ d::H, i+j ≤ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact good x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact large
        · exact long x hx
    have impos := congrArg List.length (first_short_unique long longNext small small next).1
    simp at impos
    omega
  obtain ⟨_,_,eqn⟩ := first_short_unique long good small ds aligned
  apply List.prefix_of_prefix_length_le (show r <+: g++t from ⟨s,eqn⟩) (List.prefix_append g t)
  rw [hg,List.length_append,List.length_cons]
  omega

private theorem periodic_prefix (block tail : Word ℕ) (ne : block ≠ []) (pr : tail <+: block++tail) :
    ∃ k r, block++tail = wordPow block (k+1) ++ r ∧ r <+: block ∧ r.length < block.length := by
  induction len : tail.length using Nat.strong_induction_on generalizing tail with
  | ind n ih =>
    by_cases small : tail.length < block.length
    · exact ⟨0,tail,by simp, List.prefix_of_prefix_length_le pr (List.prefix_append block tail) small.le, small⟩
    · have start := List.prefix_of_prefix_length_le (List.prefix_append block tail) pr (Nat.le_of_not_gt small)
      obtain ⟨suffix,rfl⟩ := start
      have shorter : suffix.length < n := by
        have := List.length_pos_iff.mpr ne
        simp at len
        omega
      have sub : suffix <+: block++suffix := (List.prefix_append_right_inj block).mp pr
      obtain ⟨k,r,eqn,p,bound⟩ := ih _ shorter suffix sub rfl
      refine ⟨k+1,r,?_,p,bound⟩
      rw [wordPow_succ' block (k+1),List.append_assoc,←eqn]

private theorem blocks_one_direction {i j c : ℕ} {g H t : List ℕ}
    (bad : ¬ NamedCode (layout i [] j 0 g 0)) (eqn : g = H ++ c::t)
    (long : ∀ z ∈ H, i+j ≤ z) (small : c < i+j) :
    ∃ k r s, g = wordPow (H++[c]) (k+1) ++ r ∧ r <+: H ∧ g.reverse = r.reverse ++ c::s := by
  have pr := period_at_short bad eqn long small
  have same : g = (H++[c]) ++ t := by simpa [List.append_assoc] using eqn
  obtain ⟨k,r,form,p,bound⟩ := periodic_prefix (H++[c]) t (by simp) (same ▸ pr)
  have sub : r <+: H := List.prefix_of_prefix_length_le p (List.prefix_append H [c]) (by simp at bound; omega)
  have last := same.trans form
  refine ⟨k,r,H.reverse ++ (wordPow (H++[c]) k).reverse,last,sub,?_⟩
  rw [last,wordPow_succ]
  simp [List.append_assoc]

/-- If a short gap occurs, all short gaps have the same length c, and every
block between them, including both end blocks, is the same list H. The number
of short gaps is k+1. The threshold is the sum of the singleton's margins. -/
theorem short_gap_blocks {i j : ℕ} {g : List ℕ}
    (bad : ¬ NamedCode (layout i [] j 0 g 0)) (short : ∃ z ∈ g, z < i+j) :
    ∃ H : List ℕ, ∃ c k : ℕ, c < i+j ∧ (∀ z ∈ H, i+j ≤ z) ∧
      g = H ++ wordPow (c::H) (k+1) := by
  obtain ⟨H,c,t,long,small,eqn⟩ := first_short short
  obtain ⟨k,r,s,form,sub,rev⟩ := blocks_one_direction bad eqn long small
  have badRev : ¬ NamedCode (layout j [] i 0 g.reverse 0) := by
    intro hr
    apply bad
    have same : (fun x => (layout j [] i 0 g.reverse 0 x).reverse) = layout i [] j 0 g 0 := by
      funext x
      rcases x with _ | (_ | _) <;> simp [layout,addToken,pair,reverse_mixed]
    exact same ▸ hr.reverse
  have rLong (x : ℕ) (hx : x ∈ r.reverse) : j+i ≤ x := by
    have := long x (sub.sublist.subset (List.mem_reverse.mp hx))
    omega
  obtain ⟨_,r',s',_,sub',again⟩ := blocks_one_direction badRev rev rLong (by omega)
  rw [List.reverse_reverse] at again
  have r'Long (x : ℕ) (hx : x ∈ r'.reverse) : i+j ≤ x := by
    have := rLong x (sub'.sublist.subset (List.mem_reverse.mp hx))
    omega
  have matchHeads := (first_short_unique long r'Long small small (eqn.symm.trans again)).1
  have same : r = H := sub.eq_of_length_le (by
    have one := congrArg List.length matchHeads
    have two := sub'.length_le
    simp only [List.length_reverse] at one two
    omega)
  refine ⟨H,c,k,small,long,?_⟩
  rw [form,same]
  exact rotate_power H [c] (k+1)

end ThreeWordCodes.BinaryGaps
