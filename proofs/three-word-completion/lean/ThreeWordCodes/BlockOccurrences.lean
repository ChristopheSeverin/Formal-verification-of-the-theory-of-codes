module

public import ThreeWordCodes.BoundaryReduction
public import ThreeWordCodes.PatternGraft

/-! # Locating consecutive maximum blocks inside a selected leaf -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

/-- A maximum nonempty block cannot occur strictly inside another block.
Writing this as an infix condition makes it invariant under gap recoding. -/
def RecognizesBlock (F : List ℕ) (blocks : List (List ℕ)) : Prop :=
  ∀ B∈blocks, F <:+: B → B=F

theorem recognizes_of_weight {F : List ℕ} {blocks : List (List ℕ)}
    (upper : ∀ B∈blocks,blockWeight B≤blockWeight F) : RecognizesBlock F blocks := by
  rintro B hb ⟨pre,tail,eqn⟩
  have le := upper B hb
  rw [←eqn] at le
  simp [blockWeight] at le
  have p : pre=[] := List.length_eq_zero_iff.mp (by omega)
  have t : tail=[] := List.length_eq_zero_iff.mp (by omega)
  simpa [p,t] using eqn.symm

/-- The two sides of a maximum block in the literal gap list uniquely place
the two cuts at block boundaries. -/
theorem locate_one (m : ℕ) (F : List ℕ) (blocks : List (List ℕ)) (pre tail : List ℕ)
    (fresh : m∉F) (nonempty : F≠[]) (recognize : RecognizesBlock F blocks)
    (found : separated m blocks=pre++(F++tail)) :
    ∃ left right, blocks=left++F::right ∧ pre=separated m left ∧ tail=m::separated m right := by
  induction blocks generalizing pre tail with
  | nil =>
    have eqn : pre++(F++tail)=[] := found.symm
    exact (nonempty (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp eqn).2).1).elim
  | cons B bs ih =>
    rw [separated_cons] at found
    rcases List.append_eq_append_iff.mp found with ⟨v,cut,body⟩ | ⟨v,cut,body⟩
    · cases v with
      | nil =>
        have pr : F <+: ([] : List ℕ)++m::separated m bs := ⟨tail,body.symm⟩
        exact (nonempty (List.eq_nil_of_prefix_nil (prefix_before_marker fresh pr))).elim
      | cons n t =>
        obtain ⟨rfl,remaining⟩ := List.cons.inj body
        obtain ⟨left,right,split,ep,et⟩ := ih t tail
          (fun B hb => recognize B (by simp [hb])) remaining
        exact ⟨B::left,right,by rw [split]; rfl,by rw [cut,ep,separated_cons],et⟩
    · have fit : F <+: v := prefix_before_marker fresh (show F <+: v++m::separated m bs from ⟨tail,body⟩)
      obtain ⟨after,eqn⟩ := fit
      have exactB := recognize B (by simp) ⟨pre,after,by simp only [List.append_assoc,eqn,cut]⟩
      have lens := congrArg List.length ((cut.trans (congrArg (pre++·) eqn.symm)).symm.trans exactB)
      simp only [List.length_append] at lens
      have leftNil : pre=[] := List.length_eq_zero_iff.mp (by omega)
      have rightNil : after=[] := List.length_eq_zero_iff.mp (by omega)
      subst pre after
      have ev : v=F := by simpa using eqn.symm
      subst B
      exact ⟨[],bs,rfl,rfl,List.append_cancel_left (by simpa only [ev] using body : F++tail=F++m::separated m bs)⟩

/-- A run of r+1 copies of the chosen block, omitting the final separator. -/
def blockPattern (m : ℕ) (F : List ℕ) (r : ℕ) : List ℕ := F++wordPow (m::F) r

theorem locate_block_pattern (m : ℕ) (F : List ℕ) (r : ℕ) (blocks : List (List ℕ)) (pre tail : List ℕ)
    (fresh : m∉F) (nonempty : F≠[]) (recognize : RecognizesBlock F blocks)
    (found : separated m blocks=pre++(blockPattern m F r++tail)) :
    ∃ left right, blocks=left++(List.replicate (r+1) F++right) ∧ pre=separated m left := by
  induction r generalizing blocks pre tail with
  | zero =>
    obtain ⟨left,right,split,ep,_⟩ := locate_one m F blocks pre tail fresh nonempty recognize
      (by simpa [blockPattern] using found)
    exact ⟨left,right,by simpa using split,ep⟩
  | succ r ih =>
    have shape : blockPattern m F (r+1)=F++m::blockPattern m F r := by
      simp [blockPattern,wordPow_succ']
    obtain ⟨left,more,step,ep,et⟩ := locate_one m F blocks pre (m::(blockPattern m F r++tail))
      fresh nonempty recognize (by simpa [shape,List.append_assoc] using found)
    obtain ⟨l1,r1,extra,start⟩ := ih more [] tail (fun B hb => recognize B (by simp [step,hb]))
      (by simpa using (List.cons.inj et).2.symm)
    have nil : l1=[] := by
      cases l1 with
      | nil => rfl
      | cons b bs => simp at start
    subst l1
    exact ⟨left,r1,by rw [step,extra,List.replicate_succ]; rfl,ep⟩

/-- A literal occurrence of the run can only start at the root when the
corresponding run of block names can only start at the root. -/
theorem pattern_starts_at_root (m : ℕ) (F : List ℕ) (r : ℕ) (blocks : List (List ℕ))
    (fresh : m∉F) (nonempty : F≠[]) (recognize : RecognizesBlock F blocks)
    (single : ∀ pre tail, blocks=pre++(List.replicate (r+1) F++tail) → pre=[]) :
    OccursOnlyInitially (blockPattern m F r) (separated m blocks) := by
  intro pre tail found
  obtain ⟨left,right,whereAt,loc⟩ := locate_block_pattern m F r blocks pre tail fresh nonempty recognize found
  rw [loc,single left right whereAt,separated_nil]

end ThreeWordCodes.BinaryGaps
