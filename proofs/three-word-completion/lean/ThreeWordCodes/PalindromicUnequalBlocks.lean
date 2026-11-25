module

public import ThreeWordCodes.PalindromicBlockRuns
public import ThreeWordCodes.PurePowerTheorem

/-! # Distinct blocks at the minimum gap -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem only_initial_run {s k l m : ℕ} {F : List ℕ} {other : List (List ℕ)} {z : Word Bool}
    (read : Reading s (joinBlocks m (F::other)) z) (bound : max k l≤m) (short : m≤k+l) (ne : F≠[])
    (long : ∀ B∈F::other,∀ n∈B,m<n) (top : ∀ B∈F::other,blockWeight B≤blockWeight F)
    (ending : z.getLast?=some b) (fail : ¬Completable (triple s k l z)) :
    ∃ n, List.replicate n F <+: F::other ∧ ∀ pre tail,F::other=pre++(List.replicate n F++tail) → pre=[] := by
  obtain ⟨n,rs,eqn,valid⟩ := BlockRuns.decompose F (F::other)
  have nz : n≠0 := by
    rintro rfl
    cases rs with
    | nil => simp at eqn
    | cons e rs =>
      rcases e with ⟨x,j⟩
      exact valid (x,j) (by simp) ((List.cons.inj eqn).1.symm)
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nz
  have small : ∀ e∈rs,e.1≠F ∧ e.2<r+1 := by
    intro e he
    refine ⟨valid e he,?_⟩
    by_contra! big
    obtain ⟨past,D,later,neD,bounds,inB,cut⟩ := return_layout m F r rs valid ⟨e,he,big⟩
    apply fail
    apply block_run_completion s k l m F D r past later z neD ne bound short bounds
    · intro B hb; exact long B (eqn.symm ▸ inB B hb)
    · intro B hb; exact top B (eqn.symm ▸ inB B hb)
    · intro n hn
      have empty := blocks_lower m _ long n (by rw [eqn,cut]; exact hn)
      omega
    · rwa [eqn,cut] at read
    · exact ending
  refine ⟨r+1,⟨_,eqn.symm⟩,?_⟩
  intro pre tail position
  exact BlockRuns.initial_run (Nat.succ_pos _) rs small pre tail (eqn.symm.trans position)

/-- A counterexample with a maximum block F has F at the start, and its
initial run of F's can occur only there. -/
private theorem one_side {s k l m : ℕ} (first F : List ℕ) (other : List (List ℕ)) {z : Word Bool}
    (read : Reading s (joinBlocks m (first::other)) z) (bound : max k l≤m) (short : m≤k+l)
    (ne : F≠[]) (mem : F∈first::other) (long : ∀ B∈first::other,∀ n∈B,m<n)
    (top : ∀ B∈first::other,blockWeight B≤blockWeight F)
    (code : NamedCode (triple s k l z)) (fail : ¬Completable (triple s k l z)) :
    ∃ n,List.replicate n F <+: first::other ∧ ∀ pre tail,first::other=pre++(List.replicate n F++tail) → pre=[] := by
  have last := (residual_word code fail).2.1
  by_cases head : first=F
  · subst first
    exact only_initial_run read bound short ne long top last fail
  · exact (fail (first_maximum_completion s k l m first F other [] z (by simpa using read) (by simp)
      (by omega) short ne head mem long top last)).elim

/-- Any two distinct blocks between or outside occurrences of the minimum
suffice. Choosing opposite orientations forces incompatible lengths of the
initial runs of a maximum block. -/
theorem unequal_blocks_completion (s k l m : ℕ) (first last : List ℕ) (middle : List (List ℕ)) (z : Word Bool)
    (read : Reading s (joinBlocks m (first::(middle++[last]))) z) (bound : max k l≤m) (short : m≤k+l)
    (long : ∀ B∈first::(middle++[last]),∀ n∈B,m<n) (varied : ∃ B∈first::(middle++[last]),B≠first)
    (code : NamedCode (triple s k l z)) : Completable (triple s k l z) := by
  by_contra bad
  let bs := first::(middle++[last])
  let rev := last.reverse::(middle.reverse.map List.reverse ++ [first.reverse])
  have back : bs.reverse.map List.reverse=rev := by simp [bs,rev]
  have back' : rev.reverse.map List.reverse=bs := by simp [rev,bs,List.map_reverse,List.map_map]
  have members {B : List ℕ} : B∈rev ↔ B.reverse∈bs := by
    rw [←back,List.mem_map]
    constructor
    · rintro ⟨Q,hQ,rfl⟩; simpa using hQ
    · intro hQ; exact ⟨B.reverse,by simpa using hQ,List.reverse_reverse _⟩
  obtain ⟨F,hF,maxF⟩ := Finset.exists_max_image bs.toFinset blockWeight (by simp [bs])
  have mem := List.mem_toFinset.mp hF
  have top (B : List ℕ) (hb : B∈bs) := maxF B (List.mem_toFinset.mpr hb)
  obtain ⟨B,inB,bne⟩ := varied
  obtain ⟨D,dIn,different⟩ : ∃ D∈bs,D≠F := by
    by_cases same : first=F
    · exact ⟨B,inB,same ▸ bne⟩
    · exact ⟨first,by simp [bs],same⟩
  have ne : F≠[] := by
    rintro rfl
    have w := top D dIn
    simp [blockWeight] at w
    exact different w.2
  obtain ⟨n,starts,only⟩ := one_side first F _ read bound short ne mem long top code bad
  have revRead : Reading s (joinBlocks m rev) z.reverse := by
    have rr : Reading s (joinBlocks m bs).reverse z.reverse := read.reverse
    rwa [reverse_blocks,back] at rr
  obtain ⟨q,ends',only'⟩ := one_side last.reverse F.reverse _ revRead (by omega) (by omega) (by simpa using ne)
    (members.mpr (by simpa using mem))
    (fun P hp t ht => long P.reverse (members.mp hp) t (by simpa using ht))
    (fun P hp => by simpa using top P.reverse (members.mp hp))
    (triple_reverse s k l z ▸ code.reverse) (fun done => bad (flip_back done))
  rcases le_total n q with dir | dir
  · exact incompatible_runs F bs n q dir (back.symm ▸ ends') only ⟨D,dIn,different⟩
  · have rows : List.replicate n F.reverse.reverse <+: rev.reverse.map List.reverse := by
      rw [back',List.reverse_reverse]; exact starts
    exact incompatible_runs F.reverse rev q n dir rows only'
      ⟨D.reverse,members.mpr (by simpa using dIn),by simpa using different⟩

end ThreeWordCodes.Palindromic
