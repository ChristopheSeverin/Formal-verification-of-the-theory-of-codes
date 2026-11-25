module

public import ThreeWordCodes.PalindromicEqualBlocks
public import ThreeWordCodes.PalindromicUnequalBlocks

/-! # Proposition 7 of the manuscript -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

/-- All blocks at the minimum either agree or admit the returning-run graft
in one of the two orientations. -/
theorem common_gap_construction : CommonGapConstruction := by
  intro s k l z ns size read high small code
  let D := ns.toFinset
  have nonempty : D.Nonempty := by
    obtain ⟨v,mem,_⟩ := small
    exact ⟨v,List.mem_toFinset.mpr mem⟩
  let m := D.min' nonempty
  have atM : m∈ns := List.mem_toFinset.mp (Finset.min'_mem D nonempty)
  have least (n : ℕ) (mem : n∈ns) : m≤n := Finset.min'_le D n (List.mem_toFinset.mpr mem)
  have bound := high m atM
  obtain ⟨v,hit,vs⟩ := small
  have short := (least v hit).trans vs
  obtain ⟨first,bs,shape,absent⟩ := split_at m ns
  have more : bs≠[] := by
    rintro rfl
    exact absent first (by simp) (by simpa [shape,joinBlocks] using atM)
  have long (B : List ℕ) (hb : B∈first::bs) (n : ℕ) (hn : n∈B) : m<n := by
    have below := least n (shape.symm ▸ block_mem _ hb hn)
    have different : n≠m := fun e => absent B hb (e ▸ hn)
    omega
  by_cases uniform : ∀ B∈bs,B=first
  · obtain ⟨j,rep⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (List.length_pos_iff.mpr more))
    have word := shape.trans (flat_equal_blocks m first bs uniform)
    rw [rep] at word
    exact equal_blocks_completion s k l m first j z (word ▸ read) bound short (long first (by simp))
      (fun n hn => (Nat.le_max_right k l).trans (high n (word.symm ▸ hn))) code
  · push Not at uniform
    obtain ⟨B,inB,diff⟩ := uniform
    let mid := bs.dropLast
    let last := bs.getLast more
    have split : mid++[last]=bs := List.dropLast_concat_getLast more
    exact unequal_blocks_completion s k l m first last mid z (by rwa [split,←shape]) bound short
      (by rw [split]; exact long) ⟨B,by rw [split]; simp [inB],diff⟩ code

/-- Every three-word code of Proposition 7 has a finite maximal positive
completion. The three natural number arguments of triple are zero-based. -/
theorem proposition_seven : PropositionSeven := proposition_seven_iff_common_gaps.mpr common_gap_construction

/-- The statement with the positive exponents of the manuscript and the
three literal input words. -/
theorem palindromic_completion (s k l : ℕ) (z : Word Bool)
    (hs : 0<s) (hk : 0<k) (hl : 0<l) :
    let X := wordPow [a,b] s ++ [a]
    let Y := wordPow X k ++ [b,a] ++ wordPow X (l-1)
    let words := addToken (pair X Y) z
    NamedCode words → HasPositiveCompletion (Set.range words) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  intro X Y words code
  exact (proposition_seven s k l z code).2

end ThreeWordCodes.Palindromic
