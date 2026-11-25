module

public import ThreeWordCodes.MinimumBlocks

/-! # First occurrence of a maximum-weight long block -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

/-- Write a separator after each block, including after an empty block. -/
def separated (m : ℕ) (blocks : List (List ℕ)) := blocks.flatMap (fun B => B++[m])

@[simp] theorem separated_nil (m : ℕ) : separated m [] = [] := rfl
@[simp] theorem separated_cons (m : ℕ) (B : List ℕ) (bs : List (List ℕ)) :
    separated m (B::bs) = B ++ m :: separated m bs := by simp [separated,List.append_assoc]
@[simp] theorem separated_append (m : ℕ) (bs cs : List (List ℕ)) :
    separated m (bs++cs) = separated m bs ++ separated m cs := by simp [separated]
@[simp] theorem separated_singleton (m : ℕ) (P : List ℕ) : separated m [P] = P++[m] := by simp [separated]

theorem prefix_before_marker {P U V : List ℕ} {m : ℕ} (fresh : m∉P)
    (pr : P <+: U++m::V) : P <+: U := by
  induction U generalizing P with
  | nil =>
    rcases List.prefix_cons_iff.mp pr with rfl | ⟨s,rfl,_⟩
    · rfl
    · exact (fresh (by simp)).elim
  | cons z U ih =>
    rcases List.prefix_cons_iff.mp pr with rfl | ⟨s,rfl,sp⟩
    · exact List.nil_prefix
    · exact List.cons_prefix_cons.mpr ⟨rfl,ih (by simpa using (fun h => fresh (List.mem_cons_of_mem z h))) sp⟩

private theorem infix_before_or_after {P U V : List ℕ} {m : ℕ} (fresh : m∉P)
    (present : P <:+: U++m::V) : P <:+: U ∨ P <:+: V := by
  induction U with
  | nil =>
    rcases List.infix_cons_iff.mp present with start | later
    · exact Or.inl (prefix_before_marker (U:=[]) fresh start).isInfix
    · exact Or.inr later
  | cons z U ih =>
    rcases List.infix_cons_iff.mp present with start | later
    · exact Or.inl (prefix_before_marker (U:=z::U) fresh start).isInfix
    · rcases ih later with left | right
      · exact Or.inl (List.infix_cons_iff.mpr (Or.inr left))
      · exact Or.inr right

theorem infix_in_block {P : List ℕ} {m : ℕ} (fresh : m∉P) (nonempty : P≠[])
    (blocks : List (List ℕ)) (present : P <:+: separated m blocks) :
    ∃ B∈blocks, P <:+: B := by
  induction blocks with
  | nil => exact (nonempty (by simpa [separated] using present)).elim
  | cons B bs ih =>
    rw [separated_cons] at present
    rcases infix_before_or_after fresh present with left | right
    · exact ⟨B,by simp,left⟩
    · obtain ⟨C,hc,inc⟩ := ih right
      exact ⟨C,by simp [hc],inc⟩

private theorem align_maximum {B tail : List ℕ} {z n : ℕ}
    (present : z::tail <:+: B) (le : n≤z) (size : blockWeight B ≤ blockWeight (n::tail)) :
    B=n::tail := by
  obtain ⟨pre,after,eqn⟩ := present
  rw [←eqn] at size
  have bounds : pre.sum+pre.length+after.sum+after.length+z ≤ n := by
    simp [blockWeight] at size
    omega
  have preZero : pre=[] := List.length_eq_zero_iff.mp (by omega)
  have afterZero : after=[] := List.length_eq_zero_iff.mp (by omega)
  have same : z=n := by omega
  simpa [same,preZero,afterZero] using eqn.symm

/-- At the first occurrence of a block of greatest weight, choose the single
prefix ending at its preceding separator. Any number of earlier long blocks
is allowed, including ties of equal weight with different contents. The
continuation after the chosen long block is arbitrary. -/
theorem maximum_block_completion (k h m n : ℕ) (earlier : List (List ℕ)) (prev tail later : List ℕ)
    (pos : 0<h) (low : h≤m) (short : m<k+h) (long : m<n) (above : ∀ x∈tail,m<x)
    (base : ∀ B∈earlier++[prev], ∀ x∈B,h≤x) (after : ∀ x∈later,h≤x)
    (weight : ∀ B∈earlier++[prev], blockWeight B ≤ blockWeight (n::tail))
    (first : n::tail ∉ earlier++[prev]) :
    Completable (oneMarker k h (mixed 0 (separated m (earlier++[prev]) ++ (n::tail) ++ later) 0)) := by
  let front := separated m earlier ++ prev
  have rawCut : front++[m] = separated m (earlier++[prev]) := by simp [front,List.append_assoc]
  have earlierLow : ∀ xs : List (List ℕ), (∀ B∈xs,∀ x∈B,h≤x) → ∀ x∈separated m xs,h≤x := by
    intro xs all x mem
    obtain ⟨B,hb,hx⟩ := List.mem_flatMap.mp mem
    rcases List.mem_append.mp hx with inB | isM
    · exact all B hb x inB
    · exact (List.mem_singleton.mp isM) ▸ low
  have frontLow (x : ℕ) (mem : x∈front) : h≤x := by
    apply earlierLow _ base x
    rw [←rawCut]
    simp [mem]
  let f := front.map (·-h)
  let L := tail.map (·-h)
  let R := later.map (·-h)
  have ef : f.map (h+·)=front := restore_offset h front frontLow
  have el : L.map (h+·)=tail := restore_offset h tail (fun x hx => low.trans (above x hx).le)
  have er : R.map (h+·)=later := restore_offset h later after
  have hm := Nat.add_sub_of_le low
  have hn := Nat.add_sub_of_le (low.trans long.le)
  have result := fresh_block_certificate h (m-h) (n-h) f L R pos (by omega) (by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    have := above v hv
    omega) (by
    intro pre z post eqn bound
    have raw := congrArg (List.map (h+·)) eqn
    simp only [List.map_append,List.map_cons,List.map_nil,ef,el,hm] at raw
    rw [rawCut] at raw
    have start : n≤h+z := by omega
    have all := infix_in_block (P:= (h+z)::tail) (m:=m)
      (by simp only [List.mem_cons,not_or]; exact ⟨by omega,fun bad => Nat.lt_irrefl _ (above m bad)⟩)
      (by simp) (earlier++[prev]) ⟨_,_,by simpa only [List.append_assoc,List.cons_append] using raw.symm⟩
    obtain ⟨B,mem,occurs⟩ := all
    exact first (align_maximum occurs start (weight B mem) ▸ mem))
  have form : ((f++[m-h])++(n-h)::(L++R)).map (h+·) =
      separated m (earlier++[prev]) ++ (n::tail) ++ later := by
    simp only [List.map_append,List.map_cons,List.map_nil,ef,el,er,hm,hn,←rawCut,List.append_assoc,List.cons_append]
  rw [form] at result
  exact raise_left_margin (by simp) (show m-h+1≤k by omega) result

end ThreeWordCodes.BinaryGaps
