module

public import ThreeWordCodes.BlockOccurrences
public import Mathlib.Data.List.Forall2

/-! # Detecting a maximum block when either endpoint can grow -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

/-- Coordinatewise domination on gap lists of the same length. -/
abbrev Dominated (u v : List ℕ) : Prop := List.Forall₂ (·≤·) u v

theorem Dominated.sum_le {u v : List ℕ} (d : Dominated u v) : u.sum≤v.sum := by
  induction d with
  | nil => simp
  | cons h _ ih => simp only [List.sum_cons]; omega

theorem Dominated.eq_of_sum {u v : List ℕ} (d : Dominated u v) (le : v.sum≤u.sum) : u=v := by
  induction d with
  | nil => rfl
  | @cons a b u v h d ih =>
    have bounds := Dominated.sum_le d
    simp only [List.sum_cons] at le
    rw [show a=b by omega,ih (by omega)]

theorem Dominated.lower {m : ℕ} {u v : List ℕ} (d : Dominated u v) (low : ∀ n∈u,m<n) :
    ∀ n∈v,m<n := by
  induction d with
  | nil => simp
  | cons h d ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | mem
    · exact (low _ (by simp)).trans_le h
    · exact ih (fun z hz => low z (by simp [hz])) n mem

theorem Dominated.split {u v w : List ℕ} (d : Dominated (u++v) w) :
    ∃ x y,w=x++y ∧ Dominated u x ∧ Dominated v y := by
  induction u generalizing w with
  | nil => exact ⟨[],w,rfl,.nil,d⟩
  | cons a u ih =>
    cases d with
    | cons h d =>
      obtain ⟨x,y,rfl,l,r⟩ := ih d
      exact ⟨_::x,y,rfl,.cons h l,r⟩

/-- A demanded maximum block can neither grow nor start or finish strictly
inside a host block. -/
theorem maximum_dominated {m : ℕ} {F W : List ℕ} {bs : List (List ℕ)} (ne : F≠[])
    (above : ∀ n∈F,m<n) (top : ∀ B∈bs,blockWeight B≤blockWeight F) (d : Dominated F W)
    (found : W <:+: separated m bs) : W=F ∧ F∈bs := by
  have long := d.lower above
  have wn : W≠[] := by intro nil; exact ne (List.forall₂_nil_right_iff.mp (nil ▸ d))
  obtain ⟨B,hB,pre,after,whereAt⟩ := infix_in_block (fun hm => Nat.lt_irrefl _ (long m hm)) wn bs found
  have hi := top B hB
  have ls := d.length_eq
  have ss := d.sum_le
  rw [←whereAt] at hi
  simp [blockWeight] at hi
  have pe : pre=[] := List.length_eq_zero_iff.mp (by omega)
  have ae : after=[] := List.length_eq_zero_iff.mp (by omega)
  have eqn := d.eq_of_sum (by omega)
  exact ⟨eqn.symm,by simpa [←whereAt,pe,ae,eqn] using hB⟩

/-- A whole run of maximum blocks remains rigid under coordinatewise
domination. Each copy fills a host block, which also fixes its next separator. -/
theorem dominated_run {m : ℕ} (F : List ℕ) (r : ℕ) (bs : List (List ℕ)) (ne : F≠[])
    (above : ∀ n∈F,m<n) (top : ∀ B∈bs,blockWeight B≤blockWeight F)
    (pre W tail : List ℕ) (whereAt : separated m bs=pre++(W++tail))
    (d : Dominated (blockPattern m F r) W) : W=blockPattern m F r := by
  induction r generalizing pre W with
  | zero =>
    have df : Dominated F W := by simpa [blockPattern] using d
    simpa [blockPattern] using (maximum_dominated ne above top df ⟨pre,tail,by simpa [List.append_assoc] using whereAt.symm⟩).1
  | succ r ih =>
    have pattern : blockPattern m F (r+1)=F++m::blockPattern m F r := by simp [blockPattern,wordPow_succ']
    rw [pattern] at d ⊢
    obtain ⟨P,Q,rfl,hP,hQ⟩ := d.split
    have same : P=F := (maximum_dominated ne above top hP
      ⟨pre,Q++tail,by simpa [List.append_assoc] using whereAt.symm⟩).1
    subst P
    obtain ⟨j,more,_,hR,rfl⟩ := List.forall₂_cons_left_iff.mp hQ
    obtain ⟨_,_,_,_,cut⟩ := locate_one m F bs pre (j::more++tail)
      (fun hm => Nat.lt_irrefl _ (above m hm)) ne (recognizes_of_weight top)
      (by simpa [List.append_assoc] using whereAt)
    have jm : j=m := (List.cons.inj cut).1
    subst j
    have exactR := ih (pre++F++[m]) more (by simpa [List.append_assoc] using whereAt) hR
    rw [exactR]

/-- If a proper suffix loses part of its first gap and the last recognized
gap can grow, the sequence in the host still dominates the full demand. -/
theorem increased_ends {r z g j : ℕ} {us front tail : List ℕ}
    (first : r≤z) (last : g≤j) (hits : r::us=front++j::tail) :
    ∃ W, z::us=W++tail ∧ Dominated (front++[g]) W := by
  cases front with
  | nil =>
    obtain ⟨rfl,rfl⟩ := List.cons.inj hits
    exact ⟨[z],rfl,.cons (last.trans first) .nil⟩
  | cons f front =>
    obtain ⟨rfl,rfl⟩ := List.cons.inj hits
    exact ⟨z::(front++[j]),by simp,.cons first
      (List.rel_append (List.forall₂_refl front) (.cons last .nil))⟩

end ThreeWordCodes.BinaryGaps
