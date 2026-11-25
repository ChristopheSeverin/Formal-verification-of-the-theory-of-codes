module

public import ThreeWordCodes.PalindromicReading
public import ThreeWordCodes.PalindromicRise

/-! # Reduction of Proposition 7 to the common lower bound for the gaps -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

def following (s : ℕ) (ns : List ℕ) := ns.flatMap (fun n => wordPow (x s) n ++ c)

theorem spell_full (s : ℕ) (ns : List ℕ) :
    spell (pair (x s) c) (mixed 0 ns 0) = c++following s ns := by
  have tail (gs : List ℕ) : spell (pair (x s) c) (gapTail 0 gs)=following s gs := by
    induction gs with
    | nil => rfl
    | cons n gs ih => simp [gapTail,run,spell_replicate,pair,following,List.append_assoc] at ih ⊢; exact ih
  exact congrArg (c++·) (tail ns)

theorem Reading.spelling {s : ℕ} {ns : List ℕ} {z : Word Bool} (r : Reading s ns z) :
    z++x s = c++following s ns := r.trans (spell_full s ns)

theorem Reading.rise_prefix {s n j : ℕ} {rest : List ℕ} {z : Word Bool}
    (r : Reading s (n::j::rest) z) (rise : n<j) :
    (c++wordPow (x s) n) ++ (c++wordPow (x s) n) ++ [a] <+: z := by
  obtain ⟨e,hj⟩ := Nat.exists_eq_add_of_le (show n+1≤j by omega)
  let D := (c++wordPow (x s) n) ++ (c++wordPow (x s) n)
  let W := wordPow (x s) e ++ c ++ following s rest
  have eqn : z++x s=D++(x s++W) := by
    simpa [D,W,following,hj,wordPow_add,wordPow_succ (x s) n,List.append_assoc] using r.spelling
  have long : 1≤W.length := by simp [W,c]; omega
  have lens := congrArg List.length eqn
  simp only [List.length_append] at lens
  obtain ⟨t,hd⟩ := x_head s
  have isPre : D++[a] <+: z++x s := ⟨t++W,by rw [eqn,hd]; simp [List.append_assoc]⟩
  have base : z <+: z++x s := List.prefix_append ..
  rcases List.prefix_or_prefix_of_prefix isPre base with ready | rev
  · exact ready
  · have le := rev.length_le
    simp at le
    have same := rev.eq_of_length (by simp; omega)
    rw [same]

theorem Reading.small_gap {s k l : ℕ} {ns : List ℕ} {z : Word Bool}
    (r : Reading s ns z) (code : NamedCode (triple s k l z)) : ∃ n∈ns,n≤k+l := by
  have abs := (r.equations k l).namedCode_iff.mpr code
  by_contra! large
  apply long_gap_ambiguity (k+1) (l+1) _ _ abs
  intro x hx
  obtain ⟨n,mem,rfl⟩ := List.mem_map.mp hx
  have := large n mem
  omega

private theorem end_positive {s k l : ℕ} {ns : List ℕ} {z : Word Bool}
    (r : Reading s ns z) (code : NamedCode (triple s k l z)) (bad : ¬Completable (triple s k l z)) :
    ∃ pre : List ℕ, ∃ q, ns=pre++[q+1] := by
  obtain ⟨pre,q,read⟩ := reading_exists code bad
  exact ⟨pre,q,r.unique read⟩

private theorem other_bounds {s k l f q : ℕ} {middle : List ℕ} {z : Word Bool}
    (r : Reading s (f::(middle++[q])) z) (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) :
    (∀ n∈f::middle,l≤n) ∧ (∀ n∈middle++[q],k≤n) := by
  have forward {s k l last : ℕ} {pre : List ℕ} {z : Word Bool}
      (r : Reading s (pre++[last]) z) (code : NamedCode (triple s k l z))
      (bad : ¬Completable (triple s k l z)) : ∀ n∈pre,l≤n := by
    obtain ⟨u,n,e⟩ := end_positive r code bad
    have eqn : last=n+1 := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? e
    exact before_last_bound (eqn ▸ r) code bad
  refine ⟨forward (pre:=f::middle) r code bad,?_⟩
  have rev : Reading s ((q::middle.reverse)++[f]) z.reverse := by simpa using r.reverse
  have bound := forward rev (triple_reverse s k l z ▸ code.reverse) (fun ok => bad (flip_back ok))
  intro n hn
  exact bound n (by simpa [or_comm] using hn)

private theorem first_large {s k l f q : ℕ} {middle : List ℕ} {z : Word Bool}
    (r : Reading s (f::(middle++[q])) z) (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) : k≤f := by
  by_contra! low
  have other := (other_bounds r code bad).2
  have useRise (next : ℕ) (tail : List ℕ) (shape : middle++[q]=next::tail) : False := by
    have kn := other next (by rw [shape]; simp)
    exact bad (initial_rise_completion s k l f z (by omega)
      ((shape ▸ r : Reading s (f::next::tail) z).rise_prefix (by omega)))
  cases middle with
  | nil => exact useRise q [] rfl
  | cons n ns => exact useRise n (ns++[q]) rfl

/-- Both exponents bound every gap when the reading has at least two gaps,
including the two endpoint exceptions in the manuscript. -/
theorem all_gap_bounds {s k l f q : ℕ} {middle : List ℕ} {z : Word Bool}
    (r : Reading s (f::(middle++[q])) z) (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) : ∀ n∈f::(middle++[q]),max k l ≤ n := by
  obtain ⟨fl,lr⟩ := other_bounds r code bad
  have fk := first_large r code bad
  have rev : Reading s (q::(middle.reverse++[f])) z.reverse := by simpa using r.reverse
  have ql := first_large rev (triple_reverse s k l z ▸ code.reverse) (fun ok => bad (flip_back ok))
  intro n mem
  rcases List.mem_cons.mp mem with rfl | later
  · exact max_le fk (fl n (by simp))
  rcases List.mem_append.mp later with mid | last
  · exact max_le (lr n (by simp [mid])) (fl n (by simp [mid]))
  · obtain rfl := List.mem_singleton.mp last
    exact max_le (lr n (by simp)) ql

private theorem singleton_pow {A : Type*} (a : A) (n : ℕ) : wordPow [a] n=List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ',ih,List.replicate_succ]; rfl

/-- Equal gaps cannot occur in a residual reading of any length. -/
theorem constant_gap_ambiguity {s k l n m : ℕ} {z : Word Bool}
    (r : Reading s (List.replicate (m+1) n) z) (bounds : max k l≤n) :
    ¬NamedCode (triple s k l z) := by
  intro code
  have model := (r.equations k l).namedCode_iff.mpr code
  rw [List.map_replicate] at model
  have small := r.small_gap code
  obtain ⟨x,hx,xs⟩ := small
  have eqn := List.eq_of_mem_replicate hx
  apply (one_marker_ambiguity_iff (k+1) (l+1) _).mpr _ model
  right
  exact ⟨[],1+n,m,by omega,by omega,by simp,by simp [singleton_pow]⟩

theorem two_gap_completion (s k l f q : ℕ) (z : Word Bool) (r : Reading s [f,q] z)
    (code : NamedCode (triple s k l z)) : Completable (triple s k l z) := by
  by_contra bad
  have small := r.small_gap code
  simp only [List.mem_cons,List.not_mem_nil,or_false] at small
  obtain ⟨n,h,xs⟩ := small
  rcases lt_trichotomy f q with lt | rfl | gt
  · exact bad (initial_rise_completion s k l f z (by rcases h with rfl | rfl <;> omega) (r.rise_prefix lt))
  · have bound := all_gap_bounds (middle:=[]) r code bad f (by simp)
    exact constant_gap_ambiguity (m:=1) (n:=f) r bound code
  · have rev : Reading s [q,f] z.reverse := by simpa using r.reverse
    exact bad (flip_back (initial_rise_completion s l k q z.reverse (by rcases h with rfl | rfl <;> omega) (rev.rise_prefix gt)))

/-- The remaining common-gap construction has at least three gaps and a
short entry. For every ns, its coordinates are uniquely determined by z. -/
def CommonGapConstruction : Prop :=
  ∀ s k l (z : Word Bool) (ns : List ℕ), 3≤ns.length → Reading s ns z →
    (∀ n∈ns,max k l≤n) → (∃ n∈ns,n≤k+l) → NamedCode (triple s k l z) → Completable (triple s k l z)

theorem proposition_seven_iff_common_gaps : PropositionSeven ↔ CommonGapConstruction := by
  constructor
  · exact fun all s k l z _ _ _ _ _ code => all s k l z code
  · intro common s k l z code
    by_contra bad
    obtain ⟨pre,q,r⟩ := reading_exists code bad
    cases pre with
    | nil =>
      have shape : z=single s q := by simpa [mixed,gapTail,run,single,pair] using r.last_positive
      exact bad (shape.symm ▸ single_gap_completion s k l q (shape ▸ code))
    | cons f mid =>
      cases mid with
      | nil => exact bad (two_gap_completion s k l f (q+1) z r code)
      | cons n ns =>
        exact bad (common s k l z _ (by simp) r (all_gap_bounds (middle:=n::ns) r code bad) (r.small_gap code) code)

end ThreeWordCodes.Palindromic
