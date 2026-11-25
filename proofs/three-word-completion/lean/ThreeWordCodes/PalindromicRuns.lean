module

public import ThreeWordCodes.PalindromicEnds

/-! # Restrictions on the remaining third word in Proposition 7 -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private inductive State
  | start | oneA | twoA | endedB | invalid
  deriving DecidableEq

private def next : State → Bool → State
  | .invalid, _ => .invalid
  | .start, false | .endedB, false => .oneA
  | .oneA, false => .twoA
  | .twoA, false | .endedB, true => .invalid
  | _, true => .endedB

private def scan (v : Word Bool) (s : State) := v.foldl next s

@[simp] private theorem scan_cons (a : Bool) (w : Word Bool) (s : State) :
    scan (a::w) s=scan w (next s a) := rfl
@[simp] private theorem scan_append (u v : Word Bool) (s : State) :
    scan (u++v) s=scan v (scan u s) := by simp [scan]
@[simp] private theorem scan_invalid (w : Word Bool) : scan w .invalid=.invalid := by
  induction w with
  | nil => rfl
  | cons z w ih => exact ih

private theorem reader_ok (s : ℕ) (p : Word Bool) (q : State) (ok : q=.start ∨ q=.oneA) :
    scan (spell (pair (x s) c) p) q=.start ∨ scan (spell (pair (x s) c) p) q=.oneA := by
  have ab (n : ℕ) : scan (wordPow [a,b] n) .endedB=.endedB := by
    induction n with
    | zero => rfl
    | succ n ih => rw [wordPow_succ',scan_append]; exact ih
  induction p generalizing q with
  | nil => exact ok
  | cons z p ih =>
    rw [spell_cons,scan_append]
    apply ih
    right
    cases z with
    | false =>
      change scan (x s) q=_
      rw [x,scan_append,wordPow_succ',scan_append]
      have start : scan [a,b] q=.endedB := by rcases ok with rfl | rfl <;> rfl
      rw [start,ab]
      rfl
    | true => rcases ok with rfl | rfl <;> rfl

/-- The prefix products on x and ba have neither bb nor aaa as a contiguous
factor. Either factor therefore gives an unconditional completion. -/
theorem forbidden_factor_completion (s k l : ℕ) (z : Word Bool)
    (factor : [b,b] <:+: z ∨ [a,a,a] <:+: z) : Completable (triple s k l z) := by
  apply incomparable_reading
  intro h
  obtain ⟨p,tail,eqn⟩ := prefix_on_x_c s l h
  have accepted := reader_ok s p .start (Or.inl rfl)
  have bb (q : State) : scan [b,b] q=.invalid := by cases q <;> rfl
  have aaa (q : State) : scan [a,a,a] q=.invalid := by cases q <;> rfl
  have illegal : scan (spell (pair (x s) c) p) .start=.invalid := by
    rcases factor with ⟨left,right,whereAt⟩ | ⟨left,right,whereAt⟩
    · rw [←eqn,←whereAt,scan_append,scan_append,scan_append,bb,scan_invalid,scan_invalid]
    · rw [←eqn,←whereAt,scan_append,scan_append,scan_append,aaa,scan_invalid,scan_invalid]
  rw [illegal] at accepted
  rcases accepted with eq | eq <;> contradiction

private theorem nonalternating_double (z : Word Bool) (fails : ¬z.IsChain (·≠·)) :
    [a,a] <:+: z ∨ [b,b] <:+: z := by
  induction z with
  | nil => simp at fails
  | cons x xs ih =>
    cases xs with
    | nil => simp at fails
    | cons y rest =>
      by_cases same : x=y
      · subst y
        cases x with
        | false => exact Or.inl ⟨[],rest,rfl⟩
        | true => exact Or.inr ⟨[],rest,rfl⟩
      · have tail : ¬(y::rest).IsChain (·≠·) := fun ok => fails (List.isChain_cons_cons.mpr ⟨same,ok⟩)
        exact (ih tail).imp (fun h => List.infix_cons_iff.mpr (Or.inr h)) (fun h => List.infix_cons_iff.mpr (Or.inr h))

/-- A counterexample to this proposition would start and finish in b,
contain a double a, and avoid both a double b and a triple a. -/
theorem residual_word {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬Completable (triple s k l z)) :
    z.head?=some b ∧ z.getLast?=some b ∧ [a,a] <:+: z ∧ ¬[b,b] <:+: z ∧ ¬[a,a,a] <:+: z := by
  have nz : z≠[] := code.entry_ne_nil none
  have hd := List.head?_eq_some_head nz
  have tl := List.getLast?_eq_getLast_of_ne_nil nz
  have noAAa := fun pr => bad (forbidden_factor_completion s k l z (Or.inr pr))
  have noBB := fun pr => bad (forbidden_factor_completion s k l z (Or.inl pr))
  have inA := (nonalternating_double z (fun h => bad (alternating_third_completion s k l z code h))).resolve_right noBB
  refine ⟨?_,?_,inA,noBB,noAAa⟩
  · cases equal : z.head nz with
    | false => exact (bad (initial_a_completion s k l z code (hd.trans (congrArg some equal)))).elim
    | true => exact hd.trans (congrArg some equal)
  · cases equal : z.getLast nz with
    | false => exact (bad (final_a_completion s k l z code (tl.trans (congrArg some equal)))).elim
    | true => exact tl.trans (congrArg some equal)

end ThreeWordCodes.Palindromic
