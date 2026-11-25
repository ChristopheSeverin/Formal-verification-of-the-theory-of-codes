module

public import ThreeWordCodes.GapComparison

/-! # A positive completion form of the residue test

The mixed entries may have arbitrary prefixes before their last marker. Only
the numbers of trailing copies of the pure letter are compared modulo m.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {I : Type*}

def residueWords (m : ℕ) (pre : I → Word Bool) (tail : I → ℕ) : Option I → Word Bool
  | none => run m
  | some i => pre i ++ b :: run (tail i)

theorem residue_completion [Fintype I] (m : ℕ) (hm : 0 < m) (pre : I → Word Bool) (tail : I → ℕ)
    (distinct : Function.Injective (fun i => tail i % m)) : Completable (residueWords m pre tail) := by
  let rem (i : I) := tail i%m
  let base := residueWords m pre rem
  let backward (k : Option I) := (base k).reverse
  have pure : backward none = run m := by simp [backward,base,residueWords,run]
  have mixed (i : I) : backward (some i) = run (rem i) ++ b :: (pre i).reverse := by
    simp [backward,base,residueWords,run,List.append_assoc]
  have cmp (x y : Option I) (p : backward x <+: backward y) : x=y := by
    rcases x with _ | i <;> rcases y with _ | j
    · rfl
    · rw [pure,mixed] at p
      exact (Nat.not_le_of_lt (Nat.mod_lt _ hm) (pure_prefix_bound p)).elim
    · rw [pure,mixed] at p
      exact (marked_not_prefix_pure _ _ _ p).elim
    · rw [mixed,mixed] at p
      exact congrArg some (distinct (marked_prefix p).1)
  have bc : Completable backward := by
    apply completable_prefix
    · intro x y eqn
      exact cmp x y (by rw [eqn])
    · rintro (_ | i)
      · rw [pure]
        intro h
        have := congrArg List.length h
        simp [run] at this
        omega
      · rw [mixed]
        simp
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ p
      exact congrArg backward (cmp x y p)
  have basic : Completable base := by simpa only [backward,List.reverse_reverse] using bc.reverse
  let extra : Option I → Word (Option I)
    | none => []
    | some i => List.replicate (tail i / m) none
  have runs (k : ℕ) : spell base (List.replicate k none) = run (m*k) := by
    induction k with
    | zero => simp [run]
    | succ k ih => simp only [List.replicate_succ,spell_cons,ih,Nat.mul_succ]
                   change run m ++ run (m*k) = run (m*k+m)
                   rw [Nat.add_comm,run_add]
  have actual : (fun k => base k ++ spell base (extra k)) = residueWords m pre tail := by
    funext k
    cases k with
    | none => simp [base,extra,residueWords]
    | some i =>
      simp only [extra,runs,base,residueWords,List.append_assoc,List.cons_append]
      rw [←run_add,Nat.mod_add_div]
  exact actual ▸ basic.padRight extra

end ThreeWordCodes.BinaryGaps
