module

public import ThreeWordCodes.Names
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # Powers and commuting words -/

@[expose] public section
namespace ThreeWordCodes
variable {A I : Type*}

def wordPow (u : Word A) (n : ℕ) : Word A := ((FreeMonoid.ofList u)^n).toList

@[simp] theorem wordPow_zero (u : Word A) : wordPow u 0 = [] := rfl
@[simp] theorem wordPow_one (u : Word A) : wordPow u 1 = u := by simp [wordPow]
theorem wordPow_add (u : Word A) (n m : ℕ) : wordPow u (n+m) = wordPow u n ++ wordPow u m := by
  simp [wordPow, pow_add]
theorem wordPow_succ (u : Word A) (n : ℕ) : wordPow u (n+1) = wordPow u n ++ u := by
  simp [wordPow_add]
theorem wordPow_succ' (u : Word A) (n : ℕ) : wordPow u (n+1) = u ++ wordPow u n := by
  simp [wordPow,pow_succ']
theorem wordPow_mul (u : Word A) (n m : ℕ) : wordPow (wordPow u n) m = wordPow u (n*m) := by
  simp [wordPow, pow_mul]
theorem wordPow_comm (u : Word A) (n m : ℕ) : wordPow u n ++ wordPow u m = wordPow u m ++ wordPow u n := by
  rw [← wordPow_add, ← wordPow_add, Nat.add_comm]

/-- Move the left part of a repeated block across the power. -/
theorem rotate_power (u v : Word A) (n : ℕ) : wordPow (u++v) n ++ u = u ++ wordPow (v++u) n := by
  simpa [wordPow] using congrArg FreeMonoid.toList (mul_pow_mul (FreeMonoid.ofList u) (FreeMonoid.ofList v) n)

theorem spell_wordPow (v : I → Word A) (w : Word I) (n : ℕ) :
    spell v (wordPow w n) = wordPow (spell v w) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ,spell_append,ih,wordPow_succ]

theorem spell_replicate (v : I → Word A) (i : I) (n : ℕ) :
    spell v (List.replicate n i) = wordPow (v i) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,wordPow_succ',ih]

/-- Two words commute exactly when they are powers of a common word. -/
theorem commuting_iff_common_power (u v : Word A) :
    u ++ v = v ++ u ↔ ∃ r : Word A, ∃ m n : ℕ, u = wordPow r m ∧ v = wordPow r n := by
  constructor
  · intro comm
    induction len : u.length + v.length using Nat.strong_induction_on generalizing u v with
    | ind n ih =>
      by_cases he : u = []
      · exact ⟨v,0,1,he,(wordPow_one v).symm⟩
      by_cases hf : v = []
      · exact ⟨u,1,0,(wordPow_one u).symm,hf⟩
      rcases List.append_eq_append_iff.mp comm with ⟨t,rfl,eqn⟩ | ⟨t,rfl,eqn⟩
      · obtain ⟨r,i,j,hu,ht⟩ := ih _ (by simp at len; have := List.length_pos_iff.mpr he; omega)
          u t eqn rfl
        exact ⟨r,i,i+j,hu,by rw [wordPow_add, ←hu, ←ht]⟩
      · obtain ⟨r,i,j,hv,ht⟩ := ih _ (by simp at len; have := List.length_pos_iff.mpr hf; omega)
          v t eqn rfl
        exact ⟨r,i+j,i,by rw [wordPow_add, ←hv, ←ht],hv⟩
  · rintro ⟨r,i,j,rfl,rfl⟩
    exact wordPow_comm r i j

end ThreeWordCodes
