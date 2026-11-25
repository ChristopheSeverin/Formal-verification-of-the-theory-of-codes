module

public import ThreeWordCodes.Powers
public import ThreeWordCodes.Greedy

/-! # Word-equation obstructions in the crossed comparisons of Section 5

The parameters may be arbitrary words. Substitution therefore gives all
the displayed identities on the actual binary letters.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A : Type*}

theorem alternating_transfer (a b : Word A) (m n k : ℕ) :
    wordPow (wordPow (a++b) m) n ++ (wordPow (a++b) k ++ a) =
      (wordPow (a++b) k ++ a) ++ wordPow (wordPow (b++a) n) m := by
  rw [wordPow_mul, wordPow_mul, Nat.mul_comm n m, ← List.append_assoc, wordPow_comm _ (m*n) k]
  simp only [List.append_assoc]
  rw [rotate_power a b (m*n)]

/-- The two parsings have different first names whenever n is positive.
This includes the alternating branch of III and, with the letters exchanged,
the alternating branch of IV with t=a. -/
theorem alternating_ambiguity (a b : Word A) (m n k : ℕ) (hn : 0 < n) :
    ¬ NamedCode (addToken (pair (wordPow (a++b) m) (wordPow (b++a) n)) (wordPow (a++b) k ++ a)) := by
  let v := addToken (pair (wordPow (a++b) m) (wordPow (b++a) n)) (wordPow (a++b) k ++ a)
  intro hi
  have e : spell v (List.replicate n (some false) ++ [none]) =
      spell v (none :: List.replicate m (some true)) := by
    simpa only [spell_append, spell_cons, spell_nil, List.append_nil, spell_replicate, v, addToken, pair]
      using alternating_transfer a b m n k
  have bad := hi e
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ] at bad

private theorem right_block (a b : Word A) (k : ℕ) :
    (b ++ wordPow (a++b) k) ++ a = wordPow (b++a) (k+1) := by
  rw [← rotate_power b a k, List.append_assoc, wordPow_succ]

private theorem left_block (a b : Word A) (k : ℕ) :
    a ++ (wordPow (b++a) k ++ b) = wordPow (a++b) (k+1) := by
  rw [← List.append_assoc, ← rotate_power a b k, List.append_assoc, wordPow_succ]

/-- The three entries in the (i,q)=(1,0) row of the alternating-identity table in Section 5. Here k=N-1. -/
theorem comparison_table_first (a b : Word A) (m k : ℕ) :
    let P := wordPow (a++b) m
    let C := b ++ wordPow (a++b) k
    (P ++ ((P ++ a) ++ C) = ((P ++ a) ++ C) ++ P) ∧
    (C ++ wordPow P (k+1) = wordPow (C ++ a) m ++ C) ∧
    (wordPow P (k+1) ++ (P ++ a) = (P ++ a) ++ wordPow (C ++ a) m) := by
  dsimp only
  have together : (wordPow (a++b) m ++ a) ++ (b ++ wordPow (a++b) k) =
      wordPow (a++b) (m + (k+1)) := by
    simp [wordPow_add (a++b) m, wordPow_succ', List.append_assoc]
  rw [together, right_block]
  refine ⟨wordPow_comm .., ?_, alternating_transfer a b m (k+1) m⟩
  rw [← rotate_power b a k]
  exact (alternating_transfer b a (k+1) m k).symm

/-- The three entries in the (i,q)=(0,1) row of the same table. Here k=m-1. -/
theorem comparison_table_second (a b : Word A) (k n : ℕ) :
    let P := wordPow (b++a) k ++ b
    let C := wordPow (a++b) n
    (wordPow (P ++ a) n ++ P = P ++ wordPow C (k+1)) ∧
    (C ++ ((C ++ a) ++ P) = ((C ++ a) ++ P) ++ C) ∧
    ((P ++ a) ++ (P ++ (C ++ a)) = (P ++ (C ++ a)) ++ (P ++ a)) := by
  dsimp only
  have p_a : (wordPow (b++a) k ++ b) ++ a = wordPow (b++a) (k+1) := by
    rw [List.append_assoc, wordPow_succ]
  have cp : (wordPow (a++b) n ++ a) ++ (wordPow (b++a) k ++ b) =
      wordPow (a++b) (n+(k+1)) := by rw [List.append_assoc, left_block, wordPow_add (a++b) n (k+1)]
  have pc : (wordPow (b++a) k ++ b) ++ (wordPow (a++b) n ++ a) =
      wordPow (b++a) (k+(n+1)) := by
    rw [List.append_assoc, ← List.append_assoc b, right_block, wordPow_add (b++a) k (n+1)]
  rw [p_a,cp,pc]
  exact ⟨alternating_transfer b a (k+1) n k,wordPow_comm ..,wordPow_comm ..⟩

end ThreeWordCodes
