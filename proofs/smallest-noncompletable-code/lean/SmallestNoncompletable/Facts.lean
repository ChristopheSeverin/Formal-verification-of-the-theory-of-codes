module

public import SmallestNoncompletable.Codes

/-! # Words of a code containing `{aa, abab, baaa, b}`

Letters are booleans with `a = false` and `b = true`. A word `m` of a code `M` is *framed* by a
subset `C` if `l m r ∈ C*` for some `l, r ∈ C*`. Then `m ∈ C`, because the factorization over
`C` and the factorization through `m` coincide.

* Every word avoiding `bab` is framed by `{aa, b, baaa}` with `l = baaaa` and `r = aaaa`. Hence
  the words of `M` avoiding `bab` are exactly `aa`, `b` and `baaa`.
* Every alternating word `w` satisfies `α w β = (ab)ⁿ` with `α ∈ {ε, a}`, `β ∈ {ε, b}`, so it is
  framed by `X` with `l = baaα` and `r = β`. Hence the alternating words of `M` are `b` and
  `abab`.
* If `(ab)ⁿ bᴷ ∈ M*` with `n` odd, the word `baa (ab)ⁿ bᴷ` has two factorizations, one starting
  with `b` and one with `baaa`. -/

@[expose] public section

namespace SmallestNoncompletable

open InformationTheory

variable {α : Type*}

/-- A word of a code framed by a subset of the code belongs to that subset. -/
theorem framing {C M : Set (List α)} (hCM : C ⊆ M) (hM : IsUniquelyDecodable M)
    {l m r : List α} (hl : l ∈ Star C) (hr : r ∈ Star C) (h : l ++ m ++ r ∈ Star C)
    (hm : m ∈ M) : m ∈ C := by
  obtain ⟨Ll, hLl, rfl⟩ := hl
  obtain ⟨Lr, hLr, rfl⟩ := hr
  obtain ⟨L, hL, e⟩ := h
  have := hM (Ll ++ m :: Lr) L
    (by
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      exacts [hCM (hLl x hx), hm, hCM (hLr x hx)])
    (fun x hx => hCM (hL x hx)) (by simp [e])
  have hmL : m ∈ L := by rw [← this]; simp
  exact hL m hmL

/-- The code `{aa, abab, baaa, b}`. -/
def Xcode : Set (List Bool) :=
  {[false, false], [false, true, false, true], [true, false, false, false], [true]}

/-- The words `aa`, `b` and `baaa` of the code. -/
def Bcode : Set (List Bool) := {[false, false], [true], [true, false, false, false]}

theorem Bcode_subset : Bcode ⊆ Xcode := by
  intro w hw
  simp only [Bcode, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  simp only [Xcode, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `(ab)ⁿ`. -/
def abPow (n : ℕ) : List Bool := (List.replicate n [false, true]).flatten

theorem abPow_succ (n : ℕ) : abPow (n + 1) = false :: true :: abPow n := by
  simp [abPow, List.replicate_succ]

theorem abPow_add_two (n : ℕ) : abPow (n + 2) = abPow n ++ [false, true, false, true] := by
  simp [abPow, List.replicate_succ', List.flatten_append]

theorem abPow_two_mul (q : ℕ) :
    abPow (2 * q) = (List.replicate q [false, true, false, true]).flatten := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by omega, abPow_add_two, ih, List.replicate_succ',
      List.flatten_append]
    simp

/-- `bab` is a factor. -/
def HasBab (w : List Bool) : Prop := [true, false, true] <:+: w

section AvoidBab

theorem aa_mem_B : [false, false] ∈ Star Bcode := mem_star_of_mem (by simp [Bcode])

/-- `baᵏ ∈ {aa, b, baaa}*` for `k ≠ 1`. -/
theorem block_mem : ∀ k, k ≠ 1 → true :: List.replicate k false ∈ Star Bcode
  | 0, _ => mem_star_of_mem (by simp [Bcode])
  | 1, h => absurd rfl h
  | k + 2, h => by
    by_cases hk : k = 1
    · subst hk
      exact mem_star_of_mem (by simp [Bcode])
    · have e : true :: List.replicate (k + 2) false =
          (true :: List.replicate k false) ++ [false, false] := by
        simp [List.replicate_succ', List.append_assoc]
      rw [e]
      exact append_mem_star (block_mem k hk) aa_mem_B

/-- A word starting with `b`, avoiding `bab`, and padded by `aaaa` lies in `{aa, b, baaa}*`. -/
theorem padded_mem : ∀ (m : List Bool) (k : ℕ),
    ¬ HasBab (true :: List.replicate k false ++ m) →
      true :: List.replicate k false ++ m ++ List.replicate 4 false ∈ Star Bcode
  | [], k, _ => by
    have e : true :: List.replicate k false ++ [] ++ List.replicate 4 false =
        true :: List.replicate (k + 4) false := by
      simp [List.replicate_add]
    rw [e]
    exact block_mem _ (by omega)
  | false :: m, k, h => by
    have e : true :: List.replicate k false ++ false :: m =
        true :: List.replicate (k + 1) false ++ m := by
      simp [List.replicate_succ']
    rw [e] at h ⊢
    exact padded_mem m (k + 1) h
  | true :: m, k, h => by
    have hk : k ≠ 1 := by
      rintro rfl
      exact h ⟨[], m, by simp⟩
    have h' : ¬ HasBab (true :: List.replicate 0 false ++ m) := by
      intro hb
      apply h
      have hs : (true :: List.replicate 0 false ++ m) <:+:
          (true :: List.replicate k false ++ true :: m) := by
        simpa using (List.suffix_append (true :: List.replicate k false) (true :: m)).isInfix
      exact hb.trans hs
    have e : true :: List.replicate k false ++ true :: m ++ List.replicate 4 false =
        (true :: List.replicate k false) ++ (true :: List.replicate 0 false ++ m ++
          List.replicate 4 false) := by
      simp
    rw [e]
    exact append_mem_star (block_mem k hk) (padded_mem m 0 h')

theorem hasBab_of_padded {m : List Bool}
    (h : HasBab (true :: List.replicate 4 false ++ m)) : HasBab m := by
  simp only [HasBab, List.replicate, List.cons_append, List.nil_append] at h
  rcases List.infix_cons_iff.mp h with h | h
  · simp at h
  rcases List.infix_cons_iff.mp h with h | h
  · simp at h
  rcases List.infix_cons_iff.mp h with h | h
  · simp at h
  rcases List.infix_cons_iff.mp h with h | h
  · simp at h
  rcases List.infix_cons_iff.mp h with h | h
  · simp at h
  exact h

/-- **(F1)** The words of `M` avoiding `bab` are `aa`, `b` and `baaa`. -/
theorem mem_Bcode_of_not_hasBab {M : Set (List Bool)} (hM : IsUniquelyDecodable M)
    (hB : Bcode ⊆ M) {m : List Bool} (hm : m ∈ M) (h : ¬ HasBab m) : m ∈ Bcode := by
  refine framing hB hM (l := true :: List.replicate 4 false) (r := List.replicate 4 false)
    (block_mem 4 (by omega)) ?_ ?_ hm
  · have e : List.replicate 4 false = [false, false] ++ [false, false] := rfl
    rw [e]
    exact append_mem_star aa_mem_B aa_mem_B
  · exact padded_mem m 4 fun hb => h (hasBab_of_padded hb)

end AvoidBab

section Alternating

/-- No factor `aa` or `bb`. -/
def Alternating (w : List Bool) : Prop := ¬ [false, false] <:+: w ∧ ¬ [true, true] <:+: w

theorem Alternating.tail {x : Bool} {w : List Bool} (h : Alternating (x :: w)) :
    Alternating w :=
  ⟨fun h' => h.1 (h'.trans (List.suffix_cons x w).isInfix),
    fun h' => h.2 (h'.trans (List.suffix_cons x w).isInfix)⟩

theorem Alternating.ne {x y : Bool} {w : List Bool} (h : Alternating (x :: y :: w)) : x ≠ y := by
  rintro rfl
  cases x
  · exact h.1 ⟨[], w, rfl⟩
  · exact h.2 ⟨[], w, rfl⟩

/-- An alternating word extends to a power of `ab` by at most one letter on each side. -/
theorem alternating_extend : ∀ (w : List Bool) (x : Bool), Alternating (x :: w) →
    ∃ β : List Bool, (β = [] ∨ β = [true]) ∧ ∃ n,
      (if x then false :: x :: w else x :: w) ++ β = abPow n
  | [], x, _ => by
    cases x
    · exact ⟨[true], Or.inr rfl, 1, rfl⟩
    · exact ⟨[], Or.inl rfl, 1, rfl⟩
  | y :: w, x, h => by
    have hxy := h.ne
    obtain ⟨β, hβ, n, e⟩ := alternating_extend w y h.tail
    cases x <;> cases y
    · exact absurd rfl hxy
    · refine ⟨β, hβ, n, ?_⟩
      simpa using e
    · refine ⟨β, hβ, n + 1, ?_⟩
      rw [abPow_succ, ← e]
      simp
    · exact absurd rfl hxy

/-- `baa (ab)ⁿ ∈ X*`. -/
theorem baa_abPow_mem : ∀ n, [true, false, false] ++ abPow n ∈ Star Xcode
  | 0 => by
    have : [true, false, false] = [true] ++ [false, false] := rfl
    rw [show abPow 0 = [] from rfl, List.append_nil, this]
    exact append_mem_star (mem_star_of_mem (by simp [Xcode])) (mem_star_of_mem (by simp [Xcode]))
  | 1 => by
    have : [true, false, false] ++ abPow 1 = [true, false, false, false] ++ [true] := rfl
    rw [this]
    exact append_mem_star (mem_star_of_mem (by simp [Xcode])) (mem_star_of_mem (by simp [Xcode]))
  | n + 2 => by
    rw [abPow_add_two, ← List.append_assoc]
    exact append_mem_star (baa_abPow_mem n) (mem_star_of_mem (by simp [Xcode]))

/-- **(F2)** The alternating words of `M` are `b` and `abab`. -/
theorem mem_of_alternating {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hX : Xcode ⊆ M)
    {m : List Bool} (hm : m ∈ M) (h : Alternating m) :
    m = [true] ∨ m = [false, true, false, true] := by
  have hne : m ≠ [] := fun e => hM.epsilon_notMem (e ▸ hm)
  obtain ⟨x, w, rfl⟩ : ∃ x w, m = x :: w := List.exists_cons_of_ne_nil hne
  obtain ⟨β, hβ, n, e⟩ := alternating_extend w x h
  have hβ' : β ∈ Star Xcode := by
    rcases hβ with rfl | rfl
    · exact nil_mem_star _
    · exact mem_star_of_mem (by simp [Xcode])
  have hmX : x :: w ∈ Xcode := by
    cases x
    · refine framing hX hM (l := [true, false, false]) (r := β) ?_ hβ' ?_ hm
      · exact append_mem_star (mem_star_of_mem (show [true] ∈ Xcode by simp [Xcode]))
          (mem_star_of_mem (show [false, false] ∈ Xcode by simp [Xcode]))
      · have := baa_abPow_mem n
        rw [← e] at this
        simpa using this
    · refine framing hX hM (l := [true, false, false, false]) (r := β)
        (mem_star_of_mem (by simp [Xcode])) hβ' ?_ hm
      have := baa_abPow_mem n
      rw [← e] at this
      simpa using this
  simp only [Xcode, Set.mem_insert_iff, Set.mem_singleton_iff] at hmX
  rcases hmX with h1 | h1 | h1 | h1
  · rw [h1] at h
    exact absurd ⟨[], [], rfl⟩ h.1
  · exact Or.inr h1
  · rw [h1] at h
    exact absurd ⟨[true, false], [], rfl⟩ h.1
  · exact Or.inl h1

end Alternating

/-- **(F3)** If `(ab)ⁿ bᴷ ∈ M*` then `n` is even. -/
theorem even_of_abPow_mem {M : Set (List Bool)} (hM : IsUniquelyDecodable M) (hX : Xcode ⊆ M)
    {n K : ℕ} (h : abPow n ++ List.replicate K true ∈ Star M) : Even n := by
  by_contra hodd
  obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 1 := Nat.not_even_iff_odd.mp hodd
  obtain ⟨L, hL, e⟩ := h
  have hb : [true] ∈ M := hX (by simp [Xcode])
  have haa : [false, false] ∈ M := hX (by simp [Xcode])
  have hbaaa : [true, false, false, false] ∈ M := hX (by simp [Xcode])
  have habab : [false, true, false, true] ∈ M := hX (by simp [Xcode])
  have key := hM ([true] :: [false, false] :: L)
    ([true, false, false, false] :: [true] :: (List.replicate q [false, true, false, true] ++
      List.replicate K [true]))
    (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      exacts [hb, haa, hL x hx])
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | rfl | hx | hx
      · exact hbaaa
      · exact hb
      · rw [List.eq_of_mem_replicate hx]; exact habab
      · rw [List.eq_of_mem_replicate hx]; exact hb)
    (by
      simp only [List.flatten_cons, e, List.flatten_append]
      rw [abPow_succ, abPow_two_mul, List.flatten_replicate_singleton]
      simp)
  simp at key

end SmallestNoncompletable
