module

public import ThreeWordCodes.Greedy

/-! # Binary gaps and the one-marker ambiguity criterion (equation 1)

The counter d records how many more a's are required before another b.
An unfinished run at the end is allowed. The outside margins are unrestricted.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
abbrev a : Bool := false
abbrev b : Bool := true
def run (n : ℕ) : Word Bool := List.replicate n a

def Spaced (c : ℕ) : ℕ → Word Bool → Prop
  | _, [] => True
  | d, false :: t => Spaced c (d-1) t
  | d, true :: t => d = 0 ∧ Spaced c c t

private theorem before_run (c d n : ℕ) (w : Word Bool) :
    Spaced c d (run n ++ w) ↔ Spaced c (d-n) w := by
  induction n generalizing d with
  | zero => simp [run]
  | succ n ih =>
    change Spaced c (d-1) (run n ++ w) ↔ _
    rw [ih, show d-1-n = d-(n+1) by omega]

private theorem free_end (c d n : ℕ) : Spaced c d (run n) := by
  simpa using (before_run c d n []).mpr trivial

def gapTail (j : ℕ) : List ℕ → Word Bool
  | [] => run j
  | g :: gs => run g ++ b :: gapTail j gs

def mixed (i : ℕ) (gs : List ℕ) (j : ℕ) : Word Bool := run i ++ b :: gapTail j gs

theorem gaps_spec (c i : ℕ) (gs : List ℕ) (j : ℕ) :
    Spaced c 0 (mixed i gs j) ↔ ∀ g ∈ gs, c ≤ g := by
  have tail : Spaced c c (gapTail j gs) ↔ ∀ g ∈ gs, c ≤ g := by
    induction gs with
    | nil => simp [gapTail, free_end]
    | cons g gs ih =>
      simp only [gapTail, before_run, Spaced, Nat.sub_eq_zero_iff_le, List.forall_mem_cons, ih]
  simpa [mixed, before_run, Spaced] using tail

theorem decompose (w : Word Bool) :
    (∃ n, w = run n) ∨ ∃ i gs j, w = mixed i gs j := by
  induction w with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons x w ih =>
    cases x <;> rcases ih with ⟨n,rfl⟩ | ⟨i,gs,j,rfl⟩
    · exact Or.inl ⟨n+1,rfl⟩
    · exact Or.inr ⟨i+1,gs,j,rfl⟩
    · exact Or.inr ⟨0,[],n,rfl⟩
    · exact Or.inr ⟨0,i::gs,j,rfl⟩

/-- The canonical gap list has one entry per pair of consecutive markers. -/
theorem mixed_count (i : ℕ) (gs : List ℕ) (j : ℕ) :
    (mixed i gs j).count b = gs.length+1 := by
  have empty (n : ℕ) : (run n).count b = 0 := by
    apply List.count_eq_zero.mpr
    simp [run,a,b]
  have tail : (gapTail j gs).count b = gs.length := by
    induction gs with
    | nil => exact empty j
    | cons g gs ih => simp [gapTail,empty,ih,b]
  simp [mixed,empty,tail,b]

theorem mixed_of_contains_marker {w : Word Bool} (h : b ∈ w) :
    ∃ i gs j, w = mixed i gs j := by
  rcases decompose w with ⟨n,rfl⟩ | mixed
  · simp [run,a,b] at h
  · exact mixed

private theorem tail_snoc (gs : List ℕ) (g j : ℕ) :
    gapTail j (gs ++ [g]) = gapTail g gs ++ b :: run j := by
  induction gs with
  | nil => rfl
  | cons k ks ih => simp [gapTail, ih, List.append_assoc]

theorem reverse_mixed (i : ℕ) (gs : List ℕ) (j : ℕ) :
    (mixed i gs j).reverse = mixed j gs.reverse i := by
  induction gs generalizing i with
  | nil => simp [mixed, gapTail, run, List.append_assoc]
  | cons g gs ih =>
    have eqn : mixed i (g :: gs) j = run i ++ [b] ++ mixed g gs j := by
      simp [mixed, gapTail, List.append_assoc]
    rw [eqn, List.reverse_append, ih]
    simp [mixed, tail_snoc, run, List.append_assoc]

theorem spaced_reverse (c : ℕ) (w : Word Bool) : Spaced c 0 w.reverse ↔ Spaced c 0 w := by
  rcases decompose w with ⟨n,rfl⟩ | ⟨i,gs,j,rfl⟩
  · simp [run]
  · simp [reverse_mixed, gaps_spec]

private theorem spaced_prefix {u v : Word Bool} (c d : ℕ) (h : Spaced c d (u ++ v)) :
    Spaced c d u := by
  induction u generalizing d with
  | nil => trivial
  | cons x u ih => cases x with
    | false => exact ih (d-1) h
    | true => exact ⟨h.1, ih c h.2⟩

def tokens (c : ℕ) := pair [a] (b :: run c)

private theorem products_spaced (c : ℕ) (s : Word Bool) : Spaced c 0 (spell (tokens c) s) := by
  induction s with
  | nil => trivial
  | cons x s ih =>
    cases x with
    | false => exact ih
    | true =>
      change 0 = 0 ∧ Spaced c c (run c ++ spell (tokens c) s)
      exact ⟨rfl,(before_run c c c _).mpr (by simpa using ih)⟩

/-- Every prefix of a product on a and b a^c has all its internal gaps at least c. -/
theorem spaced_of_prefix_product {w : Word Bool} (c : ℕ) (p : Word Bool) (pr : w <+: spell (tokens c) p) :
    Spaced c 0 w := by
  obtain ⟨r,eqn⟩ := pr
  exact spaced_prefix c 0 (eqn.symm ▸ products_spaced c p)

private theorem spell_pure (c n : ℕ) : spell (tokens c) (run n) = run n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (a :: ·) ih

private theorem finish (c d : ℕ) (w : Word Bool) (bound : d ≤ c) (h : Spaced c d w) :
    ∃ s, run d ++ spell (tokens c) s = w ++ run c := by
  induction w generalizing d with
  | nil =>
    refine ⟨run (c-d),?_⟩
    rw [spell_pure]
    simpa [run, ← List.replicate_add] using congrArg run (show d + (c-d) = c by omega)
  | cons x w ih =>
    cases x with
    | false =>
      cases d with
      | zero =>
        obtain ⟨s,hs⟩ := ih 0 (by omega) h
        exact ⟨false :: s, congrArg (a :: ·) hs⟩
      | succ d =>
        obtain ⟨s,hs⟩ := ih d (by omega) h
        exact ⟨s, congrArg (a :: ·) hs⟩
    | true =>
      obtain ⟨rfl,ht⟩ := h
      obtain ⟨s,hs⟩ := ih c le_rfl ht
      exact ⟨true :: s, congrArg (b :: ·) hs⟩

private theorem token_prefix (c : ℕ) : InformationTheory.IsPrefixFree (Set.range (tokens c)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ ⟨t,e⟩
  cases i <;> cases j <;> simp_all [tokens,pair,run]

theorem ambiguity_right_margin (c : ℕ) (w : Word Bool) :
    ¬ NamedCode (addToken (tokens c) w) ↔ Spaced c 0 w := by
  constructor
  · intro h
    have inj : Function.Injective (tokens c) := by
      intro i j
      cases i <;> cases j <;> simp [tokens,pair]
    obtain ⟨s,t,he⟩ := prefix_of_products_of_ambiguity inj
      (fun i => by cases i <;> simp [tokens,pair]) (token_prefix c) w h
    exact spaced_prefix c 0 (he ▸ products_spaced c s)
  · intro h code
    obtain ⟨s,hs⟩ := finish c 0 w (by omega) h
    change spell (tokens c) s = w ++ run c at hs
    have maps (z : Word Bool) : spell (addToken (tokens c) w) (z.map some) = spell (tokens c) z := by
      simp [spell, List.flatMap_def, List.map_map, Function.comp_def, addToken]
    have he : spell (addToken (tokens c) w) (none :: (run c).map some) =
        spell (addToken (tokens c) w) (s.map some) := by
      simpa only [spell_cons, addToken, maps, spell_pure] using hs.symm
    have impossible := code he
    cases s <;> simp at impossible

/-- Equation (1). The statement even allows an arbitrary initial margin of W. -/
theorem ambiguity_left_margin (c : ℕ) (w : Word Bool) :
    ¬ NamedCode (addToken (pair [a] (run c ++ [b])) w) ↔ Spaced c 0 w := by
  let f := addToken (pair [a] (run c ++ [b])) w
  have eqn : (fun i => (f i).reverse) = addToken (tokens c) w.reverse := by
    funext i
    rcases i with _ | (_ | _) <;> simp [f,addToken,pair,tokens,run]
  have rev : NamedCode f ↔ NamedCode (addToken (tokens c) w.reverse) := by
    rw [← eqn]
    exact ⟨NamedCode.reverse,fun h => by simpa using h.reverse⟩
  exact (not_congr rev).trans ((ambiguity_right_margin _ _).trans (spaced_reverse _ _))

/-- An injective triple with one mixed entry of the form b a^c always has a
positive finite completion, for every third word. -/
theorem right_marker_completion (c : ℕ) (w : Word Bool) (code : NamedCode (addToken (tokens c) w)) :
    Completable (addToken (tokens c) w) := by
  apply greedy_completion
  · intro x y eqn
    cases x <;> cases y <;> simp_all [tokens,pair,a,b]
  · intro x
    cases x <;> simp [tokens,pair]
  · exact token_prefix c
  · rintro ⟨s,t,eqn⟩
    apply (ambiguity_right_margin c w).mpr _ code
    exact spaced_prefix c 0 (eqn ▸ products_spaced c s)

/-- Reversing the preceding result handles a^c b, including c = 0. -/
theorem left_marker_completion (c : ℕ) (w : Word Bool)
    (code : NamedCode (addToken (pair [a] (run c ++ [b])) w)) :
    Completable (addToken (pair [a] (run c ++ [b])) w) := by
  let v := addToken (pair [a] (run c ++ [b])) w
  have eqn : (fun k => (v k).reverse) = addToken (tokens c) w.reverse := by
    funext k
    rcases k with _ | (_ | _) <;> simp [v,addToken,pair,tokens,run]
  have code' : NamedCode (addToken (tokens c) w.reverse) := eqn ▸ code.reverse
  have hc := right_marker_completion c w.reverse code'
  rw [←eqn] at hc
  simpa using hc.reverse

end ThreeWordCodes.BinaryGaps
