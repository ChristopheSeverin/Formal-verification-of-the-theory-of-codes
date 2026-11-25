module

public import ThreeWordCodes.ShortGaps

/-! # One-marker triples and the common-block ambiguity

The alphabet has two letters. Besides the letter a, the middle name spells
a^k b a^l. The third name can spell an arbitrary word.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

def oneMarker (k l : ℕ) (w : Word Bool) :=
  addToken (pair [a] (mixed k [] l)) w

private abbrev pureName : Option Bool := some false
private abbrev mixedName : Option Bool := some true
private abbrev extraName : Option Bool := none
private def pureNames (n : ℕ) : Word (Option Bool) := List.replicate n pureName

private theorem pureNames_spell (k l : ℕ) (w : Word Bool) (n : ℕ) :
    spell (oneMarker k l w) (pureNames n) = run n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (a :: ·) ih

private theorem pad_marker_left {k l : ℕ} {w : Word Bool} (hc : Completable (oneMarker 0 l w)) :
    Completable (oneMarker k l w) := by
  let pad (x : Option Bool) := if x = mixedName then pureNames k else []
  have eqn : (fun x => spell (oneMarker 0 l w) (pad x) ++ oneMarker 0 l w x) = oneMarker k l w := by
    funext x
    rcases x with _ | (_ | _)
    · rfl
    · rfl
    · change spell (oneMarker 0 l w) (pureNames k) ++ mixed 0 [] l = mixed k [] l
      rw [pureNames_spell]
      rfl
  exact eqn ▸ hc.padLeft pad

private theorem pad_marker_right {k l : ℕ} {w : Word Bool} (hc : Completable (oneMarker k 0 w)) :
    Completable (oneMarker k l w) := by
  let pad (x : Option Bool) := if x = mixedName then pureNames l else []
  have eqn : (fun x => oneMarker k 0 w x ++ spell (oneMarker k 0 w) (pad x)) = oneMarker k l w := by
    funext x
    rcases x with _ | (_ | _)
    · simp [pad,mixedName,oneMarker,addToken]
    · simp [pad,mixedName,oneMarker,addToken,pair]
    · change mixed k [] 0 ++ spell (oneMarker k 0 w) (pureNames l) = mixed k [] l
      rw [pureNames_spell,append_pure,Nat.zero_add]
  exact eqn ▸ hc.padRight pad

/-- In every triple lacking a positive completion all gaps of the third word
are at least both margins of the one-marker word. Ambiguity is sufficient. -/
theorem one_marker_spacing {k l : ℕ} {w : Word Bool} (bad : ¬ Completable (oneMarker k l w)) :
    Spaced k 0 w ∧ Spaced l 0 w := by
  constructor
  · apply (ambiguity_left_margin k w).mp
    exact fun code => bad (pad_marker_right (left_marker_completion k w code))
  · apply (ambiguity_right_margin l w).mp
    exact fun code => bad (pad_marker_left (right_marker_completion l w code))

theorem one_marker_gaps {k l h q : ℕ} {gs : List ℕ}
    (bad : ¬ Completable (oneMarker k l (mixed h gs q))) :
    ∀ g ∈ gs, max k l ≤ g := by
  obtain ⟨left,right⟩ := one_marker_spacing bad
  exact fun g hg => max_le ((gaps_spec ..).mp left g hg) ((gaps_spec ..).mp right g hg)

private def body (gs : List ℕ) := mixed 0 gs 0

private theorem joined_body (g : ℕ) (gs : List ℕ) :
    body (g::gs) = [b] ++ run g ++ body gs := by
  simp [body,mixed,gapTail,run]

/-- If each internal gap fits both margins, surrounding a body by these margins
gives a product on the first two names whose first token is the mixed one. -/
private theorem body_reading (w : Word Bool) (k l : ℕ) (gs : List ℕ)
    (bound : ∀ g ∈ gs, k+l ≤ g) :
    ∃ s, spell (oneMarker k l w) (mixedName::s) = run k ++ body gs ++ run l := by
  induction gs with
  | nil => exact ⟨[],by simp [oneMarker,addToken,pair,body,mixed,gapTail,mixedName,run]⟩
  | cons g gs ih =>
    obtain ⟨s,eqn⟩ := ih (fun t ht => bound t (by simp [ht]))
    let n := g - (k+l)
    refine ⟨pureNames n ++ mixedName::s,?_⟩
    simp only [spell_cons,spell_append,pureNames_spell,eqn]
    change (run k ++ b :: run l) ++ (run n ++ (run k ++ body gs ++ run l)) = _
    have gap : run l ++ (run n ++ run k) = run g := by
      rw [←run_add,←run_add]
      exact congrArg run (by have := bound g (by simp); dsimp [n]; omega)
    rw [joined_body]
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
      congrArg (fun t => run k ++ b :: (t ++ (body gs ++ run l))) gap

theorem long_gap_ambiguity (k l : ℕ) (gs : List ℕ) (bound : ∀ g ∈ gs, k+l ≤ g) :
    ¬ NamedCode (oneMarker k l (mixed 0 gs 0)) := by
  let v := oneMarker k l (body gs)
  obtain ⟨s,reading⟩ := body_reading (body gs) k l gs bound
  have eqn : spell v (pureNames k ++ [extraName] ++ pureNames l) = spell v (mixedName::s) := by
    rw [reading]
    simp only [v,spell_append,pureNames_spell,spell_cons,spell_nil,List.append_nil]
    rfl
  intro code
  have he := code eqn
  cases k <;> simp [pureNames,extraName,mixedName,pureName,List.replicate_succ] at he

/-- The repeated-block ambiguity in Section 3. A body T with sufficiently long
gaps may be repeated any number of times with the separator a^m. -/
theorem common_block_ambiguity (k l m : ℕ) (gs : List ℕ) (j : ℕ)
    (pos : 0 < k) (lk : k ≤ m) (ll : l ≤ m) (bound : ∀ g ∈ gs, k+l ≤ g) :
    let t := mixed 0 gs 0
    let w := t ++ wordPow (run m ++ t) j
    ¬ NamedCode (oneMarker k l w) := by
  let t := body gs
  let w := t ++ wordPow (run m ++ t) j
  let v := oneMarker k l w
  obtain ⟨s,reading⟩ := body_reading w k l gs bound
  change ¬ NamedCode v
  change spell v (mixedName :: s) = run k ++ t ++ run l at reading
  have commuting : w ++ run m ++ t = t ++ run m ++ w := by
    have fixed := wordPow_comm (run m ++ t) j 1
    simpa [w,List.append_assoc] using congrArg (t ++ ·) fixed
  have eqn : spell v (pureNames k ++ [extraName] ++ pureNames (m-k) ++ (mixedName :: s)) =
      spell v ((mixedName :: s) ++ pureNames (m-l) ++ [extraName] ++ pureNames l) := by
    simp only [spell_append,show spell v [extraName] = w from (List.append_nil w),
      show ∀ n, spell v (pureNames n) = run n from pureNames_spell k l w,reading]
    have first : run (m-k) ++ run k = run m := by rw [←run_add,Nat.sub_add_cancel lk]
    have last : run l ++ run (m-l) = run m := by rw [←run_add,Nat.add_sub_of_le ll]
    have lift := congrArg (fun x => run k ++ x ++ run l) commuting
    simp only [List.append_assoc] at lift ⊢
    rw [←List.append_assoc (run (m-k)) (run k), first,
      ←List.append_assoc (run l) (run (m-l)), last]
    exact lift
  intro code
  have contradiction := code eqn
  cases k with
  | zero => omega
  | succ k => simp [pureNames,extraName,mixedName,pureName,List.replicate_succ] at contradiction

private theorem body_join (x y : List ℕ) (c : ℕ) :
    mixed 0 (x ++ c::y) 0 = mixed 0 x 0 ++ run c ++ mixed 0 y 0 := by
  rw [append_pure,join_mixed,Nat.zero_add,Nat.add_zero]

private theorem repeated_body (H : List ℕ) (c n : ℕ) :
    mixed 0 (H ++ wordPow (c::H) n) 0 =
      mixed 0 H 0 ++ wordPow (run c ++ mixed 0 H 0) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wordPow_succ,←List.append_assoc H,body_join,ih,wordPow_succ]
    simp [List.append_assoc]

/-- An exact gap criterion for ambiguity of a, a^k b a^l, and a word that
begins and ends in b. Both margins may be zero. -/
theorem one_marker_ambiguity_iff (k l : ℕ) (gs : List ℕ) :
    ¬ NamedCode (oneMarker k l (mixed 0 gs 0)) ↔
      (∀ z ∈ gs, k+l ≤ z) ∨
      ∃ H : List ℕ, ∃ c n : ℕ, max k l ≤ c ∧ c < k+l ∧ (∀ z ∈ H, k+l ≤ z) ∧
        gs = H ++ wordPow (c::H) (n+1) := by
  constructor
  · intro amb
    by_cases short : ∃ z ∈ gs, z < k+l
    · obtain ⟨H,c,n,small,long,eqn⟩ := short_gap_blocks amb short
      have cmem : c ∈ gs := by rw [eqn,wordPow_succ']; simp
      have lower := one_marker_gaps (fun hc => amb hc.1) c cmem
      exact Or.inr ⟨H,c,n,lower,small,long,eqn⟩
    · push Not at short
      exact Or.inl short
  · rintro (long | ⟨H,c,n,lower,small,hl,rfl⟩)
    · exact long_gap_ambiguity k l gs long
    · rw [repeated_body]
      have ⟨hk,hl'⟩ := max_le_iff.mp lower
      exact common_block_ambiguity k l c H (n+1) (by omega) hk hl' hl

end ThreeWordCodes.BinaryGaps
