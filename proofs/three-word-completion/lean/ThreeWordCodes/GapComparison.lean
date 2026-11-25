module

public import ThreeWordCodes.GapRigidity
public import ThreeWordCodes.Powers
public import ThreeWordCodes.Alphabet

/-! # Forward and reversed readings of ambiguous binary triples

A run list records only the gaps between successive b's. Complete tokens
contribute copies of their internal gap list separated by a boundary gap.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

def layout (i : ℕ) (g : List ℕ) (j h : ℕ) (e : List ℕ) (q : ℕ) :
    Option Bool → Word Bool := addToken (pair [a] (mixed i g j)) (mixed h e q)

private def switchMixed : Option Bool → Option Bool
  | none => some true
  | some true => none
  | some false => some false

theorem swapped_ambiguity {g e : List ℕ} {i j h q : ℕ} (amb : ¬ NamedCode (layout i g j h e q)) :
    ¬ NamedCode (layout h e q i g j) := by
  have switch : (fun x => layout h e q i g j (switchMixed x)) = layout i g j h e q := by
    funext x
    rcases x with _ | (_ | _) <;> rfl
  exact fun code => amb (switch ▸ code.reindex (show Function.Injective switchMixed by decide))

def stripped (g : List ℕ) (j : ℕ) := pair [a] (mixed 0 g j)

private theorem strip_initial {i g j h e q} (bad : ¬ Completable (layout i g j h e q)) :
    ¬ Completable (layout 0 g j 0 e q) := by
  intro hc
  let v := layout 0 g j 0 e q
  let count : Option Bool → ℕ
    | none => h
    | some false => 0
    | some true => i
  let pad (x) := List.replicate (count x) (some false)
  have pure (n : ℕ) : spell v (List.replicate n (some false)) = run n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (a :: ·) ih
  have restore : (fun k => spell v (pad k) ++ v k) = layout i g j h e q := by
    funext k
    change spell v (List.replicate (count k) (some false)) ++ v k = _
    rw [pure]
    rcases k with _ | (_ | _) <;> simp [count,v,layout,addToken,pair,mixed,run]
  exact bad (restore ▸ hc.padLeft pad)

private theorem directed {i g j h e q} (bad : ¬ Completable (layout i g j h e q)) :
    ∃ s, mixed 0 e q <+: spell (stripped g j) s := by
  have marked : (fun k : Bool => k :: (if k then gapTail j g else [])) = stripped g j := by
    funext k
    cases k <;> rfl
  have complete := first_marked_completion (fun k : Bool => if k then gapTail j g else [])
  rw [marked] at complete
  by_contra no
  apply strip_initial bad
  apply greedy_completion complete.1.entries_injective complete.1.entry_ne_nil _ _ no
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ ⟨t,eqn⟩
  rw [←marked] at eqn ⊢
  obtain ⟨rfl,_⟩ := List.cons.inj eqn
  rfl

theorem directed_comparisons {i g j h e q} (bad : ¬ Completable (layout i g j h e q)) :
    (∃ s, mixed 0 e q <+: spell (stripped g j) s) ∧
    (∃ s, mixed 0 e.reverse h <+: spell (stripped g.reverse i) s) := by
  refine ⟨directed bad,directed (i:=j) (h:=q) ?_⟩
  intro rev
  apply bad
  have eqn : (fun x => (layout j g.reverse i q e.reverse h x).reverse) = layout i g j h e q := by
    funext x
    rcases x with _ | (_ | _) <;> simp [layout,addToken,pair,reverse_mixed]
  exact eqn ▸ rev.reverse

theorem run_add (i j : ℕ) : run (i+j) = run i ++ run j := List.replicate_add ..

theorem join_mixed (g e : List ℕ) (i j h q : ℕ) :
    mixed i g j ++ mixed h e q = mixed i (g ++ (j+h)::e) q := by
  have tail (z : List ℕ) : gapTail j z ++ mixed h e q = gapTail q (z ++ (j+h)::e) := by
    induction z with
    | nil => simp [mixed,gapTail,run_add,List.append_assoc]
    | cons k z ih => simp [gapTail,List.append_assoc,ih]
  simp [mixed,List.append_assoc] at tail ⊢
  exact tail g

theorem append_pure (g : List ℕ) (i j k : ℕ) :
    mixed i g j ++ run k = mixed i g (j+k) := by
  have tail : gapTail j g ++ run k = gapTail (j+k) g := by
    induction g with
    | nil => exact (run_add ..).symm
    | cons r g ih => simp [gapTail,List.append_assoc,ih]
  simp [mixed,List.append_assoc,tail]

/-- Gaps between consecutive complete tokens must have length at least j. -/
inductive Copies (g : List ℕ) (j : ℕ) : List ℕ → Prop
  | one : Copies g j g
  | more {e : List ℕ} (rest : Copies g j e) (h : ℕ) : Copies g j (g ++ (j+h)::e)

private theorem product_shape (g : List ℕ) (j : ℕ) (s : Word Bool) :
    (∃ k, spell (stripped g j) s = run k) ∨
    ∃ i e q, spell (stripped g j) s = mixed i e q ∧ Copies g j e ∧ j ≤ q := by
  induction s with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons x s ih =>
    cases x <;> rcases ih with ⟨k,he⟩ | ⟨i,e,q,he,rep,bound⟩
    · left
      exact ⟨k+1,congrArg (a :: ·) he⟩
    · right
      exact ⟨i+1,e,q,congrArg (a :: ·) he,rep,bound⟩
    · right
      exact ⟨0,g,j+k,by rw [spell_cons,he]; exact append_pure .., .one, by omega⟩
    · right
      exact ⟨0,g ++ (j+i)::e,q,by rw [spell_cons,he]; exact join_mixed .., .more rep i,bound⟩

def initial : Word Bool → ℕ
  | [] => 0
  | false :: t => initial t + 1
  | true :: _ => 0

private theorem initial_run (i : ℕ) : initial (run i) = i := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (·+1) ih

theorem initial_b (i : ℕ) (w : Word Bool) : initial (run i ++ b :: w) = i := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (·+1) ih

private theorem initial_le {u v : Word Bool} (p : u <+: v) : initial u ≤ initial v := by
  obtain ⟨t,rfl⟩ := p
  induction u with
  | nil => exact Nat.zero_le _
  | cons a u ih => cases a with
    | false => exact Nat.succ_le_succ ih
    | true => rfl

theorem pure_prefix_bound {m s : ℕ} {t : Word Bool} (p : run m <+: run s ++ b :: t) : m ≤ s := by
  simpa only [initial_run,initial_b] using initial_le p

theorem marked_not_prefix_pure (m s : ℕ) (t : Word Bool) : ¬ run s ++ b :: t <+: run m := by
  intro p
  have elem : b ∈ run s ++ b :: t := by simp
  have impossible := p.sublist.subset elem
  simp [run,a,b] at impossible

theorem marked_prefix {i h : ℕ} {s t : Word Bool}
    (p : run i ++ b :: s <+: run h ++ b :: t) : i = h ∧ s <+: t := by
  obtain ⟨r,eqn⟩ := p
  have e : run i ++ b :: (s ++ r) = run h ++ b :: t := by simpa [List.append_assoc] using eqn
  have hi : i = h := by simpa only [initial_b] using congrArg initial e
  subst h
  exact ⟨rfl, r,(List.cons.inj (List.append_cancel_left e)).2⟩

theorem tail_prefix {g e : List ℕ} {j q : ℕ} (p : gapTail j g <+: gapTail q e) :
    g <+: e ∧ j ≤ (e[g.length]?).getD q := by
  induction g generalizing e with
  | nil =>
    refine ⟨List.nil_prefix,?_⟩
    cases e with
    | nil => simpa [gapTail,initial_run] using initial_le p
    | cons h e => simpa [gapTail,initial_run,initial_b] using initial_le p
  | cons k g ih =>
    cases e with
    | nil =>
      have element : b ∈ gapTail j (k::g) := by simp [gapTail]
      have bad := p.sublist.subset element
      simp [gapTail,run,a,b] at bad
    | cons h e =>
      obtain ⟨rfl, next⟩ := marked_prefix p
      obtain ⟨⟨r,hr⟩,bound⟩ := ih next
      exact ⟨⟨r,congrArg (k :: ·) hr⟩,by simpa using bound⟩

theorem mixed_injective {i h j q : ℕ} {g e : List ℕ} (eqn : mixed i g j = mixed h e q) :
    i = h ∧ g = e ∧ j = q := by
  have left : mixed i g j <+: mixed h e q := by rw [eqn]
  have right : mixed h e q <+: mixed i g j := by rw [eqn]
  obtain ⟨hi,one⟩ := marked_prefix left
  obtain ⟨_,two⟩ := marked_prefix right
  obtain ⟨pg,le⟩ := tail_prefix one
  obtain ⟨pe,ge⟩ := tail_prefix two
  obtain rfl : g = e := pg.eq_of_length_le pe.length_le
  simp at le ge
  exact ⟨hi,rfl,Nat.le_antisymm le ge⟩

/-- Exact forward consequence of greedy reading before passing to residues:
the internal gaps of V are an initial segment of complete copies of U's gaps,
and its terminal a-run fits into the next gap or the last outside margin. -/
theorem gap_list_of_reading {g j e q} (read : ∃ s, mixed 0 e q <+: spell (stripped g j) s) :
    ∃ full last, Copies g j full ∧ j ≤ last ∧ e <+: full ∧ q ≤ (full[e.length]?).getD last := by
  obtain ⟨s,hs⟩ := read
  rcases product_shape g j s with ⟨k,eqn⟩ | ⟨i',full,last,eqn,rep,bound⟩
  · rw [eqn] at hs
    have elem : b ∈ mixed 0 e q := by simp [mixed,run]
    have bad := hs.sublist.subset elem
    simp [run,a,b] at bad
  · rw [eqn] at hs
    obtain ⟨_,pr⟩ := marked_prefix hs
    exact ⟨full,last,rep,bound,tail_prefix pr⟩

theorem gap_list_comparison {i g j h e q} (bad : ¬ Completable (layout i g j h e q)) :
    ∃ full last, Copies g j full ∧ j ≤ last ∧ e <+: full ∧ q ≤ (full[e.length]?).getD last :=
  gap_list_of_reading (directed bad)

end ThreeWordCodes.BinaryGaps
