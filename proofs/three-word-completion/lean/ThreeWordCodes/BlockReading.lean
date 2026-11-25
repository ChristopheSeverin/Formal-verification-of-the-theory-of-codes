module

public import ThreeWordCodes.GapComparison

/-! # Locating the first different marker group in Lemma 3 -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
namespace BlockReading

private inductive Kind
  | single | body
  deriving DecidableEq

private abbrev free : Option Bool := some false
private def name : Kind → Option Bool | .single => some true | .body => none
private def margin (n : ℕ) : Kind → ℕ | .single => n | .body => 0
private def inside (g : List ℕ) : Kind → List ℕ | .single => [] | .body => g

private def gaps (i j : ℕ) (g : List ℕ) (k : Kind) : List (ℕ × Kind) → List ℕ
  | [] => inside g k
  | (pad,z) :: rest => inside g k ++ (margin j k + pad + margin i z) :: gaps i j g z rest

private def ending (n : ℕ) (k : Kind) : List (ℕ × Kind) → ℕ
  | [] => margin n k
  | (_,z)::rest => ending n z rest

private def names (k : Kind) (last : ℕ) : List (ℕ × Kind) → Word (Option Bool)
  | [] => name k :: List.replicate last free
  | (pad,z) :: rest => name k :: (List.replicate pad free ++ names z last rest)

private theorem forms (s : Word (Option Bool)) :
    (∃ n, s = List.replicate n free) ∨
    ∃ h k parts t, s = List.replicate h free ++ names k t parts := by
  induction s with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons x s ih =>
    rcases x with _ | (_ | _) <;> rcases ih with ⟨n,rfl⟩ | ⟨h,k,z,t,rfl⟩
    · exact Or.inr ⟨0,.body,[],n,rfl⟩
    · exact Or.inr ⟨0,.body,(h,k)::z,t,rfl⟩
    · exact Or.inl ⟨n+1,rfl⟩
    · exact Or.inr ⟨h+1,k,z,t,rfl⟩
    · exact Or.inr ⟨0,.single,[],n,rfl⟩
    · exact Or.inr ⟨0,.single,(h,k)::z,t,rfl⟩

private theorem pure_spell (i j : ℕ) (g : List ℕ) (n : ℕ) :
    spell (layout i [] j 0 g 0) (List.replicate n free) = run n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (a :: ·) ih

private theorem core_spell (i j : ℕ) (g : List ℕ) (k : Kind) :
    layout i [] j 0 g 0 (name k) = mixed (margin i k) (inside g k) (margin j k) := by
  cases k <;> rfl

private theorem names_spell (i j : ℕ) (g : List ℕ) (k : Kind) (z : List (ℕ × Kind)) (t : ℕ) :
    spell (layout i [] j 0 g 0) (names k t z) = mixed (margin i k) (gaps i j g k z) (ending j k z + t) := by
  induction z generalizing k with
  | nil => simpa only [names,spell_cons,core_spell,pure_spell,gaps,ending] using
      append_pure (inside g k) (margin i k) (margin j k) t
  | cons p z ih =>
    obtain ⟨pad,l⟩ := p
    simp only [names,spell_cons,spell_append,core_spell,pure_spell,ih,gaps,ending]
    rw [←List.append_assoc,append_pure,join_mixed]

private theorem spell_shape (i j : ℕ) (g : List ℕ) (h : ℕ) (k : Kind) (z : List (ℕ × Kind)) (t : ℕ) :
    spell (layout i [] j 0 g 0) (List.replicate h free ++ names k t z) =
      mixed (h+margin i k) (gaps i j g k z) (ending j k z + t) := by
  simp [pure_spell,names_spell,mixed,run_add,List.append_assoc]

private theorem groups_unique (i j : ℕ) (g : List ℕ)
    (apart : ∀ x y, gaps i j g .body x ≠ gaps i j g .single y)
    (k l : Kind) (x y : List (ℕ × Kind)) (he : gaps i j g k x = gaps i j g l y) :
    k = l ∧ x = y := by
  induction x generalizing k l y with
  | nil =>
    have kl : k = l := by cases k <;> cases l <;> first | rfl | exact (apart _ _ he).elim | exact (apart _ _ he.symm).elim
    subst l
    refine ⟨rfl,?_⟩
    cases y with
    | nil => rfl
    | cons p y =>
      obtain ⟨pad,z⟩ := p
      have := congrArg List.length he
      simp [gaps] at this
  | cons p x ih =>
    obtain ⟨kpad,z⟩ := p
    have kl : k = l := by cases k <;> cases l <;> first | rfl | exact (apart _ _ he).elim | exact (apart _ _ he.symm).elim
    subst l
    refine ⟨rfl,?_⟩
    cases y with
    | nil =>
      have := congrArg List.length he
      simp [gaps] at this
    | cons p y =>
      obtain ⟨lpad,z'⟩ := p
      obtain ⟨mark,tail⟩ := List.cons.inj (List.append_cancel_left he)
      obtain ⟨rfl,rfl⟩ := ih z z' y tail
      have : kpad = lpad := by omega
      simp [this]

private theorem first_difference {i j : ℕ} {g : List ℕ}
    (bad : ¬ NamedCode (layout i [] j 0 g 0)) :
    ∃ p q, gaps i j g .body p = gaps i j g .single q := by
  classical
  by_contra! apart
  apply bad
  intro s t he
  rcases forms s with ⟨n,rfl⟩ | ⟨h,k,p,t₀,rfl⟩ <;>
    rcases forms t with ⟨m,rfl⟩ | ⟨h',l,q,t₁,rfl⟩
  · simp only [pure_spell] at he
    have en := congrArg List.length he
    simp [run] at en
    rw [en]
  · rw [pure_spell,spell_shape] at he
    have yes : b ∈ mixed (h'+margin i l) (gaps i j g l q) (ending j l q + t₁) := by simp [mixed]
    rw [← he] at yes
    simp [run,a,b] at yes
  · rw [pure_spell,spell_shape] at he
    have yes : b ∈ mixed (h+margin i k) (gaps i j g k p) (ending j k p + t₀) := by simp [mixed]
    rw [he] at yes
    simp [run,a,b] at yes
  · simp only [spell_shape] at he
    obtain ⟨left,eqn,right⟩ := mixed_injective he
    obtain ⟨rfl,rfl⟩ := groups_unique i j g apart k l p q eqn
    have hh : h = h' := Nat.add_right_cancel left
    have tt : t₀ = t₁ := Nat.add_left_cancel right
    rw [hh,tt]

private theorem begins_body (i j : ℕ) (g : List ℕ) (p : List (ℕ × Kind)) : g <+: gaps i j g .body p := by
  cases p with
  | nil => exact List.prefix_refl _
  | cons p ps => exact ⟨_,rfl⟩

private theorem leading_singles (i j : ℕ) (g : List ℕ) (q : List (ℕ × Kind)) :
    (∀ z ∈ gaps i j g .single q, i+j ≤ z) ∨
    ∃ L c rest, (∀ z ∈ L, i+j ≤ z) ∧ gaps i j g .single q = L ++ c :: (g ++ rest) := by
  induction q with
  | nil => left; simp [gaps,inside]
  | cons p q ih =>
    obtain ⟨pad,k⟩ := p
    cases k with
    | body =>
      obtain ⟨s,hs⟩ := begins_body i j g q
      exact Or.inr ⟨[], j+pad, s, by simp, by simp [gaps, inside, margin] at hs ⊢; exact hs.symm⟩
    | single =>
      rcases ih with h | ⟨L,c,rest,long,eqn⟩
      · left
        simp only [gaps,inside,margin,List.nil_append,List.forall_mem_cons]
        exact ⟨by omega,h⟩
      · right
        exact ⟨(j+pad+i)::L,c,rest,by rw [List.forall_mem_cons]; exact ⟨by omega,long⟩,by simp [gaps,inside,margin,eqn]⟩

/-- If g contains a short gap, a distinct parsing must start a second copy
after a nonempty group of singleton markers. Its strictly internal singleton
joins are all long. -/
theorem overlap_witness {i j : ℕ} {g : List ℕ} (bad : ¬ NamedCode (layout i [] j 0 g 0))
    (short : ∃ z ∈ g, z < i+j) :
    ∃ L c tail, (∀ z ∈ L, i+j ≤ z) ∧ g <+: L ++ c :: (g ++ tail) := by
  obtain ⟨p,q,eqn⟩ := first_difference bad
  have start := begins_body i j g p
  rw [eqn] at start
  rcases leading_singles i j g q with all | ⟨L,c,tail,long,he⟩
  · obtain ⟨z,hz,small⟩ := short
    exact (Nat.not_le_of_lt small (all _ (start.sublist.subset hz))).elim
  · exact ⟨L,c,tail,long,he ▸ start⟩

end BlockReading
end ThreeWordCodes.BinaryGaps
