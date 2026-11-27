module

public import SubalgebraFreeness.LinearPart

/-! # Words with distinguished letters

The rules of the graph criterion have both sides in `D* S D*`. We write such a word as a triple
`(u, s, v)` and decompose longer words into blocks ending at their distinguished letters. -/

@[expose] public section
namespace SubalgebraFreeness

variable {D S ι : Type*}

/-- A word of `D* S D*`: the letters before the distinguished letter, the distinguished letter,
and the letters after it. -/
abbrev Vertex (D S : Type*) := List D × S × List D

/-- A rule letter `zᵢ` placed in a left context `u` and a right context `v`. -/
abbrev Edge (D ι : Type*) := List D × ι × List D

/-- A word over `D` inside an alphabet `D ⊕ S`. -/
def dword (u : List D) : FreeMonoid (D ⊕ S) := FreeMonoid.ofList (u.map Sum.inl)

/-- The word of a vertex. -/
def vword (x : Vertex D S) : FreeMonoid (D ⊕ S) :=
  FreeMonoid.ofList (x.1.map Sum.inl ++ Sum.inr x.2.1 :: x.2.2.map Sum.inl)

/-- Surround a vertex by a left and a right context. -/
def put (u : List D) (x : Vertex D S) (v : List D) : Vertex D S := (u ++ x.1, x.2.1, x.2.2 ++ v)

theorem vword_eq (x : Vertex D S) :
    vword x = dword x.1 * FreeMonoid.of (Sum.inr x.2.1) * dword x.2.2 := by
  simp [vword, dword, FreeMonoid.ext_iff]

theorem vword_put (u : List D) (x : Vertex D S) (v : List D) :
    vword (put u x v) = dword u * vword x * dword v := by
  simp [vword, put, dword, FreeMonoid.ext_iff]

theorem dword_nil : (dword [] : FreeMonoid (D ⊕ S)) = 1 := rfl

/-- The position of the first right letter determines a splitting. -/
theorem map_inl_append_inr_inj {u u' : List D} {s s' : S} {w w' : List (D ⊕ S)}
    (h : u.map Sum.inl ++ Sum.inr s :: w = u'.map Sum.inl ++ Sum.inr s' :: w') :
    u = u' ∧ s = s' ∧ w = w' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil => simpa using h
    | cons d u' => simp at h
  | cons d u ih =>
    cases u' with
    | nil => simp at h
    | cons d' u' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

theorem vword_injective : Function.Injective (vword : Vertex D S → FreeMonoid (D ⊕ S)) := by
  rintro ⟨u, s, v⟩ ⟨u', s', v'⟩ h
  obtain ⟨h1, h2, h3⟩ := map_inl_append_inr_inj (congrArg FreeMonoid.toList h)
  have h3' : v = v' := (List.map_inj_right Sum.inl_injective).mp h3
  subst h1 h2 h3'
  rfl

theorem vword_ne_one (x : Vertex D S) : vword x ≠ 1 := by
  intro h
  have := congrArg (fun w => w.toList.length) h
  simp [vword] at this

/-! ### Blocks -/

/-- A word over `D ⊕ S` whose distinguished letters are `s₁, …, sₖ`, written as the blocks
`(u₀, s₁), …, (uₖ₋₁, sₖ)` followed by the final word `uₖ`. -/
abbrev Out (D S : Type*) := List (List D × S) × List D

/-- The word of a block decomposition. -/
def flatOut (o : Out D S) : FreeMonoid (D ⊕ S) :=
  FreeMonoid.ofList ((o.1.flatMap fun p => p.1.map Sum.inl ++ [Sum.inr p.2]) ++ o.2.map Sum.inl)

private theorem flatOut_list_inj {sb sb' : List (List D × S)} {c c' : List D}
    (h : (sb.flatMap fun p => p.1.map Sum.inl ++ [Sum.inr p.2]) ++ c.map Sum.inl =
      (sb'.flatMap fun p => p.1.map Sum.inl ++ [Sum.inr p.2]) ++ c'.map Sum.inl) :
    sb = sb' ∧ c = c' := by
  induction sb generalizing sb' with
  | nil =>
    cases sb' with
    | nil =>
      simp only [List.flatMap_nil, List.nil_append, List.map_inj_right Sum.inl_injective] at h
      exact ⟨rfl, h⟩
    | cons p sb' =>
      have : Sum.inr p.2 ∈ c.map (Sum.inl : D → D ⊕ S) := by
        rw [show c.map Sum.inl = _ from by simpa using h]; simp
      simp at this
  | cons p sb ih =>
    cases sb' with
    | nil =>
      have : Sum.inr p.2 ∈ c'.map (Sum.inl : D → D ⊕ S) := by
        rw [show c'.map Sum.inl = _ from by simpa using h.symm]; simp
      simp at this
    | cons p' sb' =>
      simp only [List.flatMap_cons, List.append_assoc, List.singleton_append] at h
      obtain ⟨h₁, h₂, h₃⟩ := map_inl_append_inr_inj h
      obtain ⟨rfl, rfl⟩ := ih h₃
      obtain ⟨a, s⟩ := p
      obtain ⟨a', s'⟩ := p'
      simp only at h₁ h₂
      subst h₁ h₂
      exact ⟨rfl, rfl⟩

theorem flatOut_injective : Function.Injective (flatOut : Out D S → FreeMonoid (D ⊕ S)) := by
  rintro ⟨sb, c⟩ ⟨sb', c'⟩ h
  obtain ⟨rfl, rfl⟩ := flatOut_list_inj (congrArg FreeMonoid.toList h)
  rfl

/-- Words over the presentation alphabet: an initial word over `D`, then rule letters, each
followed by a word over `D`. -/
def flatIn (w : List D × List (ι × List D)) : FreeMonoid (D ⊕ ι) :=
  FreeMonoid.ofList (w.1.map Sum.inl ++ w.2.flatMap fun p => Sum.inr p.1 :: p.2.map Sum.inl)

/-- Cut a word before each rule letter. -/
def splitIn : List (D ⊕ ι) → List D × List (ι × List D)
  | [] => ([], [])
  | .inl d :: w => (d :: (splitIn w).1, (splitIn w).2)
  | .inr i :: w => ([], (i, (splitIn w).1) :: (splitIn w).2)

theorem flatIn_splitIn (w : List (D ⊕ ι)) : (flatIn (splitIn w)).toList = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | inl d => simpa [splitIn, flatIn] using ih
    | inr i => simpa [splitIn, flatIn] using ih

theorem splitIn_map_inl_append (u : List D) (w : List (D ⊕ ι)) :
    splitIn (u.map Sum.inl ++ w) = (u ++ (splitIn w).1, (splitIn w).2) := by
  induction u with
  | nil => rfl
  | cons d u ih => simp [splitIn, ih]

theorem splitIn_flatIn (w : List D × List (ι × List D)) : splitIn (flatIn w).toList = w := by
  obtain ⟨u, zr⟩ := w
  have hz : ∀ zr : List (ι × List D),
      splitIn (zr.flatMap fun p => Sum.inr p.1 :: p.2.map Sum.inl) = ([], zr) := by
    intro zr
    induction zr with
    | nil => rfl
    | cons p zr ih =>
      obtain ⟨i, v⟩ := p
      simp only [List.flatMap_cons, List.cons_append]
      simp [splitIn, splitIn_map_inl_append, ih]
  simp only [flatIn, FreeMonoid.toList_ofList, splitIn_map_inl_append, hz, List.append_nil]

theorem flatIn_bijective : Function.Bijective (flatIn : List D × List (ι × List D) → _) := by
  constructor
  · intro a b h
    rw [← splitIn_flatIn a, ← splitIn_flatIn b, h]
  · intro w
    exact ⟨splitIn w.toList, FreeMonoid.ext (flatIn_splitIn _)⟩

/-- The rule letters with their following words over `D`. -/
def zword (zr : List (ι × List D)) : FreeMonoid (D ⊕ ι) :=
  FreeMonoid.ofList (zr.flatMap fun p => Sum.inr p.1 :: p.2.map Sum.inl)

theorem flatIn_eq (u : List D) (zr : List (ι × List D)) : flatIn (u, zr) = dword u * zword zr := rfl

theorem zword_cons (i : ι) (v : List D) (zr : List (ι × List D)) :
    zword ((i, v) :: zr) = FreeMonoid.of (Sum.inr i) * dword v * zword zr := by
  simp [zword, dword, FreeMonoid.ext_iff]

theorem zword_nil : (zword [] : FreeMonoid (D ⊕ ι)) = 1 := rfl

/-- The word of an edge `u zᵢ v`. -/
def eword (e : Edge D ι) : FreeMonoid (D ⊕ ι) := vword e

theorem eword_injective : Function.Injective (eword : Edge D ι → FreeMonoid (D ⊕ ι)) :=
  vword_injective

/-- Closing a block at a vertex. -/
theorem flatOut_close (sb : List (List D × S)) (c : List D) (x : Vertex D S) (v : List D) :
    flatOut (sb, c) * vword x * dword v =
      flatOut (sb ++ [((put c x v).1, (put c x v).2.1)], (put c x v).2.2) := by
  simp [flatOut, vword, dword, put, FreeMonoid.ext_iff]

theorem flatOut_nil (u : List D) : (flatOut ([], u) : FreeMonoid (D ⊕ S)) = dword u := by
  simp [flatOut, dword]

end SubalgebraFreeness
