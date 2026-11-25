module

public import ThreeWordCodes.Certificate
public import Mathlib.Logic.Equiv.List

/-! # Changing names, reversing words, and composing finite factorizations -/

@[expose] public section
namespace ThreeWordCodes
variable {A B I J K L R S : Type*}

/-- A parsing with arbitrary names for both flank sets and the codewords. -/
def readNamed (l : L → Word A) (v : I → Word A) (r : R → Word A)
    (z : L × Word I × R) : Word A := l z.1 ++ spell v z.2.1 ++ r z.2.2

def ParsingModel (l : L → Word A) (v : I → Word A) (r : R → Word A) : Prop :=
  Function.Bijective (readNamed l v r)

theorem PositiveFactorization.model {M P Q : Finset (Word A)} (h : PositiveFactorization M P Q) :
    ParsingModel (fun x : ↥Q => x.val) (fun x : ↥M => x.val) (fun x : ↥P => x.val) := by
  have same : readNamed (fun x : ↥Q => x.val) (fun x : ↥M => x.val) (fun x : ↥P => x.val) = assemble M P Q := by
    funext z
    simp [readNamed, assemble, spell, List.flatMap_def, concatenate]
  unfold ParsingModel
  rw [same]
  exact h

private noncomputable def imageWords [Fintype I] (f : I → Word A) : Finset (Word A) := by
  classical
  exact Finset.univ.image f

private theorem mem_imageWords [Fintype I] (f : I → Word A) (w : Word A) :
    w ∈ imageWords f ↔ ∃ i, f i = w := by classical simp [imageWords]

private noncomputable def imageNames [Fintype I] {f : I → Word A} (hi : Function.Injective f) :
    I ≃ ↥(imageWords f) :=
  Equiv.ofBijective (fun i => ⟨f i, (mem_imageWords _ _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ e => hi (congrArg Subtype.val e), by
      intro ⟨w, hw⟩
      obtain ⟨i, rfl⟩ := (mem_imageWords _ _).mp hw
      exact ⟨i, rfl⟩⟩

private theorem reverse_transport {l : L → Word A} {v : I → Word A} {r : R → Word A}
    (h : ParsingModel l v r) :
    ParsingModel (fun x => (r x).reverse) (fun i => (v i).reverse) (fun x => (l x).reverse) := by
  let flip (z : R × Word I × L) : L × Word I × R := (z.2.2, z.2.1.reverse, z.1)
  have reverse_read (z : R × Word I × L) :
      readNamed (fun x => (r x).reverse) (fun i => (v i).reverse) (fun x => (l x).reverse) z =
        (readNamed l v r (flip z)).reverse := by
    simp [readNamed, flip, spell_reverse, List.append_assoc]
  constructor
  · rintro ⟨p, s, q⟩ ⟨p', t, q'⟩ he
    simp only [reverse_read, List.reverse_inj] at he
    have hz := h.1 he
    simp [flip] at hz
    simp [hz]
  · intro w
    obtain ⟨⟨q, s, p⟩, he⟩ := h.2 w.reverse
    refine ⟨(p, s.reverse, q), ?_⟩
    rw [reverse_read]
    simpa [flip] using congrArg List.reverse he

private theorem maximal_from_model [Fintype A] {M P Q : Finset (Word A)}
    (h : PositiveFactorization M P Q) : IsMaximalCode (M : Set (Word A)) := by
  cases isEmpty_or_nonempty A with
  | inl empty =>
    refine ⟨positiveFactorization_code h, fun C sub hc => Set.Subset.antisymm ?_ sub⟩
    rintro (_ | ⟨a, w⟩) hw
    · exact (hc.epsilon_notMem hw).elim
    · exact isEmptyElim a
  | inr inhabited => exact maximal_of_finite_flanks M P Q (positiveFactorization_code h) h.2

/-- Finite names in a bijective parsing give concrete finite sets of words. -/
theorem ParsingModel.completion [Fintype A] [Fintype I] [Fintype L] [Fintype R]
    {l : L → Word A} {v : I → Word A} {r : R → Word A} (h : ParsingModel l v r) :
    HasPositiveCompletion (Set.range v) := by
  classical
  obtain ⟨⟨l₀, _, r₀⟩, _⟩ := h.2 []
  have il : Function.Injective l := fun i j e =>
    congrArg Prod.fst (h.1 (a₁ := (i, [], r₀)) (a₂ := (j, [], r₀)) (by simp [readNamed, e]))
  have ir : Function.Injective r := fun i j e =>
    congrArg (fun z : L × Word I × R => z.2.2)
      (h.1 (a₁ := (l₀, [], i)) (a₂ := (l₀, [], j)) (by simp [readNamed, e]))
  have iv : Function.Injective v := by
    intro i j e
    have hs := h.1 (a₁ := (l₀, [i], r₀)) (a₂ := (l₀, [j], r₀)) (by simp [readNamed, e])
    simpa using congrArg (fun z : L × Word I × R => z.2.1) hs
  let e := (imageNames il).prodCongr ((Equiv.listEquivOfEquiv (imageNames iv)).prodCongr (imageNames ir))
  have compat (z : L × Word I × R) :
      assemble (imageWords v) (imageWords r) (imageWords l) (e z) = readNamed l v r z := by
    change l z.1 ++ ((z.2.1.map (imageNames iv)).map Subtype.val).flatten ++ r z.2.2 = _
    simp only [readNamed, spell, List.flatMap_def, List.map_map]
    rfl
  have out : PositiveFactorization (imageWords v) (imageWords r) (imageWords l) := by
    constructor
    · intro x y he
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      simp only [compat] at he
      exact congrArg e (h.1 he)
    · intro w
      obtain ⟨z, he⟩ := h.2 w
      exact ⟨e z, (compat z).trans he⟩
  exact ⟨_, _, _, fun w hw => (mem_imageWords _ w).mpr hw, maximal_from_model out, out⟩

/-- Reverse all words and exchange the two outside factors of a completion. -/
theorem HasPositiveCompletion.reverse [Fintype A] {X : Set (Word A)}
    (h : HasPositiveCompletion X) : HasPositiveCompletion (List.reverse '' X) := by
  obtain ⟨M, L, R, sub, _, pos⟩ := h
  apply (reverse_transport pos.model).completion.mono
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, sub hw⟩, rfl⟩

def IsSuffixFree (X : Set (Word A)) : Prop := InformationTheory.IsPrefixFree (List.reverse '' X)

theorem suffix_case [Fintype A] (X : Finset (Word A))
    (hc : InformationTheory.IsUniquelyDecodable (X : Set (Word A)))
    (hs : IsSuffixFree (X : Set (Word A))) : HasPositiveCompletion (X : Set (Word A)) := by
  classical
  let Y := X.image List.reverse
  have hy : (Y : Set (Word A)) = List.reverse '' (X : Set (Word A)) := by simp [Y]
  have hid : NamedCode (fun x : ↥X => x.val) := (namedCode_iff_range _).mpr
    ⟨Subtype.val_injective, by simpa using hc⟩
  have eqrange : Set.range (fun x : ↥X => x.val.reverse) = (Y : Set (Word A)) := by
    ext w
    simp [Y]
  have hcy := ((namedCode_iff_range _).mp hid.reverse).2
  rw [eqrange] at hcy
  apply (prefix_case Y hcy (hy ▸ hs)).reverse.mono
  intro w hw
  exact ⟨w.reverse, (hy ▸ ⟨w, hw, rfl⟩), List.reverse_reverse _⟩

/-- Substitute a full inner code into a full outer code, with the flanks in their
actual order in the resulting word. All four flank names are retained. -/
theorem ParsingModel.compose {l : L → Word A} {v : B → Word A} {r : R → Word A}
    {p : J → Word B} {e : I → Word B} {q : K → Word B}
    (inner : ParsingModel l v r) (outer : ParsingModel p e q) :
    ParsingModel (fun t : L × J => l t.1 ++ spell v (p t.2))
      (fun i => spell v (e i)) (fun t : K × R => spell v (q t.1) ++ r t.2) := by
  let pack := fun z : (L × J) × Word I × (K × R) =>
    (z.1.1, readNamed p e q (z.1.2, z.2.1, z.2.2.1), z.2.2.2)
  have compat (z : (L × J) × Word I × (K × R)) :
      readNamed (fun t : L × J => l t.1 ++ spell v (p t.2))
        (fun i => spell v (e i)) (fun t : K × R => spell v (q t.1) ++ r t.2) z =
          readNamed l v r (pack z) := by
    simp only [readNamed, pack, spell_append, spell_substitution, List.append_assoc]
  constructor
  · rintro ⟨⟨x, i⟩, s, j, y⟩ ⟨⟨x', i'⟩, t, j', y'⟩ he
    rw [compat, compat] at he
    have h := inner.1 he
    change (x, readNamed p e q (i, s, j), y) = (x', readNamed p e q (i', t, j'), y') at h
    obtain ⟨rfl, mid, rfl⟩ := Prod.ext_iff.mp h |>.imp_right Prod.ext_iff.mp
    have := outer.1 mid
    simpa using this
  · intro w
    obtain ⟨⟨x, s, y⟩, he⟩ := inner.2 w
    obtain ⟨⟨i, t, j⟩, hs⟩ := outer.2 s
    exact ⟨((x, i), t, j, y), by rw [compat]; simpa [pack, hs] using he⟩

end ThreeWordCodes
