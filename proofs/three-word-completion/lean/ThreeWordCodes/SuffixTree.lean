module

public import ThreeWordCodes.Indicator
public import Mathlib.Data.List.Infix

/-! # Suffix trees encoded on a complete prefix code -/

@[expose] public section
namespace ThreeWordCodes
open WordSeries
open scoped ThreeWordCodes.WordSeries
variable {A B : Type*}

noncomputable def suffixNodes (E : Finset (Word B)) : Finset (Word B) := by
  classical
  exact insert [] (E.biUnion fun e => e.tails.toFinset.filter (· ≠ e))

@[simp] theorem mem_suffixNodes {E : Finset (Word B)} {q : Word B} :
    q ∈ suffixNodes E ↔ q = [] ∨ ∃ e ∈ E, q <:+ e ∧ q ≠ e := by
  classical simp [suffixNodes, List.mem_tails]

theorem suffixNodes_closed {E : Finset (Word B)} {q t : Word B}
    (hq : q ∈ suffixNodes E) (ht : t <:+ q) : t ∈ suffixNodes E := by
  rw [mem_suffixNodes] at hq ⊢
  rcases hq with rfl | ⟨e,he,hs,hn⟩
  · exact Or.inl (List.eq_nil_of_suffix_nil ht)
  · exact Or.inr ⟨e, he, ht.trans hs, fun eq => hn (hs.eq_of_length_le (eq ▸ ht.length_le))⟩

noncomputable def suffixLeaves [Fintype B] (J : Finset (Word B)) : Finset (Word B) := by
  classical exact (J.biUnion fun t => Finset.univ.image (fun a : B => a :: t)) \ J

theorem mem_suffixLeaves [Fintype B] {J : Finset (Word B)} {q : Word B} :
    q ∈ suffixLeaves J ↔ (∃ a t, t ∈ J ∧ a :: t = q) ∧ q ∉ J := by
  classical simp [suffixLeaves]; grind

theorem suffix_subset [Fintype B] {E : Finset (Word B)} (hn : [] ∉ E)
    (hs : ∀ x ∈ E, ∀ y ∈ E, x <:+ y → x = y) : E ⊆ suffixLeaves (suffixNodes E) := by
  intro e he
  have ne : e ≠ [] := by rintro rfl; exact hn he
  have out : e ∉ suffixNodes E := by
    intro h
    rcases mem_suffixNodes.mp h with z | ⟨y,hy,s,n⟩
    · exact ne z
    · exact n (hs e he y hy s)
  cases e with
  | nil => contradiction
  | cons a t =>
    refine mem_suffixLeaves.mpr ⟨⟨a,t,mem_suffixNodes.mpr (Or.inr ⟨_,he,?_,?_⟩),rfl⟩,out⟩
    · exact ⟨[a],rfl⟩
    · intro e
      have := congrArg List.length e
      simp at this

noncomputable def codedSet (v : B → Word A) (S : Finset (Word B)) : Finset (Word A) := by
  classical exact S.image (spell v)

@[simp] theorem mem_codedSet {v : B → Word A} {S : Finset (Word B)} {w : Word A} :
    w ∈ codedSet v S ↔ ∃ s ∈ S, spell v s = w := by classical simp [codedSet]

/-- Prefix-free tokens reflect the prefix relation between completely read name sequences. -/
theorem prefix_reflection {v : B → Word A} (hi : Function.Injective v)
    (hn : ∀ i, v i ≠ []) (hp : InformationTheory.IsPrefixFree (Set.range v))
    {s t : Word B} (h : spell v s <+: spell v t) : s <+: t := by
  induction s generalizing t with
  | nil => exact List.nil_prefix
  | cons i s ih =>
    obtain ⟨r, e⟩ := h
    cases t with
    | nil =>
      have he : v i ++ (spell v s ++ r) = [] := by simpa [List.append_assoc] using e
      exact (hn i (List.append_eq_nil_iff.mp he).1).elim
    | cons j t =>
      have he : v i ++ (spell v s ++ r) = v j ++ spell v t := by simpa [List.append_assoc] using e
      have hij : i = j := by
        apply hi
        rcases List.append_eq_append_iff.mp he with ⟨z,hz,_⟩ | ⟨z,hz,_⟩
        · exact hp _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ ⟨z,hz.symm⟩
        · exact (hp _ ⟨j,rfl⟩ _ ⟨i,rfl⟩ ⟨z,hz.symm⟩).symm
      subst j
      obtain ⟨q, eqn⟩ := ih ⟨r, List.append_cancel_left he⟩
      exact ⟨q, congrArg (List.cons i) eqn⟩

/-- The suffix-tree polynomial after an injective coding. The one-letter words
on the outer alphabet become the individual inner codewords. -/
theorem coded_suffix_series [Fintype B] (v : B → Word A) (hi : NamedCode v)
    (E : Finset (Word B)) (D : Finset (Word A))
    (hD : ∀ w, w ∈ D ↔ ∃ b, v b = w) :
    indicator (codedSet v (suffixLeaves (suffixNodes E))) + indicator (codedSet v (suffixNodes E)) =
      epsilon + (indicator D ⋆ indicator (codedSet v (suffixNodes E))) := by
  classical
  let J := suffixNodes E
  let C := suffixLeaves J
  let T := codedSet v J
  let M := codedSet v C
  have inj : Function.Injective (fun z : ↥D × ↥T => z.1.val ++ z.2.val) := by
    rintro ⟨⟨u,hu⟩,⟨t,ht⟩⟩ ⟨⟨x,hx⟩,⟨s,hs⟩⟩ he
    obtain ⟨i,rfl⟩ := (hD _).mp hu
    obtain ⟨j,rfl⟩ := (hD _).mp hx
    obtain ⟨t',_,rfl⟩ := mem_codedSet.mp ht
    obtain ⟨s',_,rfl⟩ := mem_codedSet.mp hs
    obtain ⟨rfl,rfl⟩ := List.cons.inj (hi (a₁ := i :: t') (a₂ := j :: s') he)
    rfl
  change indicator M + indicator T = epsilon + (indicator D ⋆ indicator T)
  rw [indicator_product inj]
  have empty : [] ∈ T := mem_codedSet.mpr ⟨[],mem_suffixNodes.mpr (Or.inl rfl),rfl⟩
  have get {w : Word A} (h : w ∈ joinSets D T) : ∃ i t, t ∈ J ∧ spell v (i::t) = w := by
    obtain ⟨u,hu,s,hs,rfl⟩ := mem_joinSets.mp h
    obtain ⟨i,rfl⟩ := (hD _).mp hu
    obtain ⟨t,ht,rfl⟩ := mem_codedSet.mp hs
    exact ⟨i,t,ht,rfl⟩
  have put (i : B) {t : Word B} (ht : t ∈ J) : spell v (i::t) ∈ joinSets D T :=
    mem_joinSets.mpr ⟨_, (hD _).mpr ⟨i,rfl⟩, _, mem_codedSet.mpr ⟨t,ht,rfl⟩, rfl⟩
  have noRoot : [] ∉ joinSets D T := by
    intro h
    obtain ⟨i,t,_,he⟩ := get h
    exact (List.cons_ne_nil i t) (hi (a₂ := []) he)
  have criterion (w : Word A) : w ∈ M ↔ w ∈ joinSets D T ∧ w ∉ T := by
    constructor
    · intro h
      obtain ⟨q,hq,rfl⟩ := mem_codedSet.mp h
      obtain ⟨⟨i,t,ht,rfl⟩, hn⟩ := mem_suffixLeaves.mp hq
      refine ⟨put i ht, ?_⟩
      intro bad
      obtain ⟨s,hs,e⟩ := mem_codedSet.mp bad
      exact hn (hi e ▸ hs)
    · rintro ⟨h, notT⟩
      obtain ⟨i,t,ht,rfl⟩ := get h
      apply mem_codedSet.mpr
      exact ⟨i::t, mem_suffixLeaves.mpr ⟨⟨i,t,ht,rfl⟩,fun bad => notT (mem_codedSet.mpr ⟨_,bad,rfl⟩)⟩,rfl⟩
  have child {w : Word A} (hw : w ∈ T) (hn : w ≠ []) : w ∈ joinSets D T := by
    obtain ⟨q,hq,rfl⟩ := mem_codedSet.mp hw
    cases q with
    | nil => exact (hn rfl).elim
    | cons i t => exact put i (suffixNodes_closed hq ⟨[i],rfl⟩)
  funext w
  cases w with
  | nil => simp [indicator, criterion, noRoot, empty, epsilon]
  | cons a w =>
    by_cases ht : a::w ∈ T
    · simp [indicator, criterion, ht, child ht (List.cons_ne_nil a w), epsilon]
    · by_cases hj : a::w ∈ joinSets D T <;> simp [indicator, criterion, ht, hj, epsilon]

end ThreeWordCodes
