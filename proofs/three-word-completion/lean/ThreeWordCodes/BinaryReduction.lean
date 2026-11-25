module

public import ThreeWordCodes.Shortening
public import ThreeWordCodes.Powers
public import Mathlib.Tactic.FinCases

/-! # Reduction of the full theorem to a binary alphabet

Every shortening either decreases total length or merges two names. A merger
expresses the original triple on two generators. If the original triple was
injective, these generators cannot commute and hence have a positive completion.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A : Type*}

/-- Final letters and common divisors of additive counts persist during left
shortening, as does every property closed under removing a known prefix. -/
structure LeftReductionTrace (v : Fin 3 → Word A) (g : Bool → Word A) : Prop where
  finals : ∀ b, ∃ i, (g b).getLast? = (v i).getLast?
  divisors : ∀ (μ : Word A → ℕ), (∀ x y, μ (x++y)=μ x+μ y) →
    ∀ m, (∀ i, m ∣ μ (v i)) → ∀ b, m ∣ μ (g b)
  inherited : ∀ (P : Word A → Prop), (∀ s t, P s → P (s++t) → P t) →
    (∀ i, P (v i)) → ∀ b, P (g b)

private def twoGenerators (v : Fin 3 → Word A) : Prop :=
  ∃ g : Bool → Word A, ∃ d : Fin 3 → Word Bool, (fun k => spell g (d k)) = v ∧ LeftReductionTrace v g

private theorem two_of_range {v : Fin 3 → Word A} (l r : Fin 3)
    (h : ∀ i, v i = v l ∨ v i = v r) : twoGenerators v := by
  classical
  refine ⟨pair (v l) (v r), fun i => if v i = v l then [false] else [true], ?_, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : v i = v l
    · simp [hi,pair]
    · simp only [hi, ↓reduceIte,spell_cons,spell_nil,List.append_nil,pair]
      exact ((h i).resolve_left hi).symm
  · intro b
    cases b
    · exact ⟨l,rfl⟩
    · exact ⟨r,rfl⟩
  · intro μ _ m all b
    cases b
    · exact all l
    · exact all r
  · intro P _ all b
    cases b
    · exact all l
    · exact all r

private theorem merger {v : Fin 3 → Word A} (h : ¬ Function.Injective v) : twoGenerators v := by
  classical
  by_cases u : v 0 = v 1
  · exact two_of_range (v:=v) 0 2 (fun i => by fin_cases i <;> simp_all)
  by_cases w : v 0 = v 2
  · exact two_of_range (v:=v) 0 1 (fun i => by fin_cases i <;> simp_all)
  by_cases z : v 1 = v 2
  · exact two_of_range (v:=v) 0 1 (fun i => by fin_cases i <;> simp_all)
  exfalso
  apply h
  intro i j e
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; grind)

private theorem terminal_or_pair [Fintype A] (v : Fin 3 → Word A) (hne : ∀ i, v i ≠ []) :
    Completable v ∨ twoGenerators v := by
  classical
  induction len : (∑ i, (v i).length) using Nat.strong_induction_on generalizing v with
  | ind n ih =>
    by_cases inj : Function.Injective v
    · by_cases hp : InformationTheory.IsPrefixFree (Set.range v)
      · exact Or.inl (completable_prefix inj hne hp)
      · change ¬ (∀ x ∈ Set.range v, ∀ y ∈ Set.range v, x <+: y → x = y) at hp
        push Not at hp
        obtain ⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,⟨r,eqn⟩,diff⟩ := hp
        have ij : i ≠ j := fun h => diff (congrArg v h)
        have nr : r ≠ [] := by rintro rfl; exact diff (by simpa using eqn)
        let w (k : Fin 3) := if k = j then r else v k
        let pre (k : Fin 3) : Word (Fin 3) := if k = j then [i] else []
        let outer (k : Fin 3) := pre k ++ [k]
        have restore : (fun k => spell w (outer k)) = v := by
          funext k
          by_cases hk : k = j
          · subst k
            simpa [outer,pre,w,ij] using eqn
          · simp [outer,pre,w,hk]
        have strict : r.length < (v j).length := by
          have lent := congrArg List.length eqn
          have hi := List.length_pos_iff.mpr (hne i)
          simp only [List.length_append] at lent
          omega
        have sum : (∑ k, (w k).length) < n := by
          rw [← len]
          apply Finset.sum_lt_sum
          · intro k _
            by_cases hk : k = j <;> simp [w,hk,strict.le]
          · exact ⟨j,Finset.mem_univ _,by simpa [w] using strict⟩
        have newNonempty (k : Fin 3) : w k ≠ [] := by
          by_cases hk : k = j <;> simp [w,hk,nr,hne]
        rcases ih _ sum w newNonempty rfl with complete | ⟨g,d,eqd,trace⟩
        · exact Or.inl (restore ▸ complete.substitute (last_marked_completion pre))
        · right
          refine ⟨g,fun k => spell d (outer k),?_,?_,?_,?_⟩
          · funext k
            rw [← spell_substitution,eqd]
            exact congrFun restore k
          · intro b
            obtain ⟨k,he⟩ := trace.finals b
            refine ⟨k,he.trans ?_⟩
            by_cases hk : k=j
            · subst k
              rw [←eqn]
              simp only [w,ite_true,List.getLast?_append,List.getLast?_eq_some_getLast nr,Option.some_or]
            · simp [w,hk]
          · intro μ add m all b
            apply trace.divisors μ add m _ b
            intro k
            by_cases hk : k=j
            · subst k
              have dvd := all j
              rw [←eqn,add] at dvd
              exact (show w j = r by simp [w]) ▸ (Nat.dvd_add_right (all i)).mp dvd
            · simpa [w,hk] using all k
          · intro P cut old b
            apply trace.inherited P cut _ b
            intro k
            by_cases hk : k=j
            · subst k
              simpa [w] using cut (v i) r (old i) (eqn ▸ old j)
            · simpa [w,hk] using old k
    · exact Or.inr (merger inj)

theorem powers_of_generators {g : Bool → Word A} {r : Word A} {n m : ℕ}
    (hx : g false = wordPow r n) (hy : g true = wordPow r m) (s : Word Bool) :
    ∃ k, spell g s = wordPow r k := by
  induction s with
  | nil => exact ⟨0,rfl⟩
  | cons b s ih =>
    obtain ⟨k,he⟩ := ih
    cases b
    · exact ⟨n+k,by simp [wordPow_add,hx,he]⟩
    · exact ⟨m+k,by simp [wordPow_add,hy,he]⟩

/-- The entries of the triple do not all lie in one cyclic submonoid. -/
def Nonperiodic (v : Fin 3 → Word A) : Prop :=
  ¬ ∃ r : Word A, ∀ i, ∃ k : ℕ, v i = wordPow r k

/-- The initial binary realization in Section 2. It preserves every equation
on the original names. Establishing a realization with a letter entry is the
additional normalization problem in Lemma 4. -/
theorem traced_binary_realization [Fintype A] (v : Fin 3 → Word A) (hne : ∀ i, v i ≠ [])
    (amb : ¬ NamedCode v) (nonperiodic : Nonperiodic v) :
    ∃ g : Bool → Word A, ∃ d : Fin 3 → Word Bool,
      (fun k => spell g (d k)) = v ∧ NamedCode g ∧ SameEquations v d ∧ LeftReductionTrace v g := by
  rcases terminal_or_pair v hne with complete | ⟨g,d,e,trace⟩
  · exact (amb complete.1).elim
  have nc : g false ++ g true ≠ g true ++ g false := by
    intro comm
    obtain ⟨r,k,l,x,y⟩ := (commuting_iff_common_power _ _).mp comm
    apply nonperiodic
    exact ⟨r,fun i => (congrFun e i) ▸ powers_of_generators x y (d i)⟩
  have ident : pair (g false) (g true) = g := by funext b; cases b <;> rfl
  have code : NamedCode g := ident ▸ (noncommuting_pair_completion _ _ nc).1
  have eqn := code.preserves_equations d
  rw [e] at eqn
  exact ⟨g,d,e,code,fun s t => (eqn s t).symm,trace⟩

theorem binary_realization [Fintype A] (v : Fin 3 → Word A) (hne : ∀ i, v i ≠ [])
    (amb : ¬ NamedCode v) (nonperiodic : Nonperiodic v) :
    ∃ d : Fin 3 → Word Bool, SameEquations v d := by
  obtain ⟨_,d,_,_,h,_⟩ := traced_binary_realization v hne amb nonperiodic
  exact ⟨d,h⟩

/-- A binary theorem for arbitrary binary triples is enough, even when the
original finite alphabet has higher universe level. -/
def BinaryThreeWordTheorem : Prop :=
  ∀ X : Finset (Word Bool), X.card = 3 → InformationTheory.IsUniquelyDecodable (X : Set (Word Bool)) →
    HasPositiveCompletion (X : Set (Word Bool))

/-- A counterexample decodes on a completable pair to a binary counterexample.
The trace records invariants of the actual sequence of left shortenings. -/
theorem reduction_of_noncompletion [Fintype A] {v : Fin 3 → Word A}
    (hc : NamedCode v) (no : ¬ Completable v) :
    ∃ g : Bool → Word A, ∃ d : Fin 3 → Word Bool, (fun k => spell g (d k)) = v ∧
      Completable g ∧ NamedCode d ∧ ¬ Completable d ∧ LeftReductionTrace v g := by
  obtain ⟨g,d,eqd,trace⟩ := (terminal_or_pair v hc.entry_ne_nil).resolve_left no
  have noncomm : g false ++ g true ≠ g true ++ g false := by
    intro commute
    obtain ⟨r,n,m,hx,hy⟩ := (commuting_iff_common_power _ _).mp commute
    obtain ⟨i,e₀⟩ := powers_of_generators hx hy (d 0)
    obtain ⟨j,e₁⟩ := powers_of_generators hx hy (d 1)
    have e : spell v [0,1] = spell v [1,0] := by
      simp only [spell_cons,spell_nil,List.append_nil, ←congrFun eqd 0, ←congrFun eqd 1,e₀,e₁]
      exact wordPow_comm r i j
    exact (by decide : ([0,1] : Word (Fin 3)) ≠ [1,0]) (hc e)
  have ident : pair (g false) (g true) = g := by funext b; cases b <;> rfl
  have base : Completable g := ident ▸ noncommuting_pair_completion _ _ noncomm
  have outerCode : NamedCode d := by
    intro x y eqn
    apply hc
    rw [←eqd]
    simp only [spell_substitution,eqn]
  exact ⟨g,d,eqd,base,outerCode,fun h => no (eqd ▸ base.substitute h),trace⟩

private theorem complete_names_from_binary [Fintype A] (binary : BinaryThreeWordTheorem)
    {v : Fin 3 → Word A} (hc : NamedCode v) : Completable v := by
  classical
  by_contra no
  obtain ⟨_,d,_,_,outerCode,bad,_⟩ := reduction_of_noncompletion hc no
  let Y := Finset.univ.image d
  have rangeY : (Y : Set (Word Bool)) = Set.range d := by simp [Y]
  have cardY : Y.card = 3 := by simp [Y,Finset.card_image_of_injective _ outerCode.entries_injective]
  exact bad ⟨outerCode,rangeY ▸ binary Y cardY (rangeY ▸ ((namedCode_iff_range _).mp outerCode).2)⟩

/-- Enumerate an actual three-element code without losing its range. -/
theorem enumerate_three (X : Finset (Word A)) (card : X.card = 3)
    (hc : InformationTheory.IsUniquelyDecodable (X : Set (Word A))) :
    ∃ v : Fin 3 → Word A, Set.range v = (X : Set (Word A)) ∧ NamedCode v := by
  classical
  let idx : Fin 3 ≃ ↥X := Fintype.equivOfCardEq (by simpa using card.symm)
  let v (i : Fin 3) := (idx i).val
  have hr : Set.range v = (X : Set (Word A)) := by
    ext w
    constructor
    · rintro ⟨i,rfl⟩
      exact (idx i).property
    · intro hw
      exact ⟨idx.symm ⟨w,hw⟩, by simp [v]⟩
  have named : NamedCode v := (namedCode_iff_range _).mpr
    ⟨Subtype.val_injective.comp idx.injective, hr ▸ hc⟩
  exact ⟨v,hr,named⟩

theorem binary_suffices.{u} (binary : BinaryThreeWordTheorem) : ThreeWordTheorem.{u} := by
  intro A _ X card hc
  obtain ⟨v,hr,named⟩ := enumerate_three X card hc
  exact hr ▸ (complete_names_from_binary binary named).2

theorem threeWordTheorem_iff_binary : ThreeWordTheorem.{0} ↔ BinaryThreeWordTheorem :=
  ⟨fun h => h Bool,binary_suffices⟩

end ThreeWordCodes
