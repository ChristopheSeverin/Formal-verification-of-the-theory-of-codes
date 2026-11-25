module

public import ThreeWordCodes.SuffixTree

/-! # Grafting a word onto a coded suffix tree (Lemma 5) -/

@[expose] public section
namespace ThreeWordCodes
open WordSeries
open scoped ThreeWordCodes.WordSeries
variable {A : Type*}

def Comparable (u v : Word A) : Prop := u <+: v ∨ v <+: u

private noncomputable def minimalPrefixes (H : Finset (Word A)) : Finset (Word A) := by
  classical exact H.filter fun w => ∀ v ∈ H, v <+: w → v = w

private theorem minimal_spec {H : Finset (Word A)} {w : Word A} :
    w ∈ minimalPrefixes H ↔ w ∈ H ∧ ∀ v ∈ H, v <+: w → v = w := by
  classical simp [minimalPrefixes]

private theorem below_minimal {H : Finset (Word A)} {w : Word A} (hw : w ∈ H) :
    ∃ v ∈ minimalPrefixes H, v <+: w := by
  classical
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases min : ∀ v ∈ H, v <+: w → v = w
    · exact ⟨w,minimal_spec.mpr ⟨hw,min⟩,List.prefix_refl _⟩
    · push Not at min
      obtain ⟨v,hv,cmp,ne⟩ := min
      have shorter : v.length < w.length := by
        have := cmp.length_le
        apply Nat.lt_of_le_of_ne this
        exact fun e => ne (cmp.eq_of_length e)
      obtain ⟨r,hr,pr⟩ := ih v.length (by omega) hv rfl
      exact ⟨r,hr,pr.trans cmp⟩

private theorem separating_tree [Fintype A] [DecidableEq A] (t : Word A) (ht : t ≠ [])
    (S : Finset (Word A)) :
    ∃ K : Finset (Word A), RootedPrefixClosed K ∧ t ∈ leaves K ∧
      ∀ w ∈ S, ¬ Comparable t w → ∃ r ∈ leaves K, r ∈ S ∧ r <+: w := by
  classical
  let H := S.filter (fun w => ¬ Comparable t w)
  let seed := insert t (minimalPrefixes H)
  have inc {w : Word A} (hw : w ∈ minimalPrefixes H) : w ∈ S ∧ ¬ Comparable t w :=
    Finset.mem_filter.mp (minimal_spec.mp hw).1
  have hp : InformationTheory.IsPrefixFree (seed : Set (Word A)) := by
    intro u hu v hv eqn
    rcases Finset.mem_insert.mp hu with rfl | hu <;> rcases Finset.mem_insert.mp hv with rfl | hv
    · rfl
    · exact ((inc hv).2 (Or.inl eqn)).elim
    · exact ((inc hu).2 (Or.inr eqn)).elim
    · exact (minimal_spec.mp hv).2 _ (minimal_spec.mp hu).1 eqn
  have nz : [] ∉ seed := by
    intro h
    rcases Finset.mem_insert.mp h with e | he
    · exact ht e.symm
    · exact (inc he).2 (Or.inr List.nil_prefix)
  have inside := subset_leaves hp nz
  refine ⟨internalNodes seed, internalNodes_closed _, inside (Finset.mem_insert_self ..), ?_⟩
  intro w hw hn
  obtain ⟨r,hr,pr⟩ := below_minimal (H := H) (Finset.mem_filter.mpr ⟨hw, hn⟩)
  exact ⟨r, inside (Finset.mem_insert_of_mem hr), (inc hr).1, pr⟩

private theorem base_identity {m d i j : Series A}
    (outer : m + j = epsilon + (d ⋆ j)) (inner : d + i = epsilon + (i ⋆ letters)) :
    m + (i ⋆ j) = epsilon + ((i ⋆ letters) ⋆ j) := by
  have mov := congrArg (fun z : Series A => z ⋆ j) inner
  simp only [add_conv, epsilon_conv] at mov
  funext w
  have e := congrFun mov w
  have e' := congrFun outer w
  simp only [Pi.add_apply] at *
  omega

private theorem graft_identity {m i j d k t : Series A}
    (base : m + (i ⋆ j) = epsilon + ((i ⋆ letters) ⋆ j))
    (tree : t + k = epsilon + (k ⋆ letters))
    (covered : ∀ w, (d ⋆ j) w ≤ m w + ((d ⋆ t) ⋆ j) w) :
    let f : Series A := fun w => m w + ((d ⋆ t) ⋆ j) w - (d ⋆ j) w
    f + ((i + (d ⋆ k)) ⋆ j) = epsilon + (((i + (d ⋆ k)) ⋆ letters) ⋆ j) := by
  have mov := congrArg (fun z : Series A => (d ⋆ z) ⋆ j) tree
  simp only [conv_add, conv_epsilon, add_conv, ← conv_assoc] at mov
  simp only [add_conv]
  funext w
  have e := congrFun mov w
  have e' := congrFun base w
  have bound := covered w
  simp only [Pi.add_apply] at *
  omega

/-- The complete prefix tree is specified by its internal nodes. The finite suffix
code E is on the names of its leaves. The result contains the new word and
every originally prescribed word outside the family removed by the graft. -/
theorem tree_extension_certificate [Fintype A] [Nonempty A] [DecidableEq A]
    (I : Finset (Word A)) (hI : RootedPrefixClosed I)
    (E : Finset (Word (↥(leaves I)))) (hne : [] ∉ E)
    (hsuf : ∀ x ∈ E, ∀ y ∈ E, x <:+ y → x = y)
    (s : Word (↥(leaves I))) (hs : s ∈ E) (t : Word A) (ht : t ≠ [])
    (avoid : t ∉ codedSet (fun b : ↥(leaves I) => b.val) (suffixNodes E))
    (cover : ∀ q ∈ suffixNodes E,
      Comparable t (spell (fun b : ↥(leaves I) => b.val) q) → s ++ q ∈ E) :
    let v := fun b : ↥(leaves I) => b.val
    HasFiniteCertificate ({spell v s ++ t} ∪
      (spell v '' {e | e ∈ E ∧ ¬ ∃ q ∈ suffixNodes E, s ++ q = e})) := by
  classical
  let D := leaves I
  let v := fun b : ↥D => b.val
  let J := suffixNodes E
  let S := codedSet v J
  let M := codedSet v (suffixLeaves J)
  let a := spell v s
  let U : Finset (Word A) := {a}
  have noEmpty (i : ↥D) : v i ≠ [] := by
    intro eqn
    have mem : [] ∈ leaves I := eqn ▸ i.property
    exact (mem_leaves.mp mem).2 hI.root
  have pref : InformationTheory.IsPrefixFree (Set.range v) := by simpa [v,D] using leaves_prefixFree hI
  have dec : NamedCode v := (namedCode_iff_range _).mpr ⟨Subtype.val_injective,
    pref.isUniquelyDecodable (by rintro ⟨i,hi⟩; exact noEmpty i hi)⟩
  have an : a ≠ [] := fun e => hne (dec (a₁ := s) (a₂ := []) e ▸ hs)
  have jr : [] ∈ S := mem_codedSet.mpr ⟨[],mem_suffixNodes.mpr (Or.inl rfl),rfl⟩
  have em (e) (he : e ∈ E) : spell v e ∈ M := mem_codedSet.mpr ⟨e,suffix_subset hne hsuf he,rfl⟩
  obtain ⟨K,hK,tk,separate⟩ := separating_tree t ht S
  let T := leaves K
  have idU : (indicator U ⋆ indicator S) = indicator (joinSets U S) := by
    apply indicator_product
    rintro ⟨⟨x,hx⟩,y⟩ ⟨⟨z,hz⟩,w⟩ he
    obtain rfl : x = a := Finset.mem_singleton.mp hx
    obtain rfl : z = a := Finset.mem_singleton.mp hz
    exact Prod.ext rfl (Subtype.ext (List.append_cancel_left he))
  have dead (w : Word A) : w ∈ joinSets U S ↔ ∃ q ∈ J, a ++ spell v q = w := by
    simp [U,S]
    rfl
  let grow := (indicator U ⋆ indicator T) ⋆ indicator S
  have addWord {r : Word A} (hr : r ∈ T) {q : Word A} (hq : q ∈ S) :
      0 < grow ((a ++ r) ++ q) :=
    conv_pos.mpr ⟨a++r,q,rfl,conv_pos.mpr ⟨a,r,rfl,(indicator_pos _ _).mpr (Finset.mem_singleton_self _),
      (indicator_pos _ _).mpr hr⟩,(indicator_pos _ _).mpr hq⟩
  have coveredByGrowth : ∀ w, (indicator U ⋆ indicator S) w ≤ indicator M w + grow w := by
    intro w
    rw [idU]
    by_cases hw : w ∈ joinSets U S
    · rw [indicator_of_mem hw]
      obtain ⟨q,hq,rfl⟩ := (dead _).mp hw
      by_cases cmp : Comparable t (spell v q)
      · have ok : a ++ spell v q ∈ M := by simpa [a] using em (s++q) (cover q hq cmp)
        rw [indicator_of_mem ok]
        omega
      · obtain ⟨r,hr,hrS,pr⟩ := separate _ (mem_codedSet.mpr ⟨q,hq,rfl⟩) cmp
        obtain ⟨z,hz,rfl⟩ := mem_codedSet.mp hrS
        obtain ⟨b,eqn⟩ := prefix_reflection Subtype.val_injective noEmpty pref pr
        have hb : b ∈ J := suffixNodes_closed hq ⟨z,eqn⟩
        have pos := addWord hr (mem_codedSet.mpr ⟨b,hb,rfl⟩)
        have same : (a ++ spell v z) ++ spell v b = a ++ spell v q := by rw [← eqn]; simp [List.append_assoc]
        rw [same] at pos
        omega
    · simp [indicator,hw]
  let P := indicator I + (indicator U ⋆ indicator K)
  let F : Series A := fun w => indicator M w + grow w - (indicator U ⋆ indicator S) w
  have su : indicator U [] = 0 := by simp [indicator,U,Ne.symm an]
  have fp : Set.Finite {w | 0 < P w} := by
    apply ((finite_indicator_support I).union (finite_conv_support (finite_indicator_support U)
      (finite_indicator_support K))).subset
    intro w h
    change 0 < indicator I w + (indicator U ⋆ indicator K) w at h
    change 0 < indicator I w ∨ 0 < (indicator U ⋆ indicator K) w
    omega
  have base := base_identity (coded_suffix_series v dec E D (by intro w; simp [v])) (tree_series hI)
  have eqn := graft_identity base (tree_series hK) coveredByGrowth
  refine ⟨P,indicator S,F,by simp [P,su,indicator_of_mem hI.root],
    indicator_of_mem jr,fp,finite_indicator_support S,eqn,?_⟩
  have live (w : Word A) (absent : w ∉ joinSets U S) (pos : 0 < indicator M w + grow w) : 0 < F w := by
    have zero : indicator (joinSets U S) w = 0 := ite_eq_right absent
    change 0 < indicator M w + grow w - (indicator U ⋆ indicator S) w
    simpa only [idU,zero,Nat.sub_zero] using pos
  rintro w (hw | hw)
  · obtain rfl : w = a ++ t := hw
    apply live
    · intro bad
      obtain ⟨q,hq,e⟩ := (dead _).mp bad
      exact avoid (mem_codedSet.mpr ⟨q,hq,List.append_cancel_left e⟩)
    · have := addWord tk jr
      simp only [List.append_nil] at this
      omega
  · obtain ⟨e,⟨he,keep⟩,rfl⟩ := hw
    apply live
    · intro bad
      obtain ⟨q,hq,eqn⟩ := (dead _).mp bad
      exact keep ⟨q,hq,dec (by simpa [a] using eqn : spell v (s ++ q) = spell v e)⟩
    · rw [indicator_of_mem (em _ he)]
      omega

/-- Apply the certified graft to the semantic completion problem. -/
theorem tree_extension [Fintype A] [Nonempty A] [DecidableEq A]
    (I : Finset (Word A)) (hI : RootedPrefixClosed I)
    (E : Finset (Word (↥(leaves I)))) (hne : [] ∉ E)
    (hsuf : ∀ x ∈ E, ∀ y ∈ E, x <:+ y → x = y)
    (s : Word (↥(leaves I))) (hs : s ∈ E) (t : Word A) (ht : t ≠ [])
    (avoid : t ∉ codedSet (fun b : ↥(leaves I) => b.val) (suffixNodes E))
    (cover : ∀ q ∈ suffixNodes E,
      Comparable t (spell (fun b : ↥(leaves I) => b.val) q) → s ++ q ∈ E) :
    let v := fun b : ↥(leaves I) => b.val
    HasPositiveCompletion ({spell v s ++ t} ∪
      (spell v '' {e | e ∈ E ∧ ¬ ∃ q ∈ suffixNodes E, s ++ q = e})) :=
  (tree_extension_certificate I hI E hne hsuf s hs t ht avoid cover).toPositive

end ThreeWordCodes
