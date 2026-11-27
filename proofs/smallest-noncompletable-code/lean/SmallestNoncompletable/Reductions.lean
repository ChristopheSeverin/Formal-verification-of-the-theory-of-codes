module

public import ThreeWordCodes.MainTheorem
public import ThreeWordCodes.Shortening
public import ThreeWordCodes.Parsing
public import SmallestNoncompletable.Statement

/-! # Reductions of the completion problem

* Codes with at most three words: the three-word theorem and the noncommuting pair theorem.
* Shortening by a finite prefix tree (Lemma 6 in tree form): if every word of a code is read
  by the leaves of a finite tree, and some word uses a leaf of length at least two, the code
  over the leaf alphabet has a smaller total length, and its completions transport back.
* Merging an isolated letter codeword with another letter codeword. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

variable {A : Type*}

/-! ## At most three words -/

theorem singleton_prefixFree (w : Word A) : IsPrefixFree ({w} : Set (Word A)) := by
  intro x hx y hy _
  rw [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]

theorem empty_prefixFree : IsPrefixFree (∅ : Set (Word A)) := by
  intro x hx
  exact absurd hx (Set.notMem_empty x)

/-- **At most three words.** -/
theorem small_code_completion [Fintype A] (Y : Finset (Word A)) (hcard : Y.card ≤ 3)
    (hY : IsUniquelyDecodable (Y : Set (Word A))) : HasPositiveCompletion (Y : Set (Word A)) := by
  classical
  obtain h | h | h | h : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 2 ∨ Y.card = 3 := by omega
  · obtain rfl := Finset.card_eq_zero.mp h
    exact prefix_case ∅ hY (by simpa using empty_prefixFree)
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h
    exact prefix_case {w} hY (by simpa using singleton_prefixFree w)
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h
    have hc : u ++ v ≠ v ++ u := by
      intro e
      have := hY [u, v] [v, u] (by simp) (by simp) (by simpa using e)
      simp at this
      exact huv this.1
    have := (noncommuting_pair_completion u v hc).2
    refine this.mono ?_
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    exacts [⟨false, rfl⟩, ⟨true, rfl⟩]
  · exact three_word_positive_completion Y h hY

/-! ## Reading through a finite tree -/

theorem spell_flatten {N : Type*} (v : N → Word A) :
    ∀ xs : List (List N), spell v xs.flatten = (xs.map (spell v)).flatten
  | [] => rfl
  | x :: xs => by simp [spell_append, spell_flatten v xs]

/-- Greedy reading of a word from a node of the tree of internal nodes `I`: a letter either
leads to an internal node, or closes a leaf and returns to the root. The reading succeeds when
it ends at the root. -/
def readTree [DecidableEq A] (I : Finset (Word A)) : Word A → Word A → Bool
  | node, [] => node.isEmpty
  | node, x :: w => if node ++ [x] ∈ I then readTree I (node ++ [x]) w else readTree I [] w

theorem readTree_spec [Fintype A] [DecidableEq A] {I : Finset (Word A)} (hI : RootedPrefixClosed I) :
    ∀ (w node : Word A), node ∈ I → readTree I node w = true →
      ∃ s : List (Word A), (∀ e ∈ s, e ∈ leaves I) ∧ node ++ w = s.flatten ∧
        (node ≠ [] → ∃ e ∈ s, 2 ≤ e.length)
  | [], node, _, h => by
    have : node = [] := by simpa [readTree] using h
    subst this
    exact ⟨[], by simp, by simp, fun h => absurd rfl h⟩
  | x :: w, node, hn, h => by
    by_cases hx : node ++ [x] ∈ I
    · rw [readTree, ite_eq_left hx] at h
      obtain ⟨s, hs, e, hl⟩ := readTree_spec hI w (node ++ [x]) hx h
      refine ⟨s, hs, by simpa using e, fun _ => hl (by simp)⟩
    · rw [readTree, ite_eq_right hx] at h
      obtain ⟨s, hs, e, -⟩ := readTree_spec hI w [] hI.root h
      refine ⟨(node ++ [x]) :: s, ?_, by simp [← e], ?_⟩
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact mem_leaves.mpr ⟨⟨node, hn, x, rfl⟩, hx⟩
        · exact hs f hf
      · intro hne
        refine ⟨node ++ [x], List.mem_cons_self .., ?_⟩
        have := List.length_pos_iff.mpr hne
        simp only [List.length_append, List.length_singleton]
        omega

/-- A reading from the root that enters an internal letter produces a leaf of length two. -/
theorem readTree_long [Fintype A] [DecidableEq A] {I : Finset (Word A)} (hI : RootedPrefixClosed I) :
    ∀ (w node : Word A), node ∈ I → readTree I node w = true → (∃ x ∈ w, [x] ∈ I) →
      ∃ s : List (Word A), (∀ e ∈ s, e ∈ leaves I) ∧ node ++ w = s.flatten ∧ ∃ e ∈ s, 2 ≤ e.length
  | [], _, _, _, ⟨x, hx, _⟩ => absurd hx (List.not_mem_nil)
  | x :: w, node, hn, h, ⟨y, hy, hyI⟩ => by
    by_cases hnode : node = []
    · subst hnode
      rcases List.mem_cons.mp hy with rfl | hy
      · have hx : [] ++ [y] ∈ I := by simpa using hyI
        rw [readTree, ite_eq_left hx] at h
        obtain ⟨s, hs, e, hl⟩ := readTree_spec hI w ([] ++ [y]) hx h
        exact ⟨s, hs, by simpa using e, hl (by simp)⟩
      · by_cases hx : [] ++ [x] ∈ I
        · rw [readTree, ite_eq_left hx] at h
          obtain ⟨s, hs, e, hl⟩ := readTree_spec hI w ([] ++ [x]) hx h
          exact ⟨s, hs, by simpa using e, hl (by simp)⟩
        · rw [readTree, ite_eq_right hx] at h
          obtain ⟨s, hs, e, hl⟩ := readTree_long hI w [] hI.root h ⟨y, hy, hyI⟩
          refine ⟨[x] :: s, ?_, by simp [← e], ?_⟩
          · intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact mem_leaves.mpr ⟨⟨[], hI.root, x, rfl⟩, by simpa using hx⟩
            · exact hs f hf
          · obtain ⟨f, hf, hl⟩ := hl
            exact ⟨f, List.mem_cons_of_mem _ hf, hl⟩
    · obtain ⟨s, hs, e, hl⟩ := readTree_spec hI (x :: w) node hn h
      exact ⟨s, hs, e, hl hnode⟩

/-- The leaves of a rooted prefix-closed tree form a code with a positive completion. -/
theorem leaves_completion [Fintype A] [DecidableEq A] {I : Finset (Word A)}
    (hI : RootedPrefixClosed I) : HasPositiveCompletion ((leaves I : Finset (Word A)) : Set (Word A)) := by
  have hne : ([] : Word A) ∉ leaves I := fun h => (mem_leaves.mp h).2 hI.root
  exact prefix_case _ ((leaves_prefixFree hI).isUniquelyDecodable hne) (leaves_prefixFree hI)

theorem leaves_namedCode [Fintype A] [DecidableEq A] {I : Finset (Word A)}
    (hI : RootedPrefixClosed I) : NamedCode (fun e : ↥(leaves I) => e.val) := by
  have hne : ([] : Word A) ∉ leaves I := fun h => (mem_leaves.mp h).2 hI.root
  refine (namedCode_iff_range _).mpr ⟨Subtype.val_injective, ?_⟩
  have : Set.range (fun e : ↥(leaves I) => e.val) = (leaves I : Set (Word A)) := by
    ext w; simp
  rw [this]
  exact (leaves_prefixFree hI).isUniquelyDecodable hne

theorem leaf_ne_nil [Fintype A] [DecidableEq A] {I : Finset (Word A)} (hI : RootedPrefixClosed I)
    (e : ↥(leaves I)) : e.val ≠ [] := fun h => (mem_leaves.mp (h ▸ e.property)).2 hI.root

/-- Lists of words in the leaves are lists of leaves. -/
theorem exists_names [Fintype A] [DecidableEq A] {I : Finset (Word A)} :
    ∀ s : List (Word A), (∀ e ∈ s, e ∈ leaves I) →
      ∃ t : List ↥(leaves I), t.map Subtype.val = s
  | [], _ => ⟨[], rfl⟩
  | e :: s, h => by
    obtain ⟨t, ht⟩ := exists_names s fun f hf => h f (List.mem_cons_of_mem _ hf)
    exact ⟨⟨e, h e List.mem_cons_self⟩ :: t, by simp [ht]⟩

/-- **Lemma 6, tree form.** Let `I` be a finite rooted prefix-closed set of internal nodes such
that every word of the code `W` is read from the root back to the root, and some word of `W`
contains a letter which is an internal node. Then `W` is the image of a code over the leaves
with a smaller total length, and a completion of that code gives a completion of `W`. -/
theorem tree_reduction [Fintype A] [DecidableEq A] {I : Finset (Word A)} (hI : RootedPrefixClosed I)
    {W : Finset (Word A)} (hW : IsUniquelyDecodable (W : Set (Word A)))
    (hread : ∀ w ∈ W, readTree I [] w = true) (hlong : ∃ w ∈ W, ∃ x ∈ w, [x] ∈ I)
    (ih : ∀ Z : Finset (Word ↥(leaves I)), IsUniquelyDecodable (Z : Set (Word ↥(leaves I))) →
      totalLength Z < totalLength W → HasPositiveCompletion (Z : Set (Word ↥(leaves I)))) :
    HasPositiveCompletion (W : Set (Word A)) := by
  classical
  set v : ↥(leaves I) → Word A := fun e => e.val with hv
  have hnamed : NamedCode v := leaves_namedCode hI
  -- every word has a reading by leaves
  have hparse : ∀ w ∈ W, ∃ t : List ↥(leaves I), spell v t = w := by
    intro w hw
    obtain ⟨s, hs, e, -⟩ := readTree_spec hI w [] hI.root (hread w hw)
    obtain ⟨t, rfl⟩ := exists_names s hs
    refine ⟨t, ?_⟩
    simp only [spell, List.flatMap_def, hv] at e ⊢
    simpa using e.symm
  choose! parse hparse' using hparse
  set Z : Finset (Word ↥(leaves I)) := W.image parse with hZ
  have hinj : Set.InjOn parse (W : Set (Word A)) := by
    intro u hu w hw e
    rw [← hparse' u hu, ← hparse' w hw, e]
  have himage : spell v '' (Z : Set (Word ↥(leaves I))) = (W : Set (Word A)) := by
    ext w
    simp only [hZ, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [hparse' u hu]
      exact hu
    · intro hw
      exact ⟨parse w, ⟨w, hw, rfl⟩, hparse' w hw⟩
  -- the code over the leaves
  have hZcode : IsUniquelyDecodable (Z : Set (Word ↥(leaves I))) := by
    intro xs ys hxs hys e
    have hmap := hW (xs.map (spell v)) (ys.map (spell v))
      (by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
        have : spell v t ∈ spell v '' (Z : Set _) := ⟨t, hxs t ht, rfl⟩
        rw [himage] at this
        exact this)
      (by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
        have : spell v t ∈ spell v '' (Z : Set _) := ⟨t, hys t ht, rfl⟩
        rw [himage] at this
        exact this)
      (by rw [← spell_flatten, ← spell_flatten, e])
    exact List.map_injective_iff.mpr hnamed hmap
  -- the total length decreases
  have hlen : ∀ t : List ↥(leaves I), t.length ≤ (spell v t).length := by
    intro t
    induction t with
    | nil => simp
    | cons e t ih =>
      have := List.length_pos_iff.mpr (leaf_ne_nil hI e)
      simp only [spell_cons, List.length_cons, List.length_append, hv] at ih ⊢
      omega
  have hlt : totalLength Z < totalLength W := by
    obtain ⟨w, hw, x, hx, hxI⟩ := hlong
    obtain ⟨s, hs, e, f, hf, hf2⟩ := readTree_long hI w [] hI.root (hread w hw) ⟨x, hx, hxI⟩
    have hstrict : (parse w).length < w.length := by
      obtain ⟨t, rfl⟩ := exists_names s hs
      have hw' : spell v t = w := by
        simp only [spell, List.flatMap_def, hv]
        simpa using e.symm
      have ht : parse w = t := hnamed ((hparse' w hw).trans hw'.symm)
      rw [ht, ← hw']
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem hg
      have h1 := hlen t₁
      have h2 := hlen t₂
      simp only [spell_append, spell_cons, List.length_append, List.length_cons, hv] at h1 h2 hf2 ⊢
      omega
    unfold totalLength
    rw [hZ, Finset.sum_image hinj]
    exact Finset.sum_lt_sum (fun u hu => by
      have := hlen (parse u)
      rwa [hparse' u hu] at this) ⟨w, hw, hstrict⟩
  have hne : Nonempty ↥(leaves I) := by
    obtain ⟨w, hw, x, hx, hxI⟩ := hlong
    obtain ⟨s, hs, -, f, hf, -⟩ := readTree_long hI w [] hI.root (hread w hw) ⟨x, hx, hxI⟩
    exact ⟨⟨f, hs f hf⟩⟩
  have := completion_substitution hnamed.entries_injective
    (by
      have h := leaves_completion hI
      refine h.mono ?_
      rintro _ ⟨e, rfl⟩
      exact e.property)
    (ih Z hZcode hlt)
  rwa [himage] at this

/-! ## Merging an isolated letter codeword -/

/-- If `x` is a letter codeword which occurs in no other codeword, and `y` is another letter
codeword, merging `x` into `y` removes `x` from the code. -/
theorem merge_isolated [Fintype A] [DecidableEq A] {W : Finset (Word A)} {x y : A} (hxy : x ≠ y)
    (hy : [y] ∈ W) (hiso : ∀ w ∈ W, w ≠ [x] → x ∉ w)
    (h : HasPositiveCompletion ((W.erase [x] : Finset (Word A)) : Set (Word A))) :
    HasPositiveCompletion (W : Set (Word A)) := by
  classical
  obtain ⟨M, L, R, sub, -, pos⟩ := h
  let π : A → A := fun a => if a = x then y else a
  have hc := (pos.liftLetters π).model.completion
  refine hc.mono ?_
  intro w hw
  refine ⟨⟨w, (mem_lifts _ _ _).mpr ?_⟩, rfl⟩
  by_cases hwx : w = [x]
  · subst hwx
    have : ([y] : Word A) ∈ W.erase [x] := Finset.mem_erase.mpr ⟨by simpa using hxy.symm, hy⟩
    simpa [π] using sub this
  · have hmap : w.map π = w := by
      calc w.map π = w.map id := List.map_congr_left fun a ha => by
            have : a ≠ x := fun e => hiso w hw hwx (e ▸ ha)
            simp [π, this]
        _ = w := List.map_id w
    rw [hmap]
    exact sub (Finset.mem_erase.mpr ⟨hwx, hw⟩)

/-! ## The reductions together -/

/-- One of the reductions applies to `W`: it is prefix-free or suffix-free, it has an isolated
letter codeword next to another letter codeword, or a finite tree shortens it or its reversal.
The letters of the tree occur in `W`. -/
def Reducible [DecidableEq A] (W : Finset (Word A)) : Prop :=
  IsPrefixFree (W : Set (Word A)) ∨ IsSuffixFree (W : Set (Word A)) ∨
    (∃ x y : A, x ≠ y ∧ [x] ∈ W ∧ [y] ∈ W ∧ ∀ w ∈ W, w ≠ [x] → x ∉ w) ∨
    (∃ I : Finset (Word A), RootedPrefixClosed I ∧ (∀ p ∈ I, ∀ x ∈ p, ∃ w ∈ W, x ∈ w) ∧
      (∀ w ∈ W, readTree I [] w = true) ∧ ∃ w ∈ W, ∃ x ∈ w, [x] ∈ I) ∨
    (∃ I : Finset (Word A), RootedPrefixClosed I ∧ (∀ p ∈ I, ∀ x ∈ p, ∃ w ∈ W, x ∈ w) ∧
      (∀ w ∈ W, readTree I [] w.reverse = true) ∧ ∃ w ∈ W, ∃ x ∈ w, [x] ∈ I)

theorem isUniquelyDecodable_reverse {S : Set (Word A)} (h : IsUniquelyDecodable S) :
    IsUniquelyDecodable (List.reverse '' S) := by
  intro xs ys hxs hys e
  have key : ∀ zs : List (Word A), (∀ z ∈ zs, z ∈ List.reverse '' S) →
      (zs.map List.reverse).reverse.flatten = zs.flatten.reverse ∧
        ∀ z ∈ (zs.map List.reverse).reverse, z ∈ S := by
    intro zs hzs
    refine ⟨by simp [List.reverse_flatten], ?_⟩
    intro z hz
    simp only [List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨x, hx, rfl⟩ := hzs y hy
    simpa using hx
  obtain ⟨ex, hx⟩ := key xs hxs
  obtain ⟨ey, hy⟩ := key ys hys
  have := h _ _ hx hy (by rw [ex, ey, e])
  have := congrArg (fun zs => (zs.reverse).map List.reverse) this
  simpa [List.map_reverse, Function.comp_def] using this

theorem totalLength_image_reverse [DecidableEq A] (W : Finset (Word A)) :
    totalLength (W.image List.reverse) = totalLength W := by
  unfold totalLength
  rw [Finset.sum_image (fun x _ y _ h => List.reverse_injective h)]
  simp

/-- **Completion from a reduction.** Each reduction leads to a code with a smaller total length
(over a finite alphabet in the same universe), or to a prefix or suffix code. -/
theorem completion_of_reducible {A : Type u} [Fintype A] [DecidableEq A] {W : Finset (Word A)}
    (hW : IsUniquelyDecodable (W : Set (Word A))) (hred : Reducible W)
    (ih : ∀ (B : Type u) [Fintype B] [DecidableEq B] (Z : Finset (Word B)),
      IsUniquelyDecodable (Z : Set (Word B)) → totalLength Z < totalLength W →
        HasPositiveCompletion (Z : Set (Word B))) :
    HasPositiveCompletion (W : Set (Word A)) := by
  classical
  rcases hred with h | h | ⟨x, y, hxy, hx, hy, hiso⟩ | ⟨I, hI, -, hread, hlong⟩ |
    ⟨I, hI, -, hread, hlong⟩
  · exact prefix_case W hW h
  · exact suffix_case W hW h
  · refine merge_isolated hxy hy hiso (ih A _ ?_ ?_)
    · exact fun xs ys hxs hys e => hW xs ys (fun z hz => Finset.mem_of_mem_erase (hxs z hz))
        (fun z hz => Finset.mem_of_mem_erase (hys z hz)) e
    · unfold totalLength
      rw [← Finset.add_sum_erase W _ hx]
      simp
  · exact tree_reduction hI hW hread hlong fun Z hZ hlt => ih _ Z hZ hlt
  · set Wr := W.image List.reverse with hWr
    have hcoe : (Wr : Set (Word A)) = List.reverse '' (W : Set (Word A)) := by simp [hWr]
    have hWr' : IsUniquelyDecodable (Wr : Set (Word A)) := by
      rw [hcoe]; exact isUniquelyDecodable_reverse hW
    have hc := tree_reduction hI hWr'
      (by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact hread v hv)
      (by
        obtain ⟨w, hw, x, hxw, hxI⟩ := hlong
        exact ⟨w.reverse, Finset.mem_image_of_mem _ hw, x, List.mem_reverse.mpr hxw, hxI⟩)
      (fun Z hZ hlt => ih _ Z hZ (by rwa [totalLength_image_reverse] at hlt))
    have := hc.reverse
    rw [hcoe, Set.image_image] at this
    simpa using this

/-! ## Letters that never end or never start a word -/

/-- Reading through the tree whose only internal letter is `x`: a word read from the root or
from `[x]` returns to the root unless it ends with an unread `x`. -/
theorem readTree_single [DecidableEq A] (x : A) :
    ∀ (w node : Word A), (node = [] ∨ node = [x]) → (w = [] → node = []) →
      (∀ y, w.getLast? = some y → y ≠ x) →
      readTree ({[], [x]} : Finset (Word A)) node w = true
  | [], node, _, h0, _ => by simp [readTree, h0 rfl]
  | y :: w, node, hn, _, hl => by
    have hmem : node ++ [y] ∈ ({[], [x]} : Finset (Word A)) ↔ node = [] ∧ y = x := by
      rcases hn with rfl | rfl <;> simp
    by_cases hy : node = [] ∧ y = x
    · obtain ⟨hn0, hyx⟩ := hy
      rw [readTree, ite_eq_left (hmem.mpr ⟨hn0, hyx⟩)]
      cases w with
      | nil => exact absurd hyx (hl y (by simp))
      | cons z w =>
        rw [readTree, ite_eq_right (by rw [hn0, hyx]; simp)]
        exact readTree_single x w [] (Or.inl rfl) (fun _ => rfl)
          (fun t ht => hl t (by cases w <;> simp_all))
    · rw [readTree, ite_eq_right (fun h => hy (hmem.mp h))]
      exact readTree_single x w [] (Or.inl rfl) (fun _ => rfl)
        (fun t ht => hl t (by cases w <;> simp_all))

/-- A letter which occurs in `W` and is the last letter of no word: Lemma 6 with the tree
`{ε, x}`. -/
theorem reducible_of_not_last [DecidableEq A] {W : Finset (Word A)} {x : A}
    (hx : ∃ w ∈ W, x ∈ w) (hl : ∀ w ∈ W, w.getLast? ≠ some x) : Reducible W := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨{[], [x]}, ⟨by simp, ?_⟩, ?_, ?_, ?_⟩)))
  · intro p w hw hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inl (List.eq_nil_of_prefix_nil hp)
    · rcases List.prefix_cons_iff.mp hp with h | ⟨t, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (by rw [List.eq_nil_of_prefix_nil h])
  · intro p hp y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp at hy
    · rw [List.mem_singleton.mp hy]; exact hx
  · intro w hw
    exact readTree_single x w [] (Or.inl rfl) (fun _ => rfl)
      (fun y hy e => hl w hw (e ▸ hy))
  · obtain ⟨w, hw, hxw⟩ := hx
    exact ⟨w, hw, x, hxw, by simp⟩

/-- A letter which occurs in `W` and is the first letter of no word: the same tree for the
reversed code. -/
theorem reducible_of_not_first [DecidableEq A] {W : Finset (Word A)} {x : A}
    (hx : ∃ w ∈ W, x ∈ w) (hf : ∀ w ∈ W, w.head? ≠ some x) : Reducible W := by
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨{[], [x]}, ⟨by simp, ?_⟩, ?_, ?_, ?_⟩)))
  · intro p w hw hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inl (List.eq_nil_of_prefix_nil hp)
    · rcases List.prefix_cons_iff.mp hp with h | ⟨t, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (by rw [List.eq_nil_of_prefix_nil h])
  · intro p hp y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp at hy
    · rw [List.mem_singleton.mp hy]; exact hx
  · intro w hw
    refine readTree_single x w.reverse [] (Or.inl rfl) (fun _ => rfl) ?_
    intro y hy e
    apply hf w hw
    rw [List.getLast?_reverse] at hy
    rw [← e, hy]
  · obtain ⟨w, hw, hxw⟩ := hx
    exact ⟨w, hw, x, hxw, by simp⟩

end SmallestNoncompletable
