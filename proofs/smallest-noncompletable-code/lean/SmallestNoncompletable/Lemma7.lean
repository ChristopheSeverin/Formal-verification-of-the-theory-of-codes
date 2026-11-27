module

public import SmallestNoncompletable.Profiles
public import SmallestNoncompletable.Canonical

/-! # Lemma 7

Every code with total length at most ten, at least four words and a word of length at least
four is reducible: it is prefix-free or suffix-free, it has an isolated letter codeword next to
another one, or Lemma 6 applies to it or to its reversal.

The code is brought to its canonical form, which the search of the fourteen profiles covers,
except for one long word and for words of even lengths, which are treated directly. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory Search

variable {A : Type*} [DecidableEq A]

omit [DecidableEq A] in
theorem cut_flatten (ι : A → ℕ) : ∀ L : List (Word A),
    cut (L.map List.length) (L.flatten.map ι) = L.map (List.map ι)
  | [] => rfl
  | w :: L => by
    simp only [List.map_cons, List.flatten_cons, List.map_append, cut]
    rw [List.take_left' (by simp), List.drop_left' (by simp), cut_flatten ι L]

/-- The canonical form of a code with letter codewords `Sfin` and long words `longs`. -/
theorem canonical {W : Finset (Word A)} (Sfin : Finset A) (hS : ∀ x, [x] ∈ W ↔ x ∈ Sfin)
    (longs : List (Word A)) (hlongs : ∀ w, w ∈ W ↔ (∃ x ∈ Sfin, w = [x]) ∨ w ∈ longs)
    (hnd : longs.Nodup) (hlong : ∀ w ∈ longs, 2 ≤ w.length) :
    ∃ ι : A → ℕ, Set.InjOn ι (Letters W) ∧
      W.image (List.map ι) = (wordsOf ⟨Sfin.card, longs.map List.length⟩
        (longs.flatten.map ι)).toFinset ∧
      (wordsOf ⟨Sfin.card, longs.map List.length⟩ (longs.flatten.map ι)).Nodup ∧
      Ext Sfin.card 0 Sfin.card (longs.flatten.map ι) := by
  classical
  set s := Sfin.card
  set p := longs.flatten
  set restS := (Sfin \ p.toFinset).toList
  obtain ⟨ι, -, hinj, hb1, hb2, hext⟩ := rename_exists (fun x => x ∈ Sfin) s Sfin (fun x h => h) rfl
    (p ++ restS) ∅ (fun _ => 0) 0 s (by simp) (by simp) (by simp) (by simp) le_rfl
  have hletters : ∀ x ∈ Letters W, x ∈ (∅ ∪ (p ++ restS).toFinset : Finset A) := by
    rintro x ⟨w, hw, hxw⟩
    simp only [Finset.empty_union, List.mem_toFinset, List.mem_append]
    rcases (hlongs w).mp hw with ⟨y, hy, rfl⟩ | hw'
    · rw [List.mem_singleton.mp hxw]
      by_cases hyp : y ∈ p
      · exact Or.inl hyp
      · right
        simp [restS, hy, hyp]
    · exact Or.inl (List.mem_flatten.mpr ⟨w, hw', hxw⟩)
  have hinjL : Set.InjOn ι (Letters W) := fun x hx y hy e =>
    hinj (Finset.mem_coe.mpr (hletters x hx)) (Finset.mem_coe.mpr (hletters y hy)) e
  have hSin : ∀ x ∈ Sfin, x ∈ (∅ ∪ (p ++ restS).toFinset : Finset A) := by
    intro x hx
    simp only [Finset.empty_union, List.mem_toFinset, List.mem_append]
    by_cases hxp : x ∈ p
    · exact Or.inl hxp
    · right; simp [restS, hx, hxp]
  -- the letter codewords are renamed onto `[0, s)`
  have hSimg : Sfin.image ι = Finset.range s := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (hb1 x (hSin x hx) hx)
    · rw [Finset.card_range, Finset.card_image_of_injOn (fun x hx y hy e =>
        hinj (Finset.mem_coe.mpr (hSin x hx)) (Finset.mem_coe.mpr (hSin y hy)) e)]
  have hlongL : ∀ w ∈ longs, ∀ x ∈ w, x ∈ Letters W :=
    fun w hw x hx => ⟨w, (hlongs w).mpr (Or.inr hw), hx⟩
  have hcut : cut (longs.map List.length) (p.map ι) = longs.map (List.map ι) := cut_flatten ι longs
  refine ⟨ι, hinjL, ?_, ?_, Ext.of_append (by simpa [List.map_append] using hext)⟩
  · ext v
    simp only [Finset.mem_image, List.mem_toFinset, wordsOf, hcut, List.mem_append, singlesW,
      List.mem_map, List.mem_range]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases (hlongs w).mp hw with ⟨x, hx, rfl⟩ | hw'
      · left
        have : ι x ∈ Finset.range s := hSimg ▸ Finset.mem_image_of_mem ι hx
        exact ⟨ι x, Finset.mem_range.mp this, rfl⟩
      · exact Or.inr ⟨w, hw', rfl⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨w, hw, rfl⟩)
      · have : n ∈ Sfin.image ι := hSimg ▸ Finset.mem_range.mpr hn
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp this
        exact ⟨[x], (hS x).mpr hx, rfl⟩
      · exact ⟨w, (hlongs w).mpr (Or.inr hw), rfl⟩
  · simp only [wordsOf, hcut]
    rw [List.nodup_append]
    refine ⟨(List.nodup_range).map (fun a b h => by simpa using h), ?_, ?_⟩
    · refine hnd.map_on fun u hu v hv e => map_inj hinjL (hlongL u hu) (hlongL v hv) e
    · intro a ha b hb e
      simp only [singlesW, List.mem_map, List.mem_range] at ha hb
      obtain ⟨n, -, rfl⟩ := ha
      obtain ⟨w, hw, rfl⟩ := hb
      have := hlong w hw
      have := congrArg List.length e
      simp at this
      omega

/-- **Lemma 7.** -/
theorem lemma7 (W : Finset (Word A)) (hW : IsUniquelyDecodable (W : Set (Word A)))
    (hτ : totalLength W ≤ 10) (hcard : 4 ≤ W.card) (hmax : 4 ≤ maxLength W) : Reducible W := by
  classical
  have hne : ([] : Word A) ∉ W := fun h => hW.epsilon_notMem h
  set singF := W.filter fun w => w.length = 1
  set longsF := W.filter fun w => 2 ≤ w.length
  have hsplit : ∀ w ∈ W, w.length = 1 ∨ 2 ≤ w.length := by
    intro w hw
    have : w ≠ [] := fun h => hne (h ▸ hw)
    have := List.length_pos_iff.mpr this
    omega
  -- a word of length at least four
  obtain ⟨w₄, hw₄, hw₄l⟩ : ∃ w ∈ W, 4 ≤ w.length := by
    by_contra h
    push Not at h
    have : maxLength W ≤ 3 := Finset.sup_le fun w hw => by have := h w hw; omega
    omega
  -- one long word
  by_cases ht1 : longsF.card = 1
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ht1
    have hwF : w ∈ longsF := hw ▸ Finset.mem_singleton_self w
    simp only [longsF, Finset.mem_filter] at hwF
    obtain ⟨hwW, hwl⟩ := hwF
    refine reducible_of_one_long hW hwW hwl fun v hv hvw => ?_
    rcases hsplit v hv with h | h
    · exact h
    · exfalso
      have : v ∈ longsF := Finset.mem_filter.mpr ⟨hv, h⟩
      rw [hw] at this
      exact hvw (Finset.mem_singleton.mp this)
  -- no letter codeword and all lengths even
  by_cases heven : singF = ∅ ∧ ∀ w ∈ W, Even w.length
  · exact reducible_of_even ⟨w₄, hw₄, fun h => by simp [h] at hw₄l⟩ heven.2
  -- the canonical form
  set Sfin : Finset A := W.biUnion fun w => if w.length = 1 then w.toFinset else ∅ with hSfin
  have hS : ∀ x, [x] ∈ W ↔ x ∈ Sfin := by
    intro x
    simp only [hSfin, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨[x], h, by simp⟩
    · rintro ⟨w, hw, hx⟩
      split_ifs at hx with hl
      · obtain ⟨y, rfl⟩ : ∃ y, w = [y] := by
          rcases w with _ | ⟨y, _ | ⟨z, w⟩⟩ <;> simp at hl
          exact ⟨y, rfl⟩
        simp at hx
        rwa [hx]
      · simp at hx
  set longs := longsF.toList.mergeSort fun u v => decide (u.length ≤ v.length) with hlongsdef
  have hperm : longs.Perm longsF.toList := List.mergeSort_perm _ _
  have hlongs : ∀ w, w ∈ W ↔ (∃ x ∈ Sfin, w = [x]) ∨ w ∈ longs := by
    intro w
    rw [hperm.mem_iff, Finset.mem_toList]
    constructor
    · intro hw
      rcases hsplit w hw with h | h
      · left
        obtain ⟨y, rfl⟩ : ∃ y, w = [y] := by
          rcases w with _ | ⟨y, _ | ⟨z, w⟩⟩ <;> simp at h
          exact ⟨y, rfl⟩
        exact ⟨y, (hS y).mp hw, rfl⟩
      · exact Or.inr (Finset.mem_filter.mpr ⟨hw, h⟩)
    · rintro (⟨x, hx, rfl⟩ | h)
      · exact (hS x).mpr hx
      · exact (Finset.mem_filter.mp h).1
  have hnd : longs.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hlong : ∀ w ∈ longs, 2 ≤ w.length := fun w hw =>
    (Finset.mem_filter.mp (Finset.mem_toList.mp (hperm.mem_iff.mp hw))).2
  obtain ⟨ι, hinj, himg, hndW, hext⟩ := canonical Sfin hS longs hlongs hnd hlong
  set lens := longs.map List.length
  set P : Prof := ⟨Sfin.card, lens⟩
  -- counting
  have hsingF : singF = Sfin.image fun x => [x] := by
    ext w
    simp only [singF, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hw, hl⟩
      obtain ⟨y, rfl⟩ : ∃ y, w = [y] := by
        rcases w with _ | ⟨y, _ | ⟨z, w⟩⟩ <;> simp at hl
        exact ⟨y, rfl⟩
      exact ⟨y, (hS y).mp hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hS x).mpr hx, rfl⟩
  have hscard : singF.card = Sfin.card := by
    rw [hsingF, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hWsplit : W = singF ∪ longsF := by
    ext w
    simp only [singF, longsF, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hw; rcases hsplit w hw with h | h
      exacts [Or.inl ⟨hw, h⟩, Or.inr ⟨hw, h⟩]
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  have hdisj : Disjoint singF longsF := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hlenlongs : longs.length = longsF.card := by rw [hperm.length_eq, Finset.length_toList]
  have hcardW : W.card = Sfin.card + lens.length := by
    rw [hWsplit, Finset.card_union_of_disjoint hdisj, hscard, List.length_map, hlenlongs]
  have hsumlongs : lens.sum = ∑ w ∈ longsF, w.length := by
    rw [show lens = longs.map List.length from rfl, (hperm.map List.length).sum_eq,
      Finset.sum_map_toList]
  have htot : totalLength W = Sfin.card + lens.sum := by
    unfold totalLength
    rw [hWsplit, Finset.sum_union hdisj, hsumlongs, ← hscard, Finset.card_eq_sum_ones]
    congr 1
    exact Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2
  have hw₄L : w₄ ∈ longs := by
    rcases (hlongs w₄).mp hw₄ with ⟨x, -, rfl⟩ | h
    · simp at hw₄l
    · exact h
  have ht2 : 2 ≤ lens.length := by
    have h1 : lens.length ≠ 1 := by
      rw [List.length_map, hlenlongs]; exact ht1
    have h0 : lens.length ≠ 0 := by
      rw [List.length_map]; exact List.length_pos_of_mem hw₄L |>.ne'
    omega
  have hlens2 : ∀ l ∈ lens, 2 ≤ l := by
    intro l hl
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
    exact hlong w hw
  have hvalid : P.Valid := by
    refine ⟨hlens2, ?_⟩
    have := List.length_nsmul_le_sum lens 2 hlens2
    simp only [smul_eq_mul] at this
    simp only [Prof.t, P]
    omega
  have hmem : (Sfin.card, lens) ∈ profiles := by
    apply profile_mem
    · have hsorted := List.pairwise_mergeSort (le := fun u v : Word A => decide (u.length ≤ v.length))
        (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) longsF.toList
      rw [← hlongsdef] at hsorted
      exact List.pairwise_map.mpr (hsorted.imp fun h => by simpa using h)
    · exact hlens2
    · omega
    · exact ht2
    · omega
    · exact ⟨w₄.length, List.mem_map_of_mem hw₄L, hw₄l⟩
    · by_contra h
      push Not at h
      apply heven
      refine ⟨Finset.card_eq_zero.mp (hscard ▸ h.1), fun w hw => ?_⟩
      rcases (hlongs w).mp hw with ⟨x, hx, -⟩ | hwL
      · exact absurd (Finset.card_pos.mpr ⟨x, hx⟩) (by omega)
      · rw [Nat.even_iff]
        have := h.2 w.length (List.mem_map_of_mem hwL)
        omega
  obtain ⟨certs, hrun⟩ := profiles_run _ hmem
  have hgood := run_sound hvalid hrun (longs.flatten.map ι) hext
    (by simp [P, Prof.m, lens, List.length_flatten, Function.comp_def])
  rcases hgood with h | h | h
  · exact absurd hndW h
  · exact absurd (himg ▸ uniquelyDecodable_image hinj hW) h
  · exact reducible_of_image hinj (himg ▸ h)

end SmallestNoncompletable
