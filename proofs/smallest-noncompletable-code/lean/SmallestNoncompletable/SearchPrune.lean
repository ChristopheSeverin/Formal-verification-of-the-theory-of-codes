module

public import SmallestNoncompletable.SearchCert

/-! # Soundness of the pruning

Positions of the first and last letters of the long words, the restricted growth extensions,
the invariant of the search, and the soundness of each pruning rule. -/

@[expose] public section

namespace SmallestNoncompletable.Search

open ThreeWordCodes InformationTheory

/-! ## Profiles and extensions -/

/-- A profile is valid when its long words have length at least two and the letters fit in
base `8`. -/
structure Prof.Valid (P : Prof) : Prop where
  long : ∀ l ∈ P.lens, 2 ≤ l
  small : P.s + P.t ≤ 8

/-- Two-counter restricted growth extensions from `u` used letter codewords and `k` letters. -/
def Ext (s : ℕ) : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | u, k, j :: q => (j < s ∧ j ≤ u ∧ Ext s (max u (j + 1)) k q) ∨
      (s ≤ j ∧ j ≤ k ∧ Ext s u (max k (j + 1)) q)

theorem Ext.letters {s : ℕ} : ∀ {u k : ℕ} {q : List ℕ}, Ext s u k q → s ≤ k →
    ∀ x ∈ q, (x < s ∧ x < u + q.length) ∨ (s ≤ x ∧ x < k + q.length)
  | _, _, [], _, _ => by simp
  | u, k, j :: q, h, hk => by
    intro x hx
    rcases h with ⟨hj, hju, h⟩ | ⟨hj, hjk, h⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · left; simp; omega
      · rcases h.letters hk x hx with h1 | h1
        · left; simp; omega
        · right; simp; omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · right; simp; omega
      · rcases h.letters (by omega) x hx with h1 | h1
        · left; simp; omega
        · right; simp; omega

/-- The invariant of the search state for a prefix `q₀`. -/
structure Inv (P : Prof) (q₀ : List ℕ) (u k S E : ℕ) : Prop where
  u_le : u ≤ P.s
  s_le : P.s ≤ k
  k_le : k ≤ P.s + P.t
  mem : ∀ x ∈ q₀, x < u ∨ (P.s ≤ x ∧ x < k)
  usedA : ∀ x, P.s ≤ x → x < k → x ∈ q₀
  S_eq : ∀ x, bit S x = 1 ↔ ∃ p ∈ startsL P.lens, q₀[p]? = some x
  E_eq : ∀ x, bit E x = 1 ↔ ∃ p ∈ endsL P.lens, q₀[p]? = some x

/-! ## Positions in a pattern -/

theorem startsL_lt : ∀ (lens : List ℕ), (∀ l ∈ lens, 1 ≤ l) → ∀ p ∈ startsL lens, p < lens.sum
  | [], _, _, h => by simp [startsL] at h
  | l :: ls, hl, p, h => by
    have h1 := hl l (by simp)
    simp only [startsL, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨a, ha, rfl⟩
    · simp; omega
    · have := startsL_lt ls (fun l' h => hl l' (List.mem_cons_of_mem _ h)) a ha
      simp; omega

theorem endsL_lt : ∀ (lens : List ℕ), (∀ l ∈ lens, 1 ≤ l) → ∀ p ∈ endsL lens, p < lens.sum
  | [], _, _, h => by simp [endsL] at h
  | l :: ls, hl, p, h => by
    have h1 := hl l (by simp)
    simp only [endsL, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨a, ha, rfl⟩
    · simp; omega
    · have := endsL_lt ls (fun l' h => hl l' (List.mem_cons_of_mem _ h)) a ha
      simp; omega

/-- The first letters of the long words are the letters at the start positions. -/
theorem heads_cut : ∀ (lens q : List ℕ), (∀ l ∈ lens, 1 ≤ l) → q.length = lens.sum → ∀ x : ℕ,
    (∃ w ∈ cut lens q, w.head? = some x) ↔ ∃ p ∈ startsL lens, q[p]? = some x
  | [], _, _, _, x => by simp [cut, startsL]
  | l :: ls, q, hl, hq, x => by
    have h1 := hl l (by simp)
    simp only [List.sum_cons] at hq
    have ih := heads_cut ls (q.drop l) (fun l' h => hl l' (List.mem_cons_of_mem _ h))
      (by simp; omega) x
    have hh : (q.take l).head? = q[0]? := by
      cases q with
      | nil => simp
      | cons a q => cases l with
        | zero => omega
        | succ l => simp
    constructor
    · rintro ⟨w, hw, hwx⟩
      simp only [cut, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨0, List.mem_cons_self .., by rw [← hh]; exact hwx⟩
      · obtain ⟨p, hp, hpx⟩ := ih.mp ⟨w, hw, hwx⟩
        refine ⟨p + l, List.mem_cons_of_mem _ (List.mem_map_of_mem (f := (· + l)) hp), ?_⟩
        rw [List.getElem?_drop] at hpx; rwa [Nat.add_comm]
    · rintro ⟨p, hp, hpx⟩
      simp only [startsL, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨a, ha, rfl⟩
      · exact ⟨q.take l, by simp [cut], by rw [hh]; exact hpx⟩
      · obtain ⟨w, hw, hwx⟩ := ih.mpr ⟨a, ha, by rw [List.getElem?_drop, Nat.add_comm]; exact hpx⟩
        exact ⟨w, by simp [cut, hw], hwx⟩

/-- The last letters of the long words are the letters at the end positions. -/
theorem lasts_cut : ∀ (lens q : List ℕ), (∀ l ∈ lens, 1 ≤ l) → q.length = lens.sum → ∀ x : ℕ,
    (∃ w ∈ cut lens q, w.getLast? = some x) ↔ ∃ p ∈ endsL lens, q[p]? = some x
  | [], _, _, _, x => by simp [cut, endsL]
  | l :: ls, q, hl, hq, x => by
    have h1 := hl l (by simp)
    simp only [List.sum_cons] at hq
    have ih := lasts_cut ls (q.drop l) (fun l' h => hl l' (List.mem_cons_of_mem _ h))
      (by simp; omega) x
    have hh : (q.take l).getLast? = q[l - 1]? := by
      rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
        List.getElem?_take]
      rw [ite_eq_left (by omega : l - 1 < l)]
    constructor
    · rintro ⟨w, hw, hwx⟩
      simp only [cut, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨l - 1, List.mem_cons_self .., by rw [← hh]; exact hwx⟩
      · obtain ⟨p, hp, hpx⟩ := ih.mp ⟨w, hw, hwx⟩
        refine ⟨p + l, List.mem_cons_of_mem _ (List.mem_map_of_mem (f := (· + l)) hp), ?_⟩
        rw [List.getElem?_drop] at hpx; rwa [Nat.add_comm]
    · rintro ⟨p, hp, hpx⟩
      simp only [endsL, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨a, ha, rfl⟩
      · exact ⟨q.take l, by simp [cut], by rw [hh]; exact hpx⟩
      · obtain ⟨w, hw, hwx⟩ := ih.mpr ⟨a, ha, by rw [List.getElem?_drop, Nat.add_comm]; exact hpx⟩
        exact ⟨w, by simp [cut, hw], hwx⟩

/-! ## The words of a full pattern -/

theorem mem_wordsOf {P : Prof} {q w : List ℕ} :
    w ∈ wordsOf P q ↔ (∃ x < P.s, w = [x]) ∨ w ∈ cut P.lens q := by
  simp only [wordsOf, singlesW, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨x, hx, rfl⟩ | h)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr h
  · rintro (⟨x, hx, rfl⟩ | h)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr h

theorem mem_of_mem_cut {lens q w : List ℕ} {x : ℕ} (hw : w ∈ cut lens q) (hx : x ∈ w) : x ∈ q := by
  induction lens generalizing q with
  | nil => simp [cut] at hw
  | cons l ls ih =>
    simp only [cut, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (ih hw)

theorem exists_mem_cut {lens q : List ℕ} (hq : q.length = lens.sum) {x : ℕ} (hx : x ∈ q) :
    ∃ w ∈ cut lens q, x ∈ w := by
  rw [← flatten_cut lens q hq] at hx
  simpa [List.mem_flatten] using hx

theorem long_of_mem_cut {lens q w : List ℕ} (hl : ∀ l ∈ lens, 2 ≤ l) (hq : q.length = lens.sum)
    (hw : w ∈ cut lens q) : 2 ≤ w.length := by
  have := cut_lengths lens q hq
  have hm : w.length ∈ (cut lens q).map List.length := List.mem_map_of_mem hw
  rw [this] at hm
  exact hl _ hm

/-- Facts about the words of a full pattern. -/
theorem wordsOf_facts {P : Prof} (hP : P.Valid) {q : List ℕ} (hq : q.length = P.m)
    (hsm : Small q) (hs : P.s ≤ 8) :
    (∀ w ∈ wordsOf P q, Small w) ∧ [] ∉ wordsOf P q := by
  constructor
  · intro w hw
    rcases mem_wordsOf.mp hw with ⟨x, hx, rfl⟩ | hw
    · intro y hy; rw [List.mem_singleton.mp hy]; omega
    · exact small_of_mem_cut hsm hw
  · intro h
    rcases mem_wordsOf.mp h with ⟨x, -, h⟩ | h
    · simp at h
    · have := long_of_mem_cut hP.long hq h
      simp at this

/-! ## Pruning: the endpoint letters -/

/-- If a letter `x ≥ s` occurring in `q` is not a first letter of a long word, Lemma 6 with
`{ε, x}` applies to the reversed code. -/
theorem good_of_not_first {P : Prof} (hP : P.Valid) {q : List ℕ} (hq : q.length = P.m)
    {x : ℕ} (hxs : P.s ≤ x) (hxq : x ∈ q) (hx : ¬ ∃ p ∈ startsL P.lens, q[p]? = some x) :
    Good (wordsOf P q) := by
  refine Or.inr (Or.inr (reducible_of_not_first (x := x) ?_ ?_))
  · obtain ⟨w, hw, hxw⟩ := exists_mem_cut hq hxq
    exact ⟨w, List.mem_toFinset.mpr (List.mem_append_right _ hw), hxw⟩
  · intro w hw hh
    rcases mem_wordsOf.mp (List.mem_toFinset.mp hw) with ⟨y, hy, rfl⟩ | hw
    · simp at hh; omega
    · exact hx ((heads_cut P.lens q (fun l h => by have := hP.long l h; omega) hq x).mp
        ⟨w, hw, hh⟩)

theorem good_of_not_last {P : Prof} (hP : P.Valid) {q : List ℕ} (hq : q.length = P.m)
    {x : ℕ} (hxs : P.s ≤ x) (hxq : x ∈ q) (hx : ¬ ∃ p ∈ endsL P.lens, q[p]? = some x) :
    Good (wordsOf P q) := by
  refine Or.inr (Or.inr (reducible_of_not_last (x := x) ?_ ?_))
  · obtain ⟨w, hw, hxw⟩ := exists_mem_cut hq hxq
    exact ⟨w, List.mem_toFinset.mpr (List.mem_append_right _ hw), hxw⟩
  · intro w hw hh
    rcases mem_wordsOf.mp (List.mem_toFinset.mp hw) with ⟨y, hy, rfl⟩ | hw
    · simp at hh; omega
    · exact hx ((lasts_cut P.lens q (fun l h => by have := hP.long l h; omega) hq x).mp
        ⟨w, hw, hh⟩)

/-- Pigeonhole: if more letters of `[s, s + n)` are missing from the mask than positions remain,
one of them is missed by every completion. -/
theorem exists_missed {pos : List ℕ} {i s n : ℕ} {S : ℕ} {q₀ q : List ℕ}
    (hq₀ : q₀ <+: q) (hlen : q₀.length = i)
    (hS : ∀ x, bit S x = 1 ↔ ∃ p ∈ pos, q₀[p]? = some x)
    (h : pos.countP (i ≤ ·) < missing S s n) :
    ∃ x, s ≤ x ∧ x < s + n ∧ ¬ ∃ p ∈ pos, q[p]? = some x := by
  -- the letters at the remaining positions
  set F : List ℕ := (pos.filter (i ≤ ·)).filterMap fun p => q[p]? with hF
  have hFlen : F.length ≤ pos.countP (i ≤ ·) := by
    rw [hF, List.countP_eq_length_filter]
    exact List.length_filterMap_le _ _
  set M : List ℕ := ((List.range n).filter fun x => bit S (s + x) ≠ 1).map (s + ·) with hM
  have hMlen : M.length = missing S s n := by
    rw [hM, List.length_map, missing_eq, List.countP_eq_length_filter]
  have hMnd : M.Nodup := ((List.nodup_range).filter _).map (fun a b h => by simpa using h)
  obtain ⟨x, hxM, hxF⟩ : ∃ x ∈ M, x ∉ F := by
    by_contra hc
    push Not at hc
    have := hMnd.length_le_of_subset hc
    omega
  simp only [hM, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hxM
  obtain ⟨a, ⟨ha, hbit⟩, rfl⟩ := hxM
  refine ⟨s + a, by omega, by omega, ?_⟩
  rintro ⟨p, hp, hpx⟩
  by_cases hpi : i ≤ p
  · apply hxF
    simp only [hF, List.mem_filterMap, List.mem_filter, decide_eq_true_eq]
    exact ⟨p, ⟨hp, hpi⟩, hpx⟩
  · apply hbit
    rw [hS]
    refine ⟨p, hp, ?_⟩
    obtain ⟨t, rfl⟩ := hq₀
    rw [List.getElem?_append_left (by omega)] at hpx
    exact hpx

/-! ## Pruning: the letter codewords -/

/-- If a letter codeword never occurs in a long word and another letter codeword exists, the
merge reduction applies. -/
theorem good_of_isolated {P : Prof} {q : List ℕ} (hs : 2 ≤ P.s) (hx : P.s - 1 ∉ q) : Good (wordsOf P q) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨P.s - 1, 0, by omega, ?_, ?_, ?_⟩))))
  · exact List.mem_toFinset.mpr (mem_wordsOf.mpr (Or.inl ⟨P.s - 1, by omega, rfl⟩))
  · exact List.mem_toFinset.mpr (mem_wordsOf.mpr (Or.inl ⟨0, by omega, rfl⟩))
  · intro w hw hne hxw
    rcases mem_wordsOf.mp (List.mem_toFinset.mp hw) with ⟨y, hy, rfl⟩ | hw
    · rw [List.mem_singleton.mp hxw] at hne; exact hne rfl
    · exact hx (mem_of_mem_cut hw hxw)

/-! ## Pruning: as many other letters as long words -/

theorem good_of_many {P : Prof} (hP : P.Valid) {q : List ℕ} (hq : q.length = P.m)
    {k : ℕ} (hk : P.t ≤ k - P.s) (hocc : ∀ x, P.s ≤ x → x < k → x ∈ q) :
    Good (wordsOf P q) := by
  classical
  have hl1 : ∀ l ∈ P.lens, 1 ≤ l := fun l h => by have := hP.long l h; omega
  by_cases hall : ∀ x, P.s ≤ x → x < k → ∃ p ∈ startsL P.lens, q[p]? = some x
  · -- the long words start with distinct letters `≥ s`: the code is prefix-free
    refine Or.inr (Or.inr (Or.inl ?_))
    set L := cut P.lens q with hL
    have hlen : L.length = P.t := cut_length _ _
    have hne : ∀ w ∈ L, w ≠ [] := fun w hw h => by
      have := long_of_mem_cut hP.long hq hw; simp [h] at this
    set H := L.map fun w => w.headD 0 with hH
    have hcover : ∀ x, P.s ≤ x → x < k → x ∈ H := by
      intro x h1 h2
      obtain ⟨w, hw, hwx⟩ := (heads_cut P.lens q hl1 hq x).mpr (hall x h1 h2)
      simp only [hH, List.mem_map]
      refine ⟨w, hw, ?_⟩
      rw [List.headD_eq_head?_getD, hwx]; rfl
    have hsub : (Finset.Ico P.s k) ⊆ H.toFinset := by
      intro x hx
      simp only [Finset.mem_Ico] at hx
      exact List.mem_toFinset.mpr (hcover x hx.1 hx.2)
    have hcard := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hcard
    have hHlen : H.length = P.t := by simp [hH, hlen]
    have hcard2 : H.toFinset.card ≤ H.length := List.toFinset_card_le H
    have hnodup : H.Nodup := by
      have h1 : H.toFinset.card = H.length := by omega
      rw [List.card_toFinset] at h1
      exact List.dedup_eq_self.mp ((List.dedup_sublist H).eq_of_length h1)
    have heq : H.toFinset = Finset.Ico P.s k :=
      (Finset.eq_of_subset_of_card_le hsub (by simp; omega)).symm
    have hheads : ∀ w ∈ L, P.s ≤ w.headD 0 := by
      intro w hw
      have : w.headD 0 ∈ H.toFinset := List.mem_toFinset.mpr (List.mem_map_of_mem hw)
      rw [heq, Finset.mem_Ico] at this
      exact this.1
    have hinj := List.inj_on_of_nodup_map hnodup
    intro u hu v hv huv
    simp only [Finset.mem_coe, List.mem_toFinset] at hu hv
    rcases mem_wordsOf.mp hu with ⟨x, hx, rfl⟩ | hu <;>
      rcases mem_wordsOf.mp hv with ⟨y, hy, rfl⟩ | hv
    · exact huv.eq_of_length rfl
    · exfalso
      obtain ⟨t, rfl⟩ := huv
      have := hheads _ hv
      simp at this
      omega
    · exfalso
      have := huv.length_le
      have := long_of_mem_cut hP.long hq hu
      simp at *
      omega
    · apply hinj hu hv
      obtain ⟨t, rfl⟩ := huv
      rcases u with _ | ⟨a, u⟩
      · exact absurd rfl (hne _ hu)
      · rfl
  · push Not at hall
    obtain ⟨x, h1, h2, hx⟩ := hall
    exact good_of_not_first hP hq h1 (hocc x h1 h2) (fun ⟨p, hp, hpx⟩ => hx p hp hpx)

end SmallestNoncompletable.Search
