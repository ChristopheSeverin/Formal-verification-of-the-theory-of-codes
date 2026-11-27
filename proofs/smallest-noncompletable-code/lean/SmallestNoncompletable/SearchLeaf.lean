module

public import SmallestNoncompletable.SearchLemmas
public import SmallestNoncompletable.Reductions

/-! # Soundness of the leaf tests

The words of a pattern, the goal `Good` at a leaf, and the meaning of the quick tests. -/

@[expose] public section

namespace SmallestNoncompletable.Search

open ThreeWordCodes InformationTheory

/-! ## Words of a pattern -/

/-- The letter codewords `[0], …, [s-1]`. -/
def singlesW (s : ℕ) : List (List ℕ) := (List.range s).map fun x => [x]

/-- The words of a pattern with long part `q`. -/
def wordsOf (P : Prof) (q : List ℕ) : List (List ℕ) := singlesW P.s ++ cut P.lens q

/-- The goal at a leaf: two words coincide, or the words do not form a code, or a reduction
applies. -/
def Good (ws : List (List ℕ)) : Prop :=
  ¬ ws.Nodup ∨ ¬ IsUniquelyDecodable (ws.toFinset : Set (List ℕ)) ∨ Reducible ws.toFinset

/-- Codes and lengths of a list of words. -/
def pairs (ws : List (List ℕ)) : List (ℕ × ℕ) := ws.map fun w => (code w, w.length)

@[simp] theorem length_pairs (ws : List (List ℕ)) : (pairs ws).length = ws.length := by
  simp [pairs]

theorem cut_length : ∀ (lens q : List ℕ), (cut lens q).length = lens.length
  | [], _ => rfl
  | _ :: ls, q => by simp [cut, cut_length ls]

theorem cut_lengths : ∀ (lens q : List ℕ), q.length = lens.sum →
    (cut lens q).map List.length = lens
  | [], _, _ => rfl
  | l :: ls, q, h => by
    simp only [List.sum_cons] at h
    simp only [cut, List.map_cons, List.length_take, cut_lengths ls (q.drop l) (by simp; omega)]
    congr 1
    omega

theorem flatten_cut : ∀ (lens q : List ℕ), q.length = lens.sum → (cut lens q).flatten = q
  | [], q, h => by simp at h; simp [cut, h]
  | l :: ls, q, h => by
    simp only [List.sum_cons] at h
    simp [cut, flatten_cut ls (q.drop l) (by simp; omega)]

theorem cut_append : ∀ (n : ℕ) (lens q₁ q₂ : List ℕ), q₁.length = (lens.take n).sum →
    cut lens (q₁ ++ q₂) = cut (lens.take n) q₁ ++ cut (lens.drop n) q₂
  | 0, lens, q₁, q₂, h => by
    simp at h; simp [h, cut]
  | _ + 1, [], _, _, _ => by simp [cut]
  | n + 1, l :: ls, q₁, q₂, h => by
    simp only [List.take_succ_cons, List.sum_cons] at h
    simp only [List.take_succ_cons, List.drop_succ_cons, cut, List.cons_append]
    have h1 : (q₁ ++ q₂).take l = q₁.take l := by
      rw [List.take_append_of_le_length (by omega)]
    have h2 : (q₁ ++ q₂).drop l = q₁.drop l ++ q₂ := by
      rw [List.drop_append_of_le_length (by omega)]
    rw [h1, h2, cut_append n ls (q₁.drop l) q₂ (by simp; omega)]

theorem small_of_mem_cut {lens q w : List ℕ} (hq : Small q) (hw : w ∈ cut lens q) : Small w := by
  induction lens generalizing q with
  | nil => simp [cut] at hw
  | cons l ls ih =>
    simp only [cut, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hq.of_sublist (List.take_sublist _ _)
    · exact ih (hq.of_sublist (List.drop_sublist _ _)) hw

/-- The codes of the long words. -/
theorem wordCodes_eq : ∀ (lens pre q : List ℕ), Small (pre ++ q) → q.length = lens.sum →
    wordCodes (code (pre ++ q)) lens q.length = (cut lens q).map code
  | [], _, _, _, _ => rfl
  | l :: ls, pre, q, hs, h => by
    simp only [List.sum_cons] at h
    obtain ⟨a, b, rfl, ha⟩ : ∃ a b, q = a ++ b ∧ a.length = l :=
      ⟨q.take l, q.drop l, (List.take_append_drop _ _).symm, by simp; omega⟩
    have hsa : Small a := hs.of_sublist ((List.sublist_append_left _ _).trans
      (List.sublist_append_right _ _))
    have hsb : Small b := hs.of_sublist ((List.sublist_append_right _ _).trans
      (List.sublist_append_right _ _))
    have hb : b.length = ls.sum := by simp at h; omega
    have hcut : cut (l :: ls) (a ++ b) = a :: cut ls b := by
      show (a ++ b).take l :: cut ls ((a ++ b).drop l) = a :: cut ls b
      rw [List.take_left' ha, List.drop_left' ha]
    rw [hcut]
    simp only [wordCodes, List.map_cons, p8_eq, List.length_append]
    rw [show a.length + b.length - l = b.length by omega, ← List.append_assoc]
    congr 1
    · rw [code_append_div hsb, ← ha, code_append_mod hsa]
    · exact wordCodes_eq ls (pre ++ a) b (by rwa [List.append_assoc]) hb

theorem wordCodes_eq' (lens q : List ℕ) (hs : Small q) (h : q.length = lens.sum) :
    (wordCodes (code q) lens lens.sum).zip lens = pairs (cut lens q) := by
  have e := wordCodes_eq lens [] q (by simpa using hs) h
  simp only [List.nil_append] at e
  rw [← h, e, pairs]
  have hl := cut_lengths lens q h
  calc ((cut lens q).map code).zip lens
      = ((cut lens q).map code).zip ((cut lens q).map List.length) := by rw [hl]
    _ = _ := List.zip_map'

theorem pairs_singles (s : ℕ) : (List.range s).map (fun x => (x, 1)) = pairs (singlesW s) := by
  simp [pairs, singlesW, code, Function.comp_def]

/-! ## Quick tests -/

theorem pair_inj {v w : List ℕ} (hv : Small v) (hw : Small w)
    (h : (code v, v.length) = (code w, w.length)) : v = w := by
  simp only [Prod.mk.injEq] at h
  exact code_injective hv hw h.2 h.1

theorem dupB_sound : ∀ (L : List (List ℕ)), (∀ w ∈ L, Small w) → dupB (pairs L) = true → ¬ L.Nodup
  | [], _, h => by simp [pairs, dupB] at h
  | w :: L, hs, h => by
    simp only [pairs, List.map_cons, dupB, Bool.or_eq_true, List.any_eq_true, List.mem_map,
      Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.nodup_cons]
    rintro ⟨hw, hL⟩
    rcases h with ⟨_, ⟨v, hv, rfl⟩, h1, h2⟩ | h
    · exact hw (pair_inj (hs v (List.mem_cons_of_mem _ hv)) (hs w List.mem_cons_self)
        (by simp [h1, h2]) ▸ hv)
    · exact dupB_sound L (fun v hv => hs v (List.mem_cons_of_mem _ hv)) h hL

/-- Words of a full pattern are nonempty and small. -/
structure WordsOK (ws : List (List ℕ)) : Prop where
  small : ∀ w ∈ ws, Small w
  ne : ∀ w ∈ ws, w ≠ []

theorem prefixFreeB_sound {s : ℕ} {longs : List (List ℕ)} (hl : WordsOK longs)
    (hlong : ∀ w ∈ longs, 2 ≤ w.length) (h : prefixFreeB s (pairs longs) = true) :
    IsPrefixFree ((singlesW s ++ longs).toFinset : Set (List ℕ)) := by
  simp only [prefixFreeB, pairs, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Nat.ble_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨hhead, hpre⟩ := h
  intro u hu v hv huv
  simp only [List.coe_toFinset, List.mem_append, singlesW, List.mem_map,
    List.mem_range] at hu hv
  rcases hu with ⟨x, hx, rfl⟩ | hu <;> rcases hv with ⟨y, hy, rfl⟩ | hv
  · exact huv.eq_of_length rfl
  · -- a letter codeword is a prefix of a long word: its first letter
    exfalso
    obtain ⟨t, rfl⟩ := huv
    have hs := hl.small _ hv
    have := hhead _ hv
    simp only [List.singleton_append, List.length_cons, Nat.add_sub_cancel, p8_eq] at this hs
    rw [code_head (hs.of_sublist (List.sublist_cons_self _ _))] at this
    omega
  · exfalso
    have := huv.length_le
    have := hlong u hu
    simp at *; omega
  · by_contra hne
    have hle := huv.length_le
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have := hpre u hu v hv
      have hc := (prefix_iff_code (hl.small u hu) (hl.small v hv) hle).mp huv
      have hb : Nat.blt u.length v.length = true := by simp [Nat.blt_eq, hlt]
      simp [properPrefix, hb, p8_eq, hc] at this
    · exact hne (huv.eq_of_length heq)

theorem suffixFreeB_sound {s : ℕ} {longs : List (List ℕ)} (hl : WordsOK longs)
    (hlong : ∀ w ∈ longs, 2 ≤ w.length) (h : suffixFreeB s (pairs longs) = true) :
    IsSuffixFree ((singlesW s ++ longs).toFinset : Set (List ℕ)) := by
  simp only [suffixFreeB, pairs, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Nat.ble_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨hlast, hsuf⟩ := h
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
  rw [List.reverse_prefix] at huv
  congr 1
  simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_append, singlesW,
    List.mem_map, List.mem_range] at hu hv
  rcases hu with ⟨x, hx, rfl⟩ | hu <;> rcases hv with ⟨y, hy, rfl⟩ | hv
  · exact huv.eq_of_length rfl
  · exfalso
    obtain ⟨t, rfl⟩ := huv
    have hs := hl.small _ hv
    have := hlast _ hv
    rw [code_last (hs x (by simp))] at this
    omega
  · exfalso
    have := huv.length_le
    have := hlong u hu
    simp at *; omega
  · by_contra hne
    have hle := huv.length_le
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have := hsuf u hu v hv
      have hc := (suffix_iff_code (hl.small u hu) (hl.small v hv) hle).mp huv
      have hb : Nat.blt u.length v.length = true := by simp [Nat.blt_eq, hlt]
      simp [properSuffix, hb, p8_eq, hc] at this
    · exact hne (huv.eq_of_length heq)

end SmallestNoncompletable.Search
