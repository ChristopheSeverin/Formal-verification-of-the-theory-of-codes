module

public import SmallestNoncompletable.Search.P00
public import SmallestNoncompletable.Search.P01
public import SmallestNoncompletable.Search.P02
public import SmallestNoncompletable.Search.P03
public import SmallestNoncompletable.Search.P04
public import SmallestNoncompletable.Search.P05
public import SmallestNoncompletable.Search.P06
public import SmallestNoncompletable.Search.P07
public import SmallestNoncompletable.Search.P08
public import SmallestNoncompletable.Search.P09
public import SmallestNoncompletable.Search.P10
public import SmallestNoncompletable.Search.P11
public import SmallestNoncompletable.Search.P12
public import SmallestNoncompletable.Search.P13
public import SmallestNoncompletable.SearchSound

/-! # The fourteen profiles of the search

Each profile is checked in its own module. A profile of a code with at most total length ten,
at least four words, a word of length at least four, at least two long words, and not all of
even length, is one of them. -/

@[expose] public section

namespace SmallestNoncompletable.Search

/-- The profiles of the search: the number of letter codewords and the sorted lengths of the
long words. -/
def profiles : List (ℕ × List ℕ) := [(2, [2, 4]), (2, [2, 5]), (2, [2, 6]), (2, [3, 4]), (2, [3, 5]), (2, [4, 4]), (3, [2, 4]), (3, [2, 5]), (3, [3, 4]), (4, [2, 4]), (1, [2, 2, 4]), (1, [2, 2, 5]), (1, [2, 3, 4]), (2, [2, 2, 4])]

theorem profiles_run : ∀ x ∈ profiles, ∃ certs, run ⟨x.1, x.2⟩ certs = true := by
  intro x hx
  simp only [profiles, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨certs00, run00⟩
  · exact ⟨certs01, run01⟩
  · exact ⟨certs02, run02⟩
  · exact ⟨certs03, run03⟩
  · exact ⟨certs04, run04⟩
  · exact ⟨certs05, run05⟩
  · exact ⟨certs06, run06⟩
  · exact ⟨certs07, run07⟩
  · exact ⟨certs08, run08⟩
  · exact ⟨certs09, run09⟩
  · exact ⟨certs10, run10⟩
  · exact ⟨certs11, run11⟩
  · exact ⟨certs12, run12⟩
  · exact ⟨certs13, run13⟩

theorem profile_two : ∀ s ∈ List.range 7, ∀ a ∈ List.range 5, ∀ b ∈ List.range 7,
    a ≤ b → 2 ≤ a → s + (a + b) ≤ 10 → 2 ≤ s → (4 ≤ a ∨ 4 ≤ b) → (s, [a, b]) ∈ profiles := by
  decide

theorem profile_three : ∀ s ∈ List.range 5, ∀ a ∈ List.range 4, ∀ b ∈ List.range 4,
    ∀ c ∈ List.range 6, a ≤ b → b ≤ c → 2 ≤ a → s + (a + (b + c)) ≤ 10 → 1 ≤ s →
    (4 ≤ a ∨ 4 ≤ b ∨ 4 ≤ c) → (s, [a, b, c]) ∈ profiles := by
  decide

/-- **The profile of a candidate is one of the fourteen.** -/
theorem profile_mem (s : ℕ) (lens : List ℕ) (hsorted : lens.Pairwise (· ≤ ·))
    (h2 : ∀ l ∈ lens, 2 ≤ l) (hsum : s + lens.sum ≤ 10) (ht : 2 ≤ lens.length)
    (hcard : 4 ≤ s + lens.length) (h4 : ∃ l ∈ lens, 4 ≤ l)
    (hodd : s ≠ 0 ∨ ∃ l ∈ lens, l % 2 = 1) : (s, lens) ∈ profiles := by
  match lens, hsorted, h2, hsum, ht, hcard, h4, hodd with
  | [a, b], hsorted, h2, hsum, _, hcard, h4, _ =>
    have hab : a ≤ b := List.rel_of_pairwise_cons hsorted (by simp)
    have ha := h2 a (by simp)
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil] at hsum hcard
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at h4
    exact profile_two s (List.mem_range.mpr (by omega)) a (List.mem_range.mpr (by omega)) b
      (List.mem_range.mpr (by omega)) hab ha (by omega) (by omega) h4
  | [a, b, c], hsorted, h2, hsum, _, hcard, h4, _ =>
    have hab : a ≤ b := List.rel_of_pairwise_cons hsorted (by simp)
    have hbc : b ≤ c := List.rel_of_pairwise_cons (List.Pairwise.of_cons hsorted) (by simp)
    have ha := h2 a (by simp)
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil] at hsum hcard
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at h4
    exact profile_three s (List.mem_range.mpr (by omega)) a (List.mem_range.mpr (by omega)) b
      (List.mem_range.mpr (by omega)) c (List.mem_range.mpr (by omega)) hab hbc ha (by omega)
      (by omega) h4
  | [a, b, c, d], _, h2, hsum, _, _, h4, hodd =>
    exfalso
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    have hc := h2 c (by simp)
    have hd := h2 d (by simp)
    simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at h4 hodd
    omega
  | a :: b :: c :: d :: e :: rest, _, h2, hsum, _, _, h4, _ =>
    exfalso
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    have hc := h2 c (by simp)
    have hd := h2 d (by simp)
    have he := h2 e (by simp)
    obtain ⟨l, hl, hl4⟩ := h4
    simp only [List.sum_cons] at hsum
    simp only [List.mem_cons] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | hl
    · omega
    · omega
    · omega
    · omega
    · omega
    · have := List.le_sum_of_mem hl
      omega
  | [], _, _, _, ht, _, _, _ => simp at ht
  | [_], _, _, _, ht, _, _, _ => simp at ht

end SmallestNoncompletable.Search
