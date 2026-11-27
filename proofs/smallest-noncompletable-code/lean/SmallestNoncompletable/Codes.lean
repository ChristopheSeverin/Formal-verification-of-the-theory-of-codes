module

public import SmallestNoncompletable.Residuals
public import Mathlib.InformationTheory.Coding.UniquelyDecodable
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # Codes, their stars and restrictions

`Star M` is the set of concatenations of words of `M`. For a code, the characteristic series
`τ` of `Star M` satisfies `τ = 1 + M τ = 1 + τ M`, because the first and the last word of a
factorization are unique. A code pulls back to a code along an injective map of letters.

If `b ∈ C` and every word of `C` has length at most `N`, then any factorization of a word
containing `bᴺ w bᴺ` cuts each of the two blocks. Hence `bᴺ w bᴺ ∈ C*`. -/

@[expose] public section

namespace SmallestNoncompletable

open InformationTheory

variable {α β : Type*}

/-- The concatenations of words of `M`, including the empty word. -/
def Star (M : Set (List α)) : Set (List α) :=
  {w | ∃ L : List (List α), (∀ x ∈ L, x ∈ M) ∧ L.flatten = w}

theorem nil_mem_star (M : Set (List α)) : [] ∈ Star M := ⟨[], by simp, rfl⟩

theorem append_mem_star {M : Set (List α)} {u v : List α} (hu : u ∈ Star M) (hv : v ∈ Star M) :
    u ++ v ∈ Star M := by
  obtain ⟨L, hL, rfl⟩ := hu
  obtain ⟨L', hL', rfl⟩ := hv
  exact ⟨L ++ L', fun x hx => (List.mem_append.mp hx).elim (hL x) (hL' x), by simp⟩

theorem mem_star_of_mem {M : Set (List α)} {u : List α} (hu : u ∈ M) : u ∈ Star M :=
  ⟨[u], by simpa using hu, by simp⟩

theorem replicate_mem_star {M : Set (List α)} {u : List α} (hu : u ∈ M) (n : ℕ) :
    (List.replicate n u).flatten ∈ Star M :=
  ⟨List.replicate n u, fun _ hx => (List.eq_of_mem_replicate hx) ▸ hu, rfl⟩

theorem replicate_letter_mem_star {M : Set (List α)} {b : α} (hb : [b] ∈ M) (n : ℕ) :
    List.replicate n b ∈ Star M := by
  have := replicate_mem_star hb n
  rwa [List.flatten_replicate_singleton] at this

section Series

variable {K : Type*} [Field K]

open Ser

/-- The first word of a factorization in a code is unique: `M τ = τ - 1`. -/
theorem star_eq_one_add_mul {M : Set (List α)} (hM : IsUniquelyDecodable M) :
    (Ser.char (Star M) : Ser α K) = 1 + Ser.char M * Ser.char (Star M) := by
  classical
  have hne : [] ∉ M := hM.epsilon_notMem
  ext w
  rw [coeff_add, coeff_mul]
  have hterm : ∀ i ∈ Finset.range (w.length + 1),
      (Ser.char M : Ser α K).coeff (w.take i) * (Ser.char (Star M)).coeff (w.drop i) =
        if w.take i ∈ M ∧ w.drop i ∈ Star M then 1 else 0 := by
    intro i _
    rw [coeff_char, coeff_char]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  set I := (Finset.range (w.length + 1)).filter (fun i => w.take i ∈ M ∧ w.drop i ∈ Star M)
  have hcard : I.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [I, Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨hi, hiM, ⟨Li, hLi, ei⟩⟩ := hi
    obtain ⟨hj, hjM, ⟨Lj, hLj, ej⟩⟩ := hj
    have e := hM (w.take i :: Li) (w.take j :: Lj)
      (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [hiM, hLi x hx])
      (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [hjM, hLj x hx])
      (by simp [ei, ej])
    have := congrArg List.length (List.cons.inj e).1
    simp only [List.length_take] at this
    omega
  by_cases hw : w ∈ Star M ∧ w ≠ []
  · obtain ⟨⟨L, hL, rfl⟩, hw0⟩ := hw
    obtain ⟨x, L', rfl⟩ : ∃ x L', L = x :: L' := by
      cases L with
      | nil => exact absurd rfl hw0
      | cons x L' => exact ⟨x, L', rfl⟩
    have hx : x ∈ M := hL x (by simp)
    have hmem : x.length ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_range, List.flatten_cons]
      refine ⟨by simp, by simpa using hx, ?_⟩
      rw [List.drop_left]
      exact ⟨L', fun y hy => hL y (by simp [hy]), rfl⟩
    have h1 : I.card = 1 := le_antisymm hcard (Finset.card_pos.mpr ⟨_, hmem⟩)
    rw [h1, coeff_char_of_mem (show (x :: L').flatten ∈ Star M from ⟨x :: L', hL, rfl⟩),
      coeff_one_of_ne_nil hw0]
    simp
  · have hI : I = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [I, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨_, hiM, hstar⟩ := hi
      apply hw
      refine ⟨?_, ?_⟩
      · rw [← List.take_append_drop i w]
        exact append_mem_star (mem_star_of_mem hiM) hstar
      · rintro rfl
        exact hne (by simpa using hiM)
    rw [hI, Finset.card_empty, Nat.cast_zero, add_zero]
    by_cases hw0 : w = []
    · subst hw0
      rw [coeff_char_of_mem (nil_mem_star M)]
      rfl
    · have hns : w ∉ Star M := fun h => hw ⟨h, hw0⟩
      rw [coeff_char_of_notMem hns]
      cases w with
      | nil => exact absurd rfl hw0
      | cons a w => rfl

/-- The last word of a factorization is unique as well, since `1 - M` is invertible. -/
theorem star_eq_one_add_mul' {M : Set (List α)} (hM : IsUniquelyDecodable M) :
    (Ser.char (Star M) : Ser α K) = 1 + Ser.char (Star M) * Ser.char M := by
  have h1 := star_eq_one_add_mul (K := K) hM
  set τ := (Ser.char (Star M) : Ser α K)
  set m := (Ser.char M : Ser α K)
  have hm0 : m.coeff [] = 0 := coeff_char_of_notMem hM.epsilon_notMem
  have hu : IsUnit (1 - m) := isUnit_of_coeff_nil_ne_zero (by simp [hm0])
  have e1 : (1 - m) * τ = 1 := by
    rw [sub_mul, one_mul, ← sub_eq_iff_eq_add.mpr h1]
  have e2 : τ * (1 - m) = 1 := by
    have : τ = Ring.inverse (1 - m) := by
      calc τ = Ring.inverse (1 - m) * ((1 - m) * τ) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
        _ = Ring.inverse (1 - m) := by rw [e1, mul_one]
    rw [this, Ring.inverse_mul_cancel _ hu]
  rw [mul_sub, mul_one] at e2
  rw [← e2]
  abel

end Series

section Pullback

/-- The words whose image under the letter map lies in `C`. -/
def pullback (ι : β → α) (C : Set (List α)) : Set (List β) := {v | v.map ι ∈ C}

theorem pullback_uniquelyDecodable {ι : β → α} (hι : Function.Injective ι) {C : Set (List α)}
    (hC : IsUniquelyDecodable C) : IsUniquelyDecodable (pullback ι C) := by
  intro L₁ L₂ h₁ h₂ e
  have hmap := hC (L₁.map (List.map ι)) (L₂.map (List.map ι))
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h₁ y hy)
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h₂ y hy)
    (by rw [← List.map_flatten, ← List.map_flatten, e])
  exact List.map_injective_iff.mpr (List.map_injective_iff.mpr hι) hmap

/-- A factorization of the image of a word comes from a factorization of the word. -/
theorem mem_star_pullback {ι : β → α} {C : Set (List α)} {v : List β}
    (h : v.map ι ∈ Star C) : v ∈ Star (pullback ι C) := by
  obtain ⟨L, hL, e⟩ := h
  induction L generalizing v with
  | nil =>
    simp only [List.flatten_nil] at e
    have : v = [] := List.map_eq_nil_iff.mp e.symm
    subst this
    exact nil_mem_star _
  | cons x L ih =>
    simp only [List.flatten_cons] at e
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp e.symm
    have hx : v₁ ∈ pullback ι C := by
      change v₁.map ι ∈ C
      rw [h₁]
      exact hL x (by simp)
    exact append_mem_star (mem_star_of_mem hx) (ih (fun y hy => hL y (by simp [hy])) h₂.symm)

theorem pullback_finite {ι : β → α} (hι : Function.Injective ι) {C : Set (List α)}
    (hC : C.Finite) : (pullback ι C).Finite :=
  hC.preimage (List.map_injective_iff.mpr hι).injOn

end Pullback

section Cuts

/-- Every window of length `N` contains a cut of a factorization into words of length at most
`N`. -/
theorem exists_cut {L : List (List α)} {N : ℕ} (hL : ∀ x ∈ L, x.length ≤ N) {j : ℕ}
    (hj : j ≤ L.flatten.length) :
    ∃ L₁ L₂, L = L₁ ++ L₂ ∧ j ≤ L₁.flatten.length ∧ L₁.flatten.length ≤ j + N := by
  induction L generalizing j with
  | nil => exact ⟨[], [], rfl, by simpa using hj, by simp⟩
  | cons x L ih =>
    by_cases h0 : j = 0
    · exact ⟨[], x :: L, rfl, by simp [h0], by simp⟩
    by_cases hx : j ≤ x.length
    · exact ⟨[x], L, rfl, by simpa using hx, by have := hL x (by simp); simp; omega⟩
    · push Not at hx
      have hj' : j - x.length ≤ L.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hj
        omega
      obtain ⟨L₁, L₂, rfl, h1, h2⟩ := ih (fun y hy => hL y (by simp [hy])) hj'
      refine ⟨x :: L₁, L₂, rfl, ?_, ?_⟩ <;>
      · simp only [List.flatten_cons, List.length_append]
        omega

/-- **Synchronization.** If `b ∈ C`, every word of `C` has length at most `N`, and the word
`bᴺ w bᴺ` occurs inside a word of `C*`, then `bᴺ w bᴺ ∈ C*`. -/
theorem sync_of_factor {C : Set (List α)} {b : α} (hb : [b] ∈ C) {N : ℕ}
    (hN : ∀ x ∈ C, x.length ≤ N) {x w y : List α}
    (h : x ++ (List.replicate N b ++ w ++ List.replicate N b) ++ y ∈ Star C) :
    List.replicate N b ++ w ++ List.replicate N b ∈ Star C := by
  obtain ⟨L, hL, e⟩ := h
  have hlen : ∀ z ∈ L, z.length ≤ N := fun z hz => hN z (hL z hz)
  set z := x ++ (List.replicate N b ++ w ++ List.replicate N b) ++ y with hz
  have hzlen : z.length = x.length + N + w.length + N + y.length := by
    simp [hz]; ring
  -- A cut in the first block of `b`.
  obtain ⟨L₁, L₂, rfl, c1, c1'⟩ := exists_cut hlen (j := x.length) (by rw [e]; omega)
  -- A cut in the second block of `b`.
  have hL₂ : ∀ z ∈ L₂, z.length ≤ N := fun z hz => hlen z (by simp [hz])
  have e' : L₁.flatten ++ L₂.flatten = z := by rw [← List.flatten_append, e]
  have hlen12 := congrArg List.length e'
  rw [List.length_append] at hlen12
  obtain ⟨L₃, L₄, rfl, c2, c2'⟩ := exists_cut hL₂
    (j := x.length + N + w.length - L₁.flatten.length) (by omega)
  -- The middle part is `bᵏ w bᵏ'`.
  set k := x.length + N - L₁.flatten.length
  set k' := L₁.flatten.length + L₃.flatten.length - (x.length + N + w.length)
  have hmid : L₃.flatten = List.replicate k b ++ w ++ List.replicate k' b := by
    have e3 : L₁.flatten ++ L₃.flatten ++ L₄.flatten = z := by
      rw [← e]
      simp
    have hdrop : L₃.flatten = ((z.drop L₁.flatten.length).take L₃.flatten.length) := by
      rw [← e3]
      simp
    rw [hdrop, hz]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_append, List.length_replicate]
      omega
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_drop]
      simp only [List.length_take, List.length_drop, List.length_append,
        List.length_replicate] at h1
      simp only [List.append_assoc, List.getElem_append, List.length_replicate,
        List.getElem_replicate]
      split_ifs <;> first | rfl | omega | (congr 1; omega)
  have hstar3 : L₃.flatten ∈ Star C := ⟨L₃, fun u hu => hL u (by simp [hu]), rfl⟩
  rw [hmid] at hstar3
  have hk1 : N - k + k = N := by omega
  have hk2 : k' + (N - k') = N := by omega
  have key : List.replicate N b ++ w ++ List.replicate N b = List.replicate (N - k) b ++
      (List.replicate k b ++ w ++ List.replicate k' b) ++ List.replicate (N - k') b := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (List.replicate (N - k) b), List.replicate_append_replicate,
      List.replicate_append_replicate, hk1, hk2]
  rw [key]
  exact append_mem_star (append_mem_star (replicate_letter_mem_star hb (N - k)) hstar3)
    (replicate_letter_mem_star hb (N - k'))

end Cuts

end SmallestNoncompletable
