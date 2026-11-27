module

public import SmallestNoncompletable.SearchDefs
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.Infix
import Mathlib.Tactic.Ring

/-! # Arithmetic of the checker

Base `8` codes of words, and the meaning of the helper functions of `SearchDefs`. -/

@[expose] public section

namespace SmallestNoncompletable.Search

/-! ## Cutting a pattern into words -/

/-- Cut a list into consecutive pieces of the given lengths. -/
def cut : List ℕ → List ℕ → List (List ℕ)
  | [], _ => []
  | l :: ls, p => p.take l :: cut ls (p.drop l)

/-! ## Codes of words -/

/-- The base `8` code of a word, most significant letter first. -/
def code (w : List ℕ) : ℕ := w.foldl (fun c x => 8 * c + x) 0

/-- All letters are below `8`. -/
def Small (w : List ℕ) : Prop := ∀ x ∈ w, x < 8

theorem foldl_code (w : List ℕ) (c : ℕ) :
    w.foldl (fun c x => 8 * c + x) c = c * 8 ^ w.length + code w := by
  induction w generalizing c with
  | nil => simp [code]
  | cons x w ih =>
    simp only [List.foldl_cons, code, List.length_cons]
    rw [ih, ih (8 * 0 + x)]
    ring

@[simp] theorem code_nil : code [] = 0 := rfl

theorem code_append (u v : List ℕ) : code (u ++ v) = code u * 8 ^ v.length + code v := by
  rw [code, List.foldl_append, foldl_code]
  rfl

theorem code_cons (x : ℕ) (w : List ℕ) : code (x :: w) = x * 8 ^ w.length + code w := by
  have := code_append [x] w
  simpa [code] using this

theorem code_concat (w : List ℕ) (x : ℕ) : code (w ++ [x]) = 8 * code w + x := by
  rw [code_append]; simp [code]; ring

theorem code_lt {w : List ℕ} (hw : Small w) : code w < 8 ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    rw [code_concat, List.length_append, List.length_singleton, pow_succ]
    have h1 := ih fun y hy => hw y (List.mem_append_left _ hy)
    have h2 := hw x (by simp)
    omega

theorem code_append_div {u v : List ℕ} (hv : Small v) : code (u ++ v) / 8 ^ v.length = code u := by
  rw [code_append, Nat.mul_comm, Nat.mul_add_div (pow_pos (by norm_num) _),
    Nat.div_eq_of_lt (code_lt hv), add_zero]

theorem code_append_mod {u v : List ℕ} (hv : Small v) : code (u ++ v) % 8 ^ v.length = code v := by
  rw [code_append, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (code_lt hv)]

theorem code_injective {u v : List ℕ} (hu : Small u) (hv : Small v) (hl : u.length = v.length)
    (h : code u = code v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => simpa [eq_comm] using hl
  | append_singleton u x ih =>
    obtain ⟨v, y, rfl⟩ : ∃ v' y, v = v' ++ [y] := by
      have hne : v ≠ [] := by rintro rfl; simp at hl
      exact ⟨v.dropLast, v.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    rw [code_concat, code_concat] at h
    have hx := hu x (by simp)
    have hy := hv y (by simp)
    have hxy : x = y := by omega
    subst hxy
    have : code u = code v := by omega
    rw [ih (fun z hz => hu z (List.mem_append_left _ hz)) (fun z hz => hv z (List.mem_append_left _ hz))
      (by simpa using hl) this]

theorem Small.append {u v : List ℕ} (hu : Small u) (hv : Small v) : Small (u ++ v) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  exacts [hu x h, hv x h]

theorem Small.of_sublist {u v : List ℕ} (hv : Small v) (h : u.Sublist v) : Small u :=
  fun x hx => hv x (h.subset hx)

/-- The first letter of a nonempty word. -/
theorem code_head {x : ℕ} {w : List ℕ} (hw : Small w) :
    code (x :: w) / 8 ^ w.length = x := by
  simpa [code] using code_append_div (u := [x]) hw

theorem code_last {w : List ℕ} {x : ℕ} (hx : x < 8) : code (w ++ [x]) % 8 = x := by
  rw [code_concat]; omega

/-- A prefix test on codes. -/
theorem prefix_iff_code {v w : List ℕ} (hv : Small v) (hw : Small w) (hl : v.length ≤ w.length) :
    v <+: w ↔ code w / 8 ^ (w.length - v.length) = code v := by
  constructor
  · rintro ⟨t, rfl⟩
    have ht : Small t := hw.of_sublist (List.sublist_append_right _ _)
    simp only [List.length_append, Nat.add_sub_cancel_left]
    exact code_append_div ht
  · intro h
    have hd : Small (w.drop v.length) := hw.of_sublist (List.drop_sublist _ _)
    have ht : Small (w.take v.length) := hw.of_sublist (List.take_sublist _ _)
    have e : code (w.take v.length) = code v := by
      calc code (w.take v.length)
          = code (w.take v.length ++ w.drop v.length) / 8 ^ (w.drop v.length).length :=
            (code_append_div hd).symm
        _ = code w / 8 ^ (w.length - v.length) := by rw [List.take_append_drop, List.length_drop]
        _ = code v := h
    have := code_injective ht hv (by simp [hl]) e
    refine ⟨w.drop v.length, ?_⟩
    conv_rhs => rw [← List.take_append_drop v.length w]
    rw [this]

theorem suffix_iff_code {v w : List ℕ} (hv : Small v) (hw : Small w) (hl : v.length ≤ w.length) :
    v <:+ w ↔ code w % 8 ^ v.length = code v := by
  constructor
  · rintro ⟨t, rfl⟩
    exact code_append_mod hv
  · intro h
    have hd : Small (w.drop (w.length - v.length)) := hw.of_sublist (List.drop_sublist _ _)
    have hdl : (w.drop (w.length - v.length)).length = v.length := by simp; omega
    have e : code (w.drop (w.length - v.length)) = code v := by
      calc code (w.drop (w.length - v.length))
          = code (w.take (w.length - v.length) ++ w.drop (w.length - v.length)) %
              8 ^ (w.drop (w.length - v.length)).length := (code_append_mod hd).symm
        _ = code w % 8 ^ v.length := by rw [List.take_append_drop, hdl]
        _ = code v := h
    have := code_injective hd hv hdl e
    refine ⟨w.take (w.length - v.length), ?_⟩
    conv_rhs => rw [← List.take_append_drop (w.length - v.length) w]
    rw [this]

/-! ## Helper functions -/

theorem p8_eq (n : ℕ) : p8 n = 8 ^ n := by
  show 1 <<< (3 * n) = 8 ^ n
  rw [Nat.shiftLeft_eq, one_mul, pow_mul]
  norm_num

theorem bit_eq (m x : ℕ) : bit m x = m / 2 ^ x % 2 := by
  show (m >>> x) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem bit_le_one (m x : ℕ) : bit m x ≤ 1 := by
  rw [bit_eq]; omega

theorem bit_eq_one {m x : ℕ} : bit m x = 1 ↔ m.testBit x = true := by
  rw [bit_eq, Nat.testBit_eq_decide_div_mod_eq]; simp

theorem bit_lor_shift (S j x : ℕ) : bit (Nat.lor S (Nat.shiftLeft 1 j)) x = 1 ↔ bit S x = 1 ∨ x = j := by
  rw [bit_eq_one, bit_eq_one]
  have : Nat.lor S (Nat.shiftLeft 1 j) = S ||| (1 <<< j) := rfl
  rw [this, Nat.testBit_lor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq, @eq_comm _ j x]

theorem memN_iff (x : ℕ) (l : List ℕ) : memN x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memN]
  | cons y l ih => simp [memN, ih, Nat.beq_eq]

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq_true_of_le h'] at h
    simp [max_eq_left (by omega : b ≤ a)]
  · simp [max_eq_right (Nat.le_of_ble_eq_true h)]

theorem minN_eq (a b : ℕ) : minN a b = min a b := by
  unfold minN
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq_true_of_le h'] at h
    simp [min_eq_right (by omega : b ≤ a)]
  · simp [min_eq_left (Nat.le_of_ble_eq_true h)]

/-- `missing m s n` counts the letters of `[s, s + n)` whose bit is clear. -/
theorem missing_eq (m s : ℕ) : ∀ n,
    missing m s n = (List.range n).countP fun x => bit m (s + x) ≠ 1
  | 0 => by simp [missing]
  | n + 1 => by
    rw [missing, missing_eq m s n, List.range_succ, List.countP_append]
    have := bit_le_one m (s + n)
    by_cases h : bit m (s + n) = 1 <;> simp [h]; omega

/-! ## Profile functions -/

/-- Start positions of the long words. -/
def startsL : List ℕ → List ℕ
  | [] => []
  | l :: ls => 0 :: (startsL ls).map (· + l)

/-- End positions of the long words. -/
def endsL : List ℕ → List ℕ
  | [] => []
  | l :: ls => (l - 1) :: (endsL ls).map (· + l)

theorem isStart_iff : ∀ (lens : List ℕ) (i : ℕ), isStart lens i = true ↔ i ∈ startsL lens
  | [], _ => by simp [isStart, startsL]
  | l :: ls, i => by
    simp only [isStart, startsL, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq,
      Nat.ble_eq, List.mem_cons, List.mem_map, isStart_iff ls]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i - l, h2, by omega⟩
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · right; exact ⟨by omega, by simpa using ha⟩

theorem isEnd_iff : ∀ (lens : List ℕ), (∀ l ∈ lens, 1 ≤ l) → ∀ i : ℕ,
    isEnd lens i = true ↔ i ∈ endsL lens
  | [], _, _ => by simp [isEnd, endsL]
  | l :: ls, hl, i => by
    have h1 := hl l (by simp)
    simp only [isEnd, endsL, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq,
      Nat.ble_eq, List.mem_cons, List.mem_map,
      isEnd_iff ls (fun l' h => hl l' (List.mem_cons_of_mem _ h))]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨i - l, h2, by omega⟩
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl (by omega)
      · right; exact ⟨by omega, by simpa using ha⟩

theorem remStarts_eq : ∀ (lens : List ℕ) (i : ℕ), remStarts lens i = (startsL lens).countP (i ≤ ·)
  | [], _ => by simp [remStarts, startsL]
  | l :: ls, i => by
    rw [remStarts, startsL, List.countP_cons, List.countP_map, remStarts_eq ls]
    have h1 : List.countP (fun x => decide (i - l ≤ x)) (startsL ls) =
        List.countP ((fun x => decide (i ≤ x)) ∘ fun x => x + l) (startsL ls) := by
      apply List.countP_congr
      intro x _
      simp only [Function.comp_apply, decide_eq_true_eq]
      omega
    have h2 : cond (Nat.beq i 0) 1 0 = if decide (i ≤ 0) = true then 1 else 0 := by
      by_cases h : i = 0 <;> simp [h, Nat.beq_eq]
    rw [h1, h2, Nat.add_comm]

theorem remEnds_eq : ∀ (lens : List ℕ), (∀ l ∈ lens, 1 ≤ l) → ∀ i : ℕ,
    remEnds lens i = (endsL lens).countP (i ≤ ·)
  | [], _, _ => by simp [remEnds, endsL]
  | l :: ls, hl, i => by
    have hl1 := hl l (by simp)
    rw [remEnds, endsL, List.countP_cons, List.countP_map,
      remEnds_eq ls (fun l' h => hl l' (List.mem_cons_of_mem _ h))]
    have h1 : List.countP (fun x => decide (i - l ≤ x)) (endsL ls) =
        List.countP ((fun x => decide (i ≤ x)) ∘ fun x => x + l) (endsL ls) := by
      apply List.countP_congr
      intro x _
      simp only [Function.comp_apply, decide_eq_true_eq]
      omega
    have h2 : cond (Nat.blt i l) 1 0 = if decide (i ≤ l - 1) = true then 1 else 0 := by
      by_cases h : i < l
      · simp [h, Nat.blt_eq, show i ≤ l - 1 by omega]
      · simp [h, Nat.blt_eq, show ¬ i ≤ l - 1 by omega]
    rw [h1, h2, Nat.add_comm]

end SmallestNoncompletable.Search
