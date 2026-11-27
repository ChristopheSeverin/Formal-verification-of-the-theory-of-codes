module

public import SmallestNoncompletable.Codes
public import ThreeWordCodes.Definitions

/-! # A maximal code is complete (Proposition 2.5.6 of Berstel–Perrin–Reutenauer)

Let `y` be an unbordered word and `C` a maximal code not containing `y`. Then `C ∪ {y}` has two
distinct factorizations of one word, and we may assume that they start with different words.
Consider the leftmost occurrence of `y` in either factorization. The words of the other
factorization covering this occurrence are not `y`, because two overlapping occurrences of `y`
would give a border, and an occurrence at the same place would give equal first words. Hence
they lie in `C`, and `x y u ∈ C*`.

With `y = bᴺ w bᴺ aᴸ` for a long block of `a`, synchronization gives `bᴺ w bᴺ ∈ C*` when
`b ∈ C` and `N` bounds the lengths of the words of `C`. -/

@[expose] public section

namespace SmallestNoncompletable

open InformationTheory

variable {α : Type*}

/-- No nonempty proper prefix of `y` is a suffix of `y`. -/
def Unbordered (y : List α) : Prop :=
  ∀ p : List α, p ≠ [] → p.length < y.length → p <+: y → p <:+ y → False

/-- Two overlapping occurrences of an unbordered word coincide. -/
theorem Unbordered.no_overlap {y : List α} (hy : Unbordered y) {p q p' q' : List α}
    (e : p ++ y ++ q = p' ++ y ++ q') (h1 : p.length < p'.length)
    (h2 : p'.length < p.length + y.length) : False := by
  have hp : p <+: p' := by
    have a1 : p <+: p' ++ y ++ q' := by
      rw [← e, List.append_assoc]
      exact List.prefix_append _ _
    have a2 : p' <+: p' ++ y ++ q' := by
      rw [List.append_assoc]
      exact List.prefix_append _ _
    exact List.prefix_of_prefix_length_le a1 a2 h1.le
  obtain ⟨r, rfl⟩ := hp
  simp only [List.length_append] at h1 h2
  have e' : y ++ q = r ++ (y ++ q') := by
    simp only [List.append_assoc] at e
    exact List.append_cancel_left e
  have hr : r <+: y := by
    have a1 : r <+: y ++ q := by rw [e']; exact List.prefix_append _ _
    exact List.prefix_of_prefix_length_le a1 (List.prefix_append _ _) (by omega)
  obtain ⟨s, rfl⟩ := hr
  have e'' : s ++ q = r ++ s ++ q' := by
    simp only [List.append_assoc] at e' ⊢
    exact List.append_cancel_left e'
  have hs : s <+: r ++ s := by
    have a1 : s <+: r ++ s ++ q' := by rw [← e'']; exact List.prefix_append _ _
    exact List.prefix_of_prefix_length_le a1 (List.prefix_append _ _) (by simp)
  simp only [List.length_append] at h2
  exact hy s (by rintro rfl; simp at h2) (by simp; omega) hs (List.suffix_append r s)

/-- A list containing `y` splits at the first occurrence of `y`. -/
theorem exists_first_occurrence {L : List (List α)} {y : List α} (h : y ∈ L) :
    ∃ A B, L = A ++ y :: B ∧ y ∉ A := by
  induction L with
  | nil => simp at h
  | cons x L ih =>
    by_cases hx : x = y
    · exact ⟨[], L, by simp [hx], by simp⟩
    · have hy : y ∈ L := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨A, B, rfl, hA⟩ := ih hy
      exact ⟨x :: A, B, rfl, by simp [Ne.symm hx, hA]⟩

/-- A prefix of a factorization covering the first `n` letters, all of whose words start before
position `n`. -/
theorem exists_cover (L : List (List α)) {n : ℕ} (hn : n ≤ L.flatten.length) :
    ∃ P Q, L = P ++ Q ∧ n ≤ P.flatten.length ∧
      ∀ P' e Q', P = P' ++ e :: Q' → P'.flatten.length < n := by
  induction L generalizing n with
  | nil =>
    refine ⟨[], [], rfl, by simpa using hn, fun P' e Q' h => ?_⟩
    simp at h
  | cons x L ih =>
    by_cases h0 : n = 0
    · refine ⟨[], x :: L, rfl, by simp [h0], fun P' e Q' h => ?_⟩
      simp at h
    by_cases hx : n ≤ x.length
    · refine ⟨[x], L, rfl, by simpa using hx, fun P' e Q' h => ?_⟩
      cases P' with
      | nil => simp only [List.flatten_nil, List.length_nil]; omega
      | cons z P' => simp at h
    · push Not at hx
      have hn' : n - x.length ≤ L.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hn
        omega
      obtain ⟨P, Q, rfl, h1, h2⟩ := ih hn'
      refine ⟨x :: P, Q, rfl, ?_, fun P' e Q' h => ?_⟩
      · simp only [List.flatten_cons, List.length_append]
        omega
      cases P' with
      | nil => simp only [List.flatten_nil, List.length_nil]; omega
      | cons z P' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        have := h2 P' e Q' h
        simp only [List.flatten_cons, List.length_append]
        omega

/-- In a list of nonempty words, a prefix list with the same total length is the whole list. -/
theorem eq_of_prefix_of_flatten_length {A P : List (List α)} (hne : ∀ x ∈ P, x ≠ [])
    (h : A <+: P) (hl : P.flatten.length ≤ A.flatten.length) : A = P := by
  obtain ⟨R, rfl⟩ := h
  cases R with
  | nil => simp
  | cons r R =>
    have hr : r ≠ [] := hne r (by simp)
    have : 0 < r.length := List.length_pos_iff.mpr hr
    simp only [List.flatten_append, List.flatten_cons, List.length_append] at hl
    omega

/-- The core of the argument: if every occurrence of `y` in the second factorization starts after
the end of the first occurrence of `y` in the first factorization, the second factorization
covers that occurrence by words of `C`. -/
theorem context_of_late {C : Set (List α)} {y : List α} {A₁ B₁ L₂ : List (List α)}
    (hL₂ : ∀ x ∈ L₂, x ∈ C ∨ x = y)
    (e : (A₁ ++ y :: B₁).flatten = L₂.flatten)
    (hocc : ∀ P Q, L₂ = P ++ y :: Q → A₁.flatten.length + y.length ≤ P.flatten.length) :
    ∃ u, A₁.flatten ++ y ++ u ∈ Star C := by
  set n := A₁.flatten.length + y.length
  have hn : n ≤ L₂.flatten.length := by
    rw [← e]
    simp only [List.flatten_append, List.flatten_cons, List.length_append, n]
    omega
  obtain ⟨P, Q, rfl, hPn, hP⟩ := exists_cover L₂ hn
  have hPC : ∀ x ∈ P, x ∈ C := by
    intro x hx
    obtain ⟨P', Q', rfl⟩ := List.append_of_mem hx
    rcases hL₂ x (by simp) with h | rfl
    · exact h
    · have h1 := hP P' x Q' rfl
      have h2 := hocc P' (Q' ++ Q) (by simp)
      omega
  refine ⟨P.flatten.drop n, ?_⟩
  have hpre : P.flatten.take n = A₁.flatten ++ y := by
    have e2 : A₁.flatten ++ y ++ B₁.flatten = P.flatten ++ Q.flatten := by simpa using e
    have := congrArg (List.take n) e2
    rw [List.take_append_of_le_length hPn, List.take_left' (by simp [n])] at this
    exact this.symm
  rw [← hpre, List.take_append_drop]
  exact ⟨P, hPC, rfl⟩

/-- Distinct factorizations can be shortened to distinct factorizations with different first
words. -/
theorem exists_distinct_heads {Y : Set (List α)} (hne : ∀ x ∈ Y, x ≠ []) :
    ∀ L₁ L₂ : List (List α), (∀ x ∈ L₁, x ∈ Y) → (∀ x ∈ L₂, x ∈ Y) →
      L₁.flatten = L₂.flatten → L₁ ≠ L₂ →
      ∃ x₁ L₁' y₁ L₂', x₁ ≠ y₁ ∧ (∀ x ∈ x₁ :: L₁', x ∈ Y) ∧ (∀ x ∈ y₁ :: L₂', x ∈ Y) ∧
        (x₁ :: L₁').flatten = (y₁ :: L₂').flatten := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ e hneq
    cases L₂ with
    | nil => exact absurd rfl hneq
    | cons z L₂ =>
      have hz : z.length = 0 := by
        have := congrArg List.length e
        simp only [List.flatten_nil, List.length_nil, List.flatten_cons,
          List.length_append] at this
        omega
      exact absurd (List.length_eq_zero_iff.mp hz) (hne z (h₂ z (by simp)))
  | cons x L₁ ih =>
    intro L₂ h₁ h₂ e hneq
    cases L₂ with
    | nil =>
      have hx : x.length = 0 := by
        have := congrArg List.length e
        simp only [List.flatten_nil, List.length_nil, List.flatten_cons,
          List.length_append] at this
        omega
      exact absurd (List.length_eq_zero_iff.mp hx) (hne x (h₁ x (by simp)))
    | cons z L₂ =>
      by_cases hxz : x = z
      · subst hxz
        exact ih L₂ (fun w hw => h₁ w (by simp [hw])) (fun w hw => h₂ w (by simp [hw]))
          (by simpa using e) (fun h => hneq (by rw [h]))
      · exact ⟨x, L₁, z, L₂, hxz, h₁, h₂, e⟩

/-- **Proposition 2.5.6** for unbordered words: every unbordered word occurs in a word of `C*`
when `C` is a maximal code. -/
theorem exists_context {C : Set (List α)} (hC : ThreeWordCodes.IsMaximalCode C) {y : List α}
    (hy : Unbordered y) (hy0 : y ≠ []) : ∃ x u, x ++ y ++ u ∈ Star C := by
  classical
  by_cases hyC : y ∈ C
  · exact ⟨[], [], by simpa using mem_star_of_mem hyC⟩
  set Y := insert y C with hYdef
  have hCne : ∀ x ∈ C, x ≠ [] := fun x hx h => hC.1.epsilon_notMem (h ▸ hx)
  have hYne : ∀ x ∈ Y, x ≠ [] := by
    intro x hx
    rcases hx with rfl | hx
    exacts [hy0, hCne x hx]
  have hnotUD : ¬ IsUniquelyDecodable Y := by
    intro hU
    have := hC.2 Y (Set.subset_insert y C) hU
    exact hyC (this ▸ Set.mem_insert y C)
  simp only [IsUniquelyDecodable, not_forall] at hnotUD
  obtain ⟨L₁, L₂, h₁, h₂, e, hneq⟩ := hnotUD
  obtain ⟨x₁, M₁, y₁, M₂, hxy, hM₁, hM₂, eM⟩ :=
    exists_distinct_heads hYne L₁ L₂ h₁ h₂ e hneq
  -- Elements of the factorizations are in `C` or equal to `y`.
  have memY : ∀ {L : List (List α)}, (∀ x ∈ L, x ∈ Y) → ∀ x ∈ L, x ∈ C ∨ x = y := by
    intro L hL x hx
    rcases hL x hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- The argument for an ordered pair of factorizations.
  have ordered : ∀ (N₁ N₂ : List (List α)), (∀ x ∈ N₁, x ∈ Y) → (∀ x ∈ N₂, x ∈ Y) →
      N₁.flatten = N₂.flatten → N₁.head? ≠ N₂.head? → ∀ A₁ B₁, N₁ = A₁ ++ y :: B₁ → y ∉ A₁ →
      (∀ A₂ B₂, N₂ = A₂ ++ y :: B₂ → y ∉ A₂ → A₁.flatten.length ≤ A₂.flatten.length) →
      ∃ x u, x ++ y ++ u ∈ Star C := by
    intro N₁ N₂ hN₁ hN₂ eN hhead A₁ B₁ hsplit hA₁ hfirst
    have hA₁C : ∀ x ∈ A₁, x ∈ C := by
      intro x hx
      rcases memY hN₁ x (by rw [hsplit]; simp [hx]) with h | rfl
      · exact h
      · exact absurd hx hA₁
    refine ⟨A₁.flatten, ?_⟩
    apply context_of_late (memY hN₂) (by rw [← hsplit, eN])
    intro P Q hPQ
    -- The first occurrence of `y` in `N₂` is a prefix of `P`.
    obtain ⟨A₂, B₂, hs2, hA₂⟩ := exists_first_occurrence (show y ∈ N₂ by rw [hPQ]; simp)
    have hle := hfirst A₂ B₂ hs2 hA₂
    have hpre : A₂ <+: P := by
      by_contra hnot
      have hlt : P.length < A₂.length := by
        by_contra hge
        push Not at hge
        apply hnot
        have a1 : A₂ <+: N₂ := by rw [hs2]; exact List.prefix_append _ _
        have a2 : P <+: N₂ := by rw [hPQ]; exact List.prefix_append _ _
        exact List.prefix_of_prefix_length_le a1 a2 hge
      apply hA₂
      have : N₂[P.length]? = some y := by rw [hPQ]; simp
      rw [hs2, List.getElem?_append_left hlt] at this
      exact List.mem_of_getElem? this
    have hflat : A₂.flatten.length ≤ P.flatten.length := by
      obtain ⟨R, rfl⟩ := hpre
      simp
    -- Compare the positions of the two occurrences.
    have eD : A₁.flatten ++ y ++ B₁.flatten = P.flatten ++ y ++ Q.flatten := by
      have := eN
      rw [hsplit, hPQ] at this
      simpa using this
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_or_eq_of_le (hle.trans hflat) with hlt' | heq
    · exact hy.no_overlap eD hlt' hlt
    · -- Equal positions: the prefixes are equal factorizations in `C`.
      have hPA : A₂ = P := eq_of_prefix_of_flatten_length (fun x hx => hYne x (hN₂ x
        (by rw [hPQ]; simp [hx]))) hpre (by omega)
      subst hPA
      have hA₂C : ∀ x ∈ A₂, x ∈ C := by
        intro x hx
        rcases memY hN₂ x (by rw [hs2]; simp [hx]) with h | rfl
        · exact h
        · exact absurd hx hA₂
      have eA : A₁.flatten = A₂.flatten := by
        have := congrArg (List.take A₁.flatten.length) eD
        rw [List.append_assoc, List.take_append_of_le_length le_rfl, List.take_length,
          List.append_assoc, List.take_append_of_le_length (by omega), List.take_of_length_le
          (by omega)] at this
        exact this
      have hAA := hC.1 A₁ A₂ hA₁C hA₂C eA
      subst hAA
      apply hhead
      rw [hsplit, hs2]
      cases A₁ <;> simp
  -- At least one factorization contains `y`.
  have hsome : y ∈ x₁ :: M₁ ∨ y ∈ y₁ :: M₂ := by
    by_contra hnone
    push Not at hnone
    have hC₁ : ∀ x ∈ x₁ :: M₁, x ∈ C := fun x hx => by
      rcases memY hM₁ x hx with h | rfl
      exacts [h, absurd hx hnone.1]
    have hC₂ : ∀ x ∈ y₁ :: M₂, x ∈ C := fun x hx => by
      rcases memY hM₂ x hx with h | rfl
      exacts [h, absurd hx hnone.2]
    exact hxy (List.cons.inj (hC.1 _ _ hC₁ hC₂ eM)).1
  have hhead : (x₁ :: M₁).head? ≠ (y₁ :: M₂).head? := by simpa using hxy
  -- Order the two factorizations by the position of their first occurrence of `y`.
  by_cases h₁ : y ∈ x₁ :: M₁
  · obtain ⟨A₁, B₁, hs1, hA₁⟩ := exists_first_occurrence h₁
    by_cases h₂ : y ∈ y₁ :: M₂
    · obtain ⟨A₂, B₂, hs2, hA₂⟩ := exists_first_occurrence h₂
      -- The first occurrence in a list is unique.
      have uniq : ∀ {N : List (List α)} {A B A' B' : List (List α)}, N = A ++ y :: B → y ∉ A →
          N = A' ++ y :: B' → y ∉ A' → A = A' := by
        intro N A B A' B' h h' g g'
        rw [h] at g
        rcases List.append_eq_append_iff.mp g with ⟨c, rfl, hc⟩ | ⟨c, rfl, hc⟩
        · cases c with
          | nil => simp
          | cons z c =>
            simp only [List.cons_append, List.cons.injEq] at hc
            exact absurd (hc.1 ▸ List.mem_append_right A (List.mem_cons_self ..)) g'
        · cases c with
          | nil => simp
          | cons z c =>
            simp only [List.cons_append, List.cons.injEq] at hc
            exact absurd (hc.1 ▸ List.mem_append_right A' (List.mem_cons_self ..)) h'
      rcases le_total A₁.flatten.length A₂.flatten.length with hle | hle
      · exact ordered _ _ hM₁ hM₂ eM hhead A₁ B₁ hs1 hA₁ fun A B h h' => by
          rw [← uniq hs2 hA₂ h h']; exact hle
      · exact ordered _ _ hM₂ hM₁ eM.symm (Ne.symm hhead) A₂ B₂ hs2 hA₂ fun A B h h' => by
          rw [← uniq hs1 hA₁ h h']; exact hle
    · exact ordered _ _ hM₁ hM₂ eM hhead A₁ B₁ hs1 hA₁ fun A B h _ => absurd
        (show y ∈ y₁ :: M₂ by rw [h]; simp) h₂
  · have h₂ : y ∈ y₁ :: M₂ := hsome.resolve_left h₁
    obtain ⟨A₂, B₂, hs2, hA₂⟩ := exists_first_occurrence h₂
    exact ordered _ _ hM₂ hM₁ eM.symm (Ne.symm hhead) A₂ B₂ hs2 hA₂ fun A B h _ => absurd
      (show y ∈ x₁ :: M₁ by rw [h]; simp) h₁

/-- The word `bᴺ w bᴺ aᴸ` with `L = 2N + |w| + 1` is unbordered. -/
theorem unbordered_block {a b : α} (hab : a ≠ b) {N : ℕ} (hN : 1 ≤ N) (w : List α) :
    Unbordered (List.replicate N b ++ w ++ List.replicate N b ++
      List.replicate (2 * N + w.length + 1) a) := by
  set X := List.replicate N b ++ w ++ List.replicate N b with hX
  set y := X ++ List.replicate (2 * N + w.length + 1) a with hy
  have hXlen : X.length = 2 * N + w.length := by simp [hX]; omega
  have hylen : y.length = 2 * (2 * N + w.length) + 1 := by simp [hy, hXlen]; omega
  intro p hp0 hplen hpre hsuf
  have ht := List.prefix_iff_eq_take.mp hpre
  have hd := List.suffix_iff_eq_drop.mp hsuf
  have hpos : 0 < p.length := List.length_pos_iff.mpr hp0
  -- An index where the prefix reads `b` and the suffix reads `a`.
  set i := if p.length ≤ 2 * N + w.length + 1 then 0 else 2 * N + w.length - 1 with hi
  have hip : i < p.length := by rw [hi]; split_ifs <;> omega
  have hXb : ∀ j, j < X.length → (j < N ∨ N + w.length ≤ j) → X[j]? = some b := by
    intro j hj hcase
    rw [hXlen] at hj
    simp only [hX, List.append_assoc]
    rcases hcase with h | h
    · rw [List.getElem?_append_left (by simpa using h)]
      simp [h]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getElem?_replicate]
      rw [ite_eq_left (by omega)]
  have left : y[i]? = some b := by
    have hiX : i < X.length := by rw [hi, hXlen]; split_ifs <;> omega
    rw [hy, List.getElem?_append_left hiX]
    exact hXb i hiX (by rw [hi]; split_ifs <;> omega)
  have right : y[y.length - p.length + i]? = some a := by
    have hge : X.length ≤ y.length - p.length + i := by
      rw [hi, hylen, hXlen]; split_ifs <;> omega
    have hlt : y.length - p.length + i < y.length := by omega
    rw [hy, List.getElem?_append_right hge, List.getElem?_replicate]
    rw [ite_eq_left (by rw [hXlen]; omega)]
  have e1 : p[i]? = y[i]? := by
    conv_lhs => rw [ht]
    rw [List.getElem?_take_of_lt hip]
  have e2 : p[i]? = y[y.length - p.length + i]? := by
    conv_lhs => rw [hd]
    rw [List.getElem?_drop]
  have := e1.symm.trans e2
  rw [left, right] at this
  exact hab (Option.some.inj this).symm

/-- **Synchronization for maximal codes.** If `b ∈ C` and `N ≥ 1` bounds the lengths of the
words of a maximal code `C` over an alphabet with another letter `a`, then `bᴺ w bᴺ ∈ C*` for
every word `w`. -/
theorem sync_of_maximal {C : Set (List α)} (hC : ThreeWordCodes.IsMaximalCode C) {a b : α}
    (hab : a ≠ b) (hb : [b] ∈ C) {N : ℕ} (hN1 : 1 ≤ N) (hN : ∀ x ∈ C, x.length ≤ N)
    (w : List α) : List.replicate N b ++ w ++ List.replicate N b ∈ Star C := by
  obtain ⟨x, u, h⟩ := exists_context hC (unbordered_block hab hN1 w)
    (by intro h; have := congrArg List.length h; simp at this)
  apply sync_of_factor hb hN (x := x) (y := List.replicate (2 * N + w.length + 1) a ++ u)
  simpa only [List.append_assoc] using h

end SmallestNoncompletable
