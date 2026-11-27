module

public import SmallestNoncompletable.SearchLeaf

/-! # Soundness of the certificates

A tree certificate lists internal nodes by their codes with a leading `1`; it describes a finite
rooted prefix-closed tree through which every word reads back to the root. An ambiguity
certificate gives two lists of word indices with equal concatenations. -/

@[expose] public section

namespace SmallestNoncompletable.Search

open ThreeWordCodes InformationTheory

/-! ## Node codes -/

/-- The code of a node: its letters below a leading `1`. -/
def enc (p : List ℕ) : ℕ := code (1 :: p)

theorem enc_nil : enc [] = 1 := rfl

theorem enc_concat (p : List ℕ) (x : ℕ) : enc (p ++ [x]) = 8 * enc p + x := by
  rw [enc, ← List.cons_append, code_concat]; rfl

theorem enc_bounds {p : List ℕ} (hp : Small p) : 8 ^ p.length ≤ enc p ∧ enc p < 2 * 8 ^ p.length := by
  rw [enc, code_cons]
  have := code_lt hp
  constructor <;> omega

theorem enc_injective {p p' : List ℕ} (hp : Small p) (hp' : Small p') (h : enc p = enc p') : p = p' := by
  have hl : p.length = p'.length := by
    have h1 := enc_bounds hp
    have h2 := enc_bounds hp'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : 2 * 8 ^ p.length ≤ 8 ^ p'.length := by
        calc 2 * 8 ^ p.length ≤ 8 * 8 ^ p.length := by omega
          _ = 8 ^ (p.length + 1) := by ring
          _ ≤ 8 ^ p'.length := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 * 8 ^ p'.length ≤ 8 ^ p.length := by
        calc 2 * 8 ^ p'.length ≤ 8 * 8 ^ p'.length := by omega
          _ = 8 ^ (p'.length + 1) := by ring
          _ ≤ 8 ^ p.length := Nat.pow_le_pow_right (by norm_num) hlt
      omega
  have := code_injective (u := 1 :: p) (v := 1 :: p')
    (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; omega; exact hp x hx)
    (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; omega; exact hp' x hx)
    (by simp [hl]) h
  exact (List.cons.inj this).2

/-- Valid node codes. -/
theorem lettersBelow_spec {k : ℕ} (hk : k ≤ 8) :
    ∀ (fuel e : ℕ), lettersBelow k fuel e = true →
      ∃ p, e = enc p ∧ (∀ x ∈ p, x < k) ∧ p.length ≤ fuel
  | 0, e, h => ⟨[], by rw [enc_nil]; simpa [lettersBelow, Nat.beq_eq] using h, by simp, by simp⟩
  | fuel + 1, e, h => by
    simp only [lettersBelow, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
      Nat.ble_eq] at h
    rcases h with rfl | ⟨⟨h1, h2⟩, h3⟩
    · exact ⟨[], rfl, by simp, by simp⟩
    · obtain ⟨p, hp, hpk, hpl⟩ := lettersBelow_spec hk fuel (e / 8) h3
      refine ⟨p ++ [e % 8], ?_, ?_, by simp; omega⟩
      · rw [enc_concat, ← hp]; omega
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hpk x hx
        · rw [List.mem_singleton.mp hx]; exact h1

/-- Decode a node code. -/
def ofCode : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, e => if e ≤ 1 then [] else ofCode fuel (e / 8) ++ [e % 8]

theorem ofCode_enc : ∀ (p : List ℕ), Small p → ∀ fuel, p.length < fuel → ofCode fuel (enc p) = p := by
  intro p hp
  induction p using List.reverseRecOn with
  | nil => intro fuel hf; cases fuel with
    | zero => simp at hf
    | succ n => simp [ofCode, enc_nil]
  | append_singleton p x ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ n =>
      have hx := hp x (by simp)
      have hp' : Small p := fun y hy => hp y (List.mem_append_left _ hy)
      have h1 := (enc_bounds hp').1
      have : 1 < enc (p ++ [x]) := by
        rw [enc_concat]; have := Nat.one_le_pow p.length 8 (by norm_num); omega
      rw [ofCode, ite_eq_right (by omega : ¬ (enc (p ++ [x]) ≤ 1)), enc_concat,
        show (8 * enc p + x) / 8 = enc p by omega,
        show (8 * enc p + x) % 8 = x by omega, ih hp' n (by simp at hf; omega)]

/-! ## Reading through node codes -/

/-- Reading a list of letters on node codes. -/
def readE (I : List ℕ) : ℕ → List ℕ → Bool
  | node, [] => Nat.beq node 1
  | node, x :: w => cond (memN (8 * node + x) I) (readE I (8 * node + x) w) (readE I 1 w)

theorem readF_eq (I : List ℕ) : ∀ (b a : List ℕ) (node : ℕ), Small (a ++ b) →
    readF I (code (a ++ b)) b.length node = readE I node b
  | [], _, _, _ => rfl
  | x :: b, a, node, hs => by
    have hx : (code (a ++ x :: b) / p8 b.length) % 8 = x := by
      rw [p8_eq, show a ++ x :: b = (a ++ [x]) ++ b by simp,
        code_append_div (hs.of_sublist (by simp)), code_last (hs x (by simp))]
    simp only [readF, List.length_cons, readE, hx]
    rw [show a ++ x :: b = (a ++ [x]) ++ b by simp]
    have hs' : Small ((a ++ [x]) ++ b) := by simpa using hs
    rw [readF_eq I b (a ++ [x]) _ hs', readF_eq I b (a ++ [x]) _ hs']

theorem readR_eq (I : List ℕ) : ∀ (w : List ℕ) (node : ℕ), Small w →
    readR I (code w) w.length node = readE I node w.reverse := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro node _; rfl
  | append_singleton u x ih =>
    intro node hs
    have hx := hs x (by simp)
    have hu : Small u := fun y hy => hs y (List.mem_append_left _ hy)
    rw [List.length_append, List.length_singleton, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    simp only [readR, readE, code_concat, show (8 * code u + x) % 8 = x by omega,
      show (8 * code u + x) / 8 = code u by omega, ih _ hu]

/-- The finite tree described by a list of node codes. -/
def treeOf (I : List ℕ) : Finset (List ℕ) := (I.map (ofCode 9)).toFinset

theorem mem_treeOf {I : List ℕ} {k : ℕ} (hk : k ≤ 8) (hI : ∀ e ∈ I, lettersBelow k 8 e = true)
    {p : List ℕ} (hp : Small p) : p ∈ treeOf I ↔ enc p ∈ I := by
  simp only [treeOf, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨q, rfl, hq, hql⟩ := lettersBelow_spec hk 8 e (hI e he)
    have hqs : Small q := fun x hx => by have := hq x hx; omega
    rwa [ofCode_enc q hqs 9 (by omega)]
  · intro he
    obtain ⟨q, hq, hqk, hql⟩ := lettersBelow_spec hk 8 _ (hI _ he)
    have hqs : Small q := fun x hx => by have := hqk x hx; omega
    have := enc_injective hp hqs hq
    subst this
    exact ⟨enc p, he, ofCode_enc p hp 9 (by omega)⟩

theorem treeOf_spec {I : List ℕ} {k : ℕ} (hk : k ≤ 8) (hI : ∀ e ∈ I, lettersBelow k 8 e = true)
    {p : List ℕ} (hp : p ∈ treeOf I) : Small p ∧ ∀ x ∈ p, x < k := by
  simp only [treeOf, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨e, he, rfl⟩ := hp
  obtain ⟨q, rfl, hq, hql⟩ := lettersBelow_spec hk 8 e (hI e he)
  have hqs : Small q := fun x hx => by have := hq x hx; omega
  rw [ofCode_enc q hqs 9 (by omega)]
  exact ⟨hqs, hq⟩

theorem one_lt_enc {p : List ℕ} (hp : Small p) (hne : p ≠ []) : 8 ≤ enc p := by
  have h1 := (enc_bounds hp).1
  obtain ⟨y, p', rfl⟩ := List.exists_cons_of_ne_nil hne
  have : 8 ≤ 8 ^ (y :: p').length := by
    simp only [List.length_cons, pow_succ]
    have := Nat.one_le_pow p'.length 8 (by norm_num)
    omega
  omega

/-- **Soundness of a tree certificate.** -/
theorem checkTree_sound {ws : List (List ℕ)} {k : ℕ} {rev : Bool} {I : List ℕ}
    (hk : k ≤ 8) (hsmall : ∀ w ∈ ws, Small w) (hocc : ∀ x < k, ∃ w ∈ ws, x ∈ w)
    (h : checkTree (pairs ws) k rev I = true) : Reducible ws.toFinset := by
  simp only [checkTree, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hroot, hclosed⟩, hlet⟩, hread⟩, x, hxk, hx⟩ := h
  rw [memN_iff] at hroot hx
  have hmem : ∀ p, Small p → (p ∈ treeOf I ↔ enc p ∈ I) := fun p hp => mem_treeOf hk hlet hp
  -- the tree is rooted and closed under removing the last letter, hence prefix-closed
  have hdrop : ∀ w ∈ treeOf I, ∀ y, w = w.dropLast ++ [y] → w.dropLast ∈ treeOf I := by
    intro w hw y hwy
    have hws := (treeOf_spec hk hlet hw).1
    have hw' := (hmem _ hws).mp hw
    have hy : y < 8 := hws y (by rw [hwy]; simp)
    have hds : Small w.dropLast := hws.of_sublist (List.dropLast_sublist _)
    have hne : w ≠ [] := by rw [hwy]; simp
    rcases hclosed _ hw' with h1 | h2
    · have := one_lt_enc hws hne; omega
    · rw [memN_iff, hwy, enc_concat, show (8 * enc w.dropLast + y) / 8 = enc w.dropLast by omega]
        at h2
      exact (hmem _ hds).mpr h2
  have hRP : RootedPrefixClosed (treeOf I) := by
    refine ⟨(hmem [] (by simp [Small])).mpr hroot, ?_⟩
    intro p w hw hp
    obtain ⟨t, rfl⟩ := hp
    induction t using List.reverseRecOn with
    | nil => simpa using hw
    | append_singleton t y ih =>
      apply ih
      have := hdrop _ hw y (by simp)
      simpa using this
  refine Or.inr (Or.inr (Or.inr ?_))
  have hletters : ∀ p ∈ treeOf I, ∀ y ∈ p, ∃ w ∈ ws.toFinset, y ∈ w := by
    intro p hp y hy
    obtain ⟨w, hw, hyw⟩ := hocc y ((treeOf_spec hk hlet hp).2 y hy)
    exact ⟨w, List.mem_toFinset.mpr hw, hyw⟩
  have hwit : ∃ w ∈ ws.toFinset, ∃ y ∈ w, [y] ∈ treeOf I := by
    obtain ⟨w, hw, hxw⟩ := hocc x hxk
    refine ⟨w, List.mem_toFinset.mpr hw, x, hxw, (hmem [x] ?_).mpr ?_⟩
    · intro y hy; rw [List.mem_singleton.mp hy]; omega
    · have : enc [x] = 8 + x := by simp [enc, code]
      rwa [this]
  -- reading: the node codes follow the tree
  have hreadE : ∀ (w node : List ℕ), Small w → Small node →
      readE I (enc node) w = readTree (treeOf I) node w := by
    intro w
    induction w with
    | nil =>
      intro node _ hn
      simp only [readE, readTree]
      rcases node with _ | ⟨y, node⟩
      · rfl
      · have : enc (y :: node) ≠ 1 := by have := one_lt_enc hn (by simp); omega
        rw [Bool.eq_iff_iff]
        simp [Nat.beq_eq, this]
    | cons y w ih =>
      intro node hw hn
      have hy := hw y (by simp)
      have hw' : Small w := fun z hz => hw z (by simp [hz])
      have hn' : Small (node ++ [y]) := hn.append (by intro z hz; rw [List.mem_singleton.mp hz]; exact hy)
      simp only [readE, readTree, ← enc_concat]
      by_cases hm : node ++ [y] ∈ treeOf I
      · have : memN (enc (node ++ [y])) I = true := (memN_iff _ _).mpr ((hmem _ hn').mp hm)
        rw [this, Bool.cond_true, ite_eq_left hm, ih _ hw' hn']
      · have : memN (enc (node ++ [y])) I = false := by
          rw [Bool.eq_false_iff]
          intro h'
          exact hm ((hmem _ hn').mpr ((memN_iff _ _).mp h'))
        rw [this, Bool.cond_false, ite_eq_right hm, ← enc_nil, ih _ hw' (by simp [Small])]
  cases rev
  · refine Or.inl ⟨treeOf I, hRP, hletters, ?_, hwit⟩
    intro w hw
    have hwl := List.mem_toFinset.mp hw
    have hws := hsmall w hwl
    have h1 := hread (code w, w.length) (List.mem_map.mpr ⟨w, hwl, rfl⟩)
    simp only [Bool.cond_false] at h1
    have h2 := readF_eq I w [] 1 (by simpa using hws)
    simp only [List.nil_append] at h2
    rw [h2, ← enc_nil, hreadE w [] hws (by simp [Small])] at h1
    exact h1
  · refine Or.inr ⟨treeOf I, hRP, hletters, ?_, hwit⟩
    intro w hw
    have hwl := List.mem_toFinset.mp hw
    have hws := hsmall w hwl
    have h1 := hread (code w, w.length) (List.mem_map.mpr ⟨w, hwl, rfl⟩)
    simp only [Bool.cond_true] at h1
    rw [readR_eq I w 1 hws, ← enc_nil,
      hreadE w.reverse [] (fun z hz => hws z (List.mem_reverse.mp hz)) (by simp [Small])] at h1
    exact h1

/-! ## Ambiguity certificates -/

/-- The concatenation of the words with the given indices. -/
def flatI (ws : List (List ℕ)) (l : List ℕ) : List ℕ := (l.map fun i => ws.getD i []).flatten

theorem getD_pairs (ws : List (List ℕ)) {i : ℕ} (hi : i < ws.length) :
    (pairs ws).getD i (0, 0) = (code (ws.getD i []), (ws.getD i []).length) := by
  simp [pairs, List.getD_eq_getElem?_getD, hi]

theorem concatCode_eq (ws : List (List ℕ)) :
    ∀ l : List ℕ, (∀ i ∈ l, i < ws.length) →
      concatCode (pairs ws) l = (code (flatI ws l), (flatI ws l).length)
  | [], _ => rfl
  | i :: l, h => by
    simp only [concatCode]
    rw [getD_pairs ws (h i (by simp)), concatCode_eq ws l (fun j hj => h j (by simp [hj]))]
    simp [flatI, code_append, p8_eq]

theorem small_flatI {ws : List (List ℕ)} (hs : ∀ w ∈ ws, Small w) (l : List ℕ) :
    Small (flatI ws l) := by
  intro x hx
  simp only [flatI, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨i, -, rfl⟩, hx⟩ := hx
  rw [List.getD_eq_getElem?_getD] at hx
  cases h : ws[i]? with
  | none => simp [h] at hx
  | some w => simp [h] at hx; exact hs w (List.mem_of_getElem? h) x hx

/-- **Soundness of an ambiguity certificate.** -/
theorem checkAmb_sound {ws : List (List ℕ)} (hs : ∀ w ∈ ws, Small w) (hn : ws.Nodup)
    {l r : List ℕ} (h : checkAmb (pairs ws) l r = true) :
    ¬ IsUniquelyDecodable (ws.toFinset : Set (List ℕ)) := by
  match l, r, h with
  | i :: l, j :: r, h =>
    simp only [checkAmb, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Nat.beq_eq,
      List.all_eq_true, Nat.blt_eq, length_pairs] at h
    obtain ⟨⟨⟨hij, hl⟩, hr⟩, hc⟩ := h
    rw [concatCode_eq ws _ hl, concatCode_eq ws _ hr] at hc
    simp only at hc
    have hflat : flatI ws (i :: l) = flatI ws (j :: r) :=
      code_injective (small_flatI hs _) (small_flatI hs _) hc.2 hc.1
    intro hUD
    have hmem : ∀ m : List ℕ, (∀ a ∈ m, a < ws.length) →
        ∀ w ∈ m.map (fun a => ws.getD a []), w ∈ (ws.toFinset : Set (List ℕ)) := by
      intro m hm w hw
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
      simp only [Finset.mem_coe, List.mem_toFinset, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (hm a ha), Option.getD_some]
      exact List.getElem_mem _
    have := hUD _ _ (hmem _ hl) (hmem _ hr) hflat
    simp only [List.map_cons, List.cons.injEq] at this
    have hi := hl i (by simp)
    have hj := hr j (by simp)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some, Option.getD_some] at this
    have hij' : i ≠ j := fun e => by simp [e] at hij
    exact hij' ((List.Nodup.getElem_inj_iff hn).mp this.1)
  | [], _, h => simp [checkAmb] at h
  | _ :: _, [], h => simp [checkAmb] at h

/-- **Soundness of a certificate.** -/
theorem checkCert_sound {ws : List (List ℕ)} {k c : ℕ} (hk : k ≤ 8) (hsmall : ∀ w ∈ ws, Small w)
    (hocc : ∀ x < k, ∃ w ∈ ws, x ∈ w) (h : checkCert (pairs ws) k c = true) : Good ws := by
  unfold checkCert at h
  split at h
  · exact Or.inr (Or.inr (checkTree_sound hk hsmall hocc h))
  · exact Or.inr (Or.inr (checkTree_sound hk hsmall hocc h))
  · by_cases hn : ws.Nodup
    · exact Or.inr (Or.inl (checkAmb_sound hsmall hn h))
    · exact Or.inl hn
  · simp at h

end SmallestNoncompletable.Search
