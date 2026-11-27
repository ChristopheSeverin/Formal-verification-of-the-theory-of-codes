module

public import SmallestNoncompletable.SearchPrune

/-! # Soundness of the search

If `run P certs = true` for a valid profile `P`, then every two-counter restricted growth
string `q` of the right length gives a list of words satisfying `Good`. -/

@[expose] public section

namespace SmallestNoncompletable.Search

open ThreeWordCodes InformationTheory

/-! ## Products of earlier words -/

theorem isProduct_sound {D : List (List ℕ)} (hD : ∀ d ∈ D, Small d) (c : ℕ) :
    ∀ fuel l, isProduct (pairs D) c fuel l = true →
      ∃ xs : List (List ℕ), (∀ x ∈ xs, x ∈ D) ∧ code xs.flatten = c % 8 ^ l ∧
        xs.flatten.length = l
  | _, 0, _ => ⟨[], by simp, by simp [Nat.mod_one], by simp⟩
  | 0, _ + 1, h => by simp [isProduct] at h
  | fuel + 1, l + 1, h => by
    simp only [isProduct, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, pairs,
      List.mem_map] at h
    obtain ⟨_, ⟨e, he, rfl⟩, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    simp only at h1 h2 h3 h4
    rw [p8_eq, p8_eq] at h3
    obtain ⟨xs, hxs, hc, hl⟩ := isProduct_sound hD c fuel (l + 1 - e.length) h4
    refine ⟨e :: xs, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      exacts [he, hxs x hx]
    · simp only [List.flatten_cons, code_append, hl, hc]
      rw [← h3, ← Nat.mod_mod_of_dvd c (Nat.pow_dvd_pow 8 (Nat.sub_le (l + 1) e.length)),
        Nat.div_add_mod']
    · simp only [List.flatten_cons, List.length_append, hl]
      omega

/-! ## Completed words -/

theorem doneCount_spec : ∀ (lens : List ℕ) (i : ℕ), (∀ l ∈ lens, 1 ≤ l) →
    doneCount lens i ≠ 0 → doneCount lens i < lens.length ∧ i = (lens.take (doneCount lens i)).sum
  | [], _, _, h => by simp [doneCount] at h
  | [_], _, _, h => by simp [doneCount] at h
  | _ :: _ :: _, 0, _, h => by simp [doneCount] at h
  | l :: l' :: ls, i + 1, hl, h => by
    by_cases h1 : i + 1 = l
    · have : doneCount (l :: l' :: ls) (i + 1) = 1 := by simp [doneCount, Nat.beq_eq, h1]
      rw [this]
      simp [h1]
    · by_cases h2 : l < i + 1
      · have hrec := doneCount_spec (l' :: ls) (i + 1 - l)
          (fun l'' h => hl l'' (List.mem_cons_of_mem _ h))
        by_cases h3 : doneCount (l' :: ls) (i + 1 - l) = 0
        · have : doneCount (l :: l' :: ls) (i + 1) = 0 := by
            simp [doneCount, Nat.beq_eq, h1, Nat.blt_eq, h2, h3]
          exact absurd this h
        · have : doneCount (l :: l' :: ls) (i + 1) = doneCount (l' :: ls) (i + 1 - l) + 1 := by
            simp [doneCount, Nat.beq_eq, h1, Nat.blt_eq, h2, h3]
          rw [this]
          obtain ⟨hlt, hsum⟩ := hrec h3
          refine ⟨by simp at hlt ⊢; omega, ?_⟩
          rw [List.take_succ_cons, List.sum_cons, ← hsum]
          omega
      · have : doneCount (l :: l' :: ls) (i + 1) = 0 := by
          simp [doneCount, Nat.beq_eq, h1, Nat.blt_eq, h2]
        exact absurd this h

/-- **Soundness of the test on a completed word.** -/
theorem wordOK_sound {P : Prof} (hP : P.Valid) {q₀ q' : List ℕ} (hsm : Small q₀)
    (h : wordOK P q₀.length (code q₀) = false) :
    Good (wordsOf P (q₀ ++ q')) := by
  classical
  have hl1 : ∀ l ∈ P.lens, 1 ≤ l := fun l h => by have := hP.long l h; omega
  set n := doneCount P.lens q₀.length with hn
  by_cases hn0 : n = 0
  · simp [wordOK, ← hn, hn0] at h
  obtain ⟨hnt, hsum⟩ := doneCount_spec P.lens q₀.length hl1 hn0
  rw [← hn] at hnt hsum
  set l := P.lens.getD (n - 1) 0 with hl
  set pre := P.lens.take (n - 1) with hpre
  have htake : P.lens.take n = pre ++ [l] := by
    rw [hpre, hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact List.take_succ_eq_append_getElem (by omega)
  have hsumn : q₀.length = pre.sum + l := by rw [hsum, htake, List.sum_append]; simp
  -- split the prefix into the earlier words and the completed word
  set a := q₀.take pre.sum with ha
  set b := q₀.drop pre.sum with hb
  have hq₀ : q₀ = a ++ b := (List.take_append_drop _ _).symm
  have hblen : b.length = l := by simp [hb]; omega
  have halen : a.length = pre.sum := by simp [ha]; omega
  have hsa : Small a := hsm.of_sublist (List.take_sublist _ _)
  have hsb : Small b := hsm.of_sublist (List.drop_sublist _ _)
  have hcut : cut P.lens (q₀ ++ q') = cut pre a ++ [b] ++ cut (P.lens.drop n) q' := by
    rw [cut_append n P.lens q₀ q' hsum, htake, hq₀, cut_append (pre.length) (pre ++ [l]) a b
      (by rw [List.take_left' rfl]; exact halen)]
    rw [List.take_left' rfl, List.drop_left' rfl]
    simp [cut, ← hblen]
  have hwords : wordsOf P (q₀ ++ q') = (singlesW P.s ++ cut pre a) ++ b :: cut (P.lens.drop n) q' := by
    rw [wordsOf, hcut]; simp
  -- the data of the test
  have hdl : doneLen P q₀.length = l := rfl
  have hw : code q₀ % p8 l = code b := by rw [p8_eq, hq₀, ← hblen, code_append_mod hsb]
  have hearlier : earlierWords P q₀.length (code q₀) = pairs (singlesW P.s ++ cut pre a) := by
    show (List.range P.s).map (fun x => (x, 1)) ++
      (wordCodes (code q₀ / p8 l) pre pre.sum).zip pre = _
    rw [p8_eq, hq₀, ← hblen, code_append_div hsb, wordCodes_eq' pre a hsa halen, pairs_singles,
      pairs, pairs, pairs, List.map_append]
  have hbeq : Nat.beq (doneCount P.lens q₀.length) 0 = false := by
    rw [← hn]
    cases h : Nat.beq n 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hn0
  simp only [wordOK, hbeq, hdl, hearlier, hw, Bool.cond_false, Bool.and_eq_false_iff,
    Bool.not_eq_false'] at h
  set E := singlesW P.s ++ cut pre a with hE
  have hEsm : ∀ e ∈ E, Small e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [singlesW, List.mem_map, List.mem_range] at he
      obtain ⟨x, hx, rfl⟩ := he
      intro y hy; rw [List.mem_singleton.mp hy]; have := hP.small; simp [Prof.t] at this; omega
    · exact small_of_mem_cut hsa he
  rw [hwords]
  by_cases hnd : ((E ++ b :: cut (P.lens.drop n) q')).Nodup
  swap
  · exact Or.inl hnd
  have hbE : b ∉ E := by
    rw [List.nodup_append] at hnd
    exact fun hb' => hnd.2.2 b hb' b (List.mem_cons_self ..) rfl
  rcases h with h | h
  · exfalso
    simp only [List.any_eq_true, Bool.and_eq_true, Nat.beq_eq, pairs, List.mem_map] at h
    obtain ⟨_, ⟨e, he, rfl⟩, h1, h2⟩ := h
    simp only at h1 h2
    exact hbE (code_injective (hEsm e he) hsb (by rw [h2, hblen]) h1 ▸ he)
  · obtain ⟨xs, hxs, hc, hxl⟩ := isProduct_sound hEsm (code b) l l h
    rw [← hblen, Nat.mod_eq_of_lt (code_lt hsb)] at hc
    have hflat : xs.flatten = b :=
      code_injective (fun y hy => by
        obtain ⟨x, hx, hyx⟩ := List.mem_flatten.mp hy
        exact hEsm x (hxs x hx) y hyx) hsb (by rw [hxl, hblen]) hc
    refine Or.inr (Or.inl fun hUD => ?_)
    have := hUD [b] xs (by simp) (fun x hx => by simp [hxs x hx])
      (by rw [hflat]; simp)
    exact hbE (hxs b (by rw [← this]; simp))

/-! ## Pruning and leaves -/

theorem Inv.small {P : Prof} (hP : P.Valid) {q₀ : List ℕ} {u k S E : ℕ} (hinv : Inv P q₀ u k S E) :
    Small q₀ := by
  intro x hx
  have := hP.small
  rcases hinv.mem x hx with h | h
  · have := hinv.u_le; omega
  · have := hinv.k_le; omega

/-- **Soundness of the pruning.** -/
theorem prune_sound {P : Prof} (hP : P.Valid) {q₀ : List ℕ} {u k S E : ℕ}
    (hinv : Inv P q₀ u k S E) (h : prune P q₀.length u k S E = true) {q' : List ℕ}
    (hext : Ext P.s u k q') (hlen : (q₀ ++ q').length = P.m) : Good (wordsOf P (q₀ ++ q')) := by
  have hl1 : ∀ l ∈ P.lens, 1 ≤ l := fun l h => by have := hP.long l h; omega
  have hocc : ∀ x, P.s ≤ x → x < k → x ∈ q₀ ++ q' := fun x h1 h2 =>
    List.mem_append_left _ (hinv.usedA x h1 h2)
  simp only [prune, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨h1, h2⟩
  · exact good_of_many hP hlen h hocc
  · rw [remStarts_eq] at h
    obtain ⟨x, hx1, hx2, hx⟩ := exists_missed (q := q₀ ++ q') (List.prefix_append _ _) rfl
      hinv.S_eq h
    exact good_of_not_first hP hlen hx1 (hocc x hx1 (by have := hinv.s_le; omega)) hx
  · rw [remEnds_eq _ hl1] at h
    obtain ⟨x, hx1, hx2, hx⟩ := exists_missed (q := q₀ ++ q') (List.prefix_append _ _) rfl
      hinv.E_eq h
    exact good_of_not_last hP hlen hx1 (hocc x hx1 (by have := hinv.s_le; omega)) hx
  · apply good_of_isolated h1
    intro hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases hinv.mem _ hx with h | h <;> omega
    · rcases hext.letters hinv.s_le _ hx with h | h
      · simp only [List.length_append] at hlen
        omega
      · omega

/-- **Soundness of the leaf test.** -/
theorem leaf_sound {P : Prof} (hP : P.Valid) {q : List ℕ} {u k S E : ℕ} (hinv : Inv P q u k S E)
    (hlen : q.length = P.m) {certs r : List ℕ} (h : leaf P k (code q) certs = some r) :
    Good (wordsOf P q) := by
  have hsm := hinv.small hP
  have hs8 : P.s ≤ 8 := by have := hP.small; omega
  have hk8 : k ≤ 8 := by have := hinv.k_le; have := hP.small; simp [Prof.t] at *; omega
  obtain ⟨hwsm, -⟩ := wordsOf_facts hP hlen hsm hs8
  have hlongs : (wordCodes (code q) P.lens P.m).zip P.lens = pairs (cut P.lens q) :=
    wordCodes_eq' P.lens q hsm hlen
  have hcutok : WordsOK (cut P.lens q) :=
    ⟨fun w hw => small_of_mem_cut hsm hw, fun w hw h => by
      have := long_of_mem_cut hP.long hlen hw; simp [h] at this⟩
  have hlong : ∀ w ∈ cut P.lens q, 2 ≤ w.length := fun w hw => long_of_mem_cut hP.long hlen hw
  unfold leaf at h
  rw [hlongs] at h
  dsimp only at h
  by_cases hq : (dupB (pairs (cut P.lens q)) || prefixFreeB P.s (pairs (cut P.lens q)) ||
      suffixFreeB P.s (pairs (cut P.lens q))) = true
  · simp only [Bool.or_eq_true] at hq
    rcases hq with (hq | hq) | hq
    · refine Or.inl fun hnd => dupB_sound _ hcutok.small hq ?_
      exact (List.nodup_append.mp hnd).2.1
    · exact Or.inr (Or.inr (Or.inl (prefixFreeB_sound hcutok hlong hq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (suffixFreeB_sound hcutok hlong hq))))
  · rw [Bool.not_eq_true] at hq
    rw [hq, Bool.cond_false] at h
    match certs, h with
    | c :: cs, h =>
      have hc : checkCert (pairs (wordsOf P q)) k c = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rw [wordsOf, pairs, List.map_append, ← pairs, ← pairs, ← pairs_singles] at hc
        simp [hc] at h
      refine checkCert_sound hk8 hwsm ?_ hc
      intro x hx
      by_cases hxs : x < P.s
      · exact ⟨[x], mem_wordsOf.mpr (Or.inl ⟨x, hxs, rfl⟩), by simp⟩
      · obtain ⟨w, hw, hxw⟩ := exists_mem_cut hlen (hinv.usedA x (by omega) hx)
        exact ⟨w, mem_wordsOf.mpr (Or.inr hw), hxw⟩

/-! ## The search -/

theorem foldOpt_spec (f : ℕ → List ℕ → Option (List ℕ)) :
    ∀ (n a : ℕ) (cs r : List ℕ), foldOpt f a n cs = some r →
      ∀ j, a ≤ j → j < a + n → ∃ cs' r', f j cs' = some r'
  | 0, _, _, _, _, j, h1, h2 => by omega
  | n + 1, a, cs, r, h, j, h1, h2 => by
    change (match f a cs with
      | some cs' => foldOpt f (a + 1) n cs'
      | none => none) = some r at h
    cases hfa : f a cs with
    | none => rw [hfa] at h; simp at h
    | some cs' =>
      rw [hfa] at h
      by_cases hj : j = a
      · exact ⟨cs, cs', hj ▸ hfa⟩
      · exact foldOpt_spec f n (a + 1) cs' r h j (by omega) (by omega)

theorem dfs_zero (P : Prof) (i u k S E acc : ℕ) (certs : List ℕ) :
    dfs P 0 i u k S E acc certs =
      cond (prune P i u k S E || !wordOK P i acc) (some certs) (leaf P k acc certs) := rfl

theorem dfs_succ (P : Prof) (n i u k S E acc : ℕ) (certs : List ℕ) :
    dfs P (n + 1) i u k S E acc certs =
      cond (prune P i u k S E || !wordOK P i acc) (some certs) (
        match foldOpt (fun j cs => dfs P n (i + 1) (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
            (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
            (cond (isStart P.lens i) (Nat.lor S (Nat.shiftLeft 1 j)) S)
            (cond (isEnd P.lens i) (Nat.lor E (Nat.shiftLeft 1 j)) E) (8 * acc + j) cs)
            0 (minN (u + 1) P.s) certs with
        | some cs => foldOpt (fun j cs => dfs P n (i + 1) (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
            (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
            (cond (isStart P.lens i) (Nat.lor S (Nat.shiftLeft 1 j)) S)
            (cond (isEnd P.lens i) (Nat.lor E (Nat.shiftLeft 1 j)) E) (8 * acc + j) cs)
            P.s (k + 1 - P.s) cs
        | none => none) := rfl

/-- The invariant passes to a child. -/
theorem Inv.child {P : Prof} (hP : P.Valid) {q₀ : List ℕ} {u k S E : ℕ}
    (hinv : Inv P q₀ u k S E) (hk : k < P.s + P.t) {j : ℕ}
    (hj : (j < P.s ∧ j ≤ u) ∨ (P.s ≤ j ∧ j ≤ k)) :
    Inv P (q₀ ++ [j]) (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
      (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
      (cond (isStart P.lens q₀.length) (Nat.lor S (Nat.shiftLeft 1 j)) S)
      (cond (isEnd P.lens q₀.length) (Nat.lor E (Nat.shiftLeft 1 j)) E) := by
  have hl1 : ∀ l ∈ P.lens, 1 ≤ l := fun l h => by have := hP.long l h; omega
  have hpos : ∀ (pos : List ℕ) (b : Bool) (M x : ℕ),
      (b = true ↔ q₀.length ∈ pos) →
      (∀ x, bit M x = 1 ↔ ∃ p ∈ pos, q₀[p]? = some x) →
      (bit (cond b (Nat.lor M (Nat.shiftLeft 1 j)) M) x = 1 ↔
        ∃ p ∈ pos, (q₀ ++ [j])[p]? = some x) := by
    intro pos b M x hb hM
    have key : ∀ p, (q₀ ++ [j])[p]? = some x ↔
        (q₀[p]? = some x) ∨ (p = q₀.length ∧ j = x) := by
      intro p
      rcases Nat.lt_trichotomy p q₀.length with hp | hp | hp
      · rw [List.getElem?_append_left hp]; simp; omega
      · subst hp; simp
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
        simp; omega
    cases b
    · simp only [Bool.cond_false, hM]
      have hnot : q₀.length ∉ pos := fun h => by simpa using hb.mpr h
      constructor
      · rintro ⟨p, hp, hpx⟩; exact ⟨p, hp, (key p).mpr (Or.inl hpx)⟩
      · rintro ⟨p, hp, hpx⟩
        rcases (key p).mp hpx with h | ⟨rfl, -⟩
        · exact ⟨p, hp, h⟩
        · exact absurd hp hnot
    · simp only [Bool.cond_true, bit_lor_shift, hM]
      have hin : q₀.length ∈ pos := hb.mp rfl
      constructor
      · rintro (⟨p, hp, hpx⟩ | rfl)
        · exact ⟨p, hp, (key p).mpr (Or.inl hpx)⟩
        · exact ⟨q₀.length, hin, by simp⟩
      · rintro ⟨p, hp, hpx⟩
        rcases (key p).mp hpx with h | ⟨rfl, rfl⟩
        · exact Or.inl ⟨p, hp, h⟩
        · exact Or.inr rfl
  have hu := hinv.u_le
  have hsk := hinv.s_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Nat.blt_eq, h1, maxN_eq]; omega
    · simp [Nat.blt_eq, show ¬ j < P.s by omega]; omega
  · cases h : Nat.ble P.s j <;> simp [maxN_eq] <;> omega
  · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Nat.ble_eq, show ¬ P.s ≤ j by omega]; exact hinv.k_le
    · simp [Nat.ble_eq, h1, maxN_eq]; omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases hinv.mem x hx with h | h
      · left
        cases h' : Nat.blt j P.s <;> simp [maxN_eq] <;> omega
      · right
        cases h' : Nat.ble P.s j <;> simp [maxN_eq] <;> omega
    · rw [List.mem_singleton.mp hx]
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [Nat.blt_eq, h1, maxN_eq]
      · right; simp [Nat.ble_eq, h1, maxN_eq]
  · intro x h1 h2
    by_cases hxk : x < k
    · exact List.mem_append_left _ (hinv.usedA x h1 hxk)
    · rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
      · simp [Nat.ble_eq, show ¬ P.s ≤ j by omega] at h2; omega
      · simp [Nat.ble_eq, hj1, maxN_eq] at h2
        have : x = j := by omega
        rw [this]; simp
  · intro x
    exact hpos _ _ _ x (isStart_iff P.lens q₀.length) hinv.S_eq
  · intro x
    exact hpos _ _ _ x (isEnd_iff P.lens hl1 q₀.length) hinv.E_eq

/-- **Soundness of the search.** -/
theorem dfs_sound {P : Prof} (hP : P.Valid) : ∀ (fuel : ℕ) (q₀ : List ℕ) (u k S E : ℕ)
    (certs r : List ℕ), Inv P q₀ u k S E → q₀.length + fuel = P.m →
    dfs P fuel q₀.length u k S E (code q₀) certs = some r →
    ∀ q', Ext P.s u k q' → q'.length = fuel → Good (wordsOf P (q₀ ++ q'))
  | fuel, q₀, u, k, S, E, certs, r, hinv, hlen, h, q', hext, hq' => by
    have hlen' : (q₀ ++ q').length = P.m := by simp; omega
    by_cases hpr : prune P q₀.length u k S E = true
    · exact prune_sound hP hinv hpr hext hlen'
    by_cases hw : wordOK P q₀.length (code q₀) = false
    · exact wordOK_sound hP (hinv.small hP) hw
    have hc : (prune P q₀.length u k S E || !wordOK P q₀.length (code q₀)) = false := by
      simp only [Bool.not_eq_true] at hpr hw
      simp [hpr, hw]
    match fuel, q', hext, hq', h with
    | 0, [], _, _, h =>
      rw [dfs_zero, hc, Bool.cond_false] at h
      simpa using leaf_sound hP hinv (by simpa using hlen) h
    | n + 1, j :: q'', hext, hq', h =>
      rw [dfs_succ, hc, Bool.cond_false] at h
      have hnot : ¬ (P.t ≤ k - P.s) := by
        intro ht
        apply hpr
        simp [prune, Nat.ble_eq, ht]
      have hk : k < P.s + P.t := by have := hinv.s_le; omega
      -- the child for `j`
      have hchild : ∃ cs r', dfs P n (q₀.length + 1)
          (cond (Nat.blt j P.s) (maxN u (j + 1)) u) (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
          (cond (isStart P.lens q₀.length) (Nat.lor S (Nat.shiftLeft 1 j)) S)
          (cond (isEnd P.lens q₀.length) (Nat.lor E (Nat.shiftLeft 1 j)) E)
          (8 * code q₀ + j) cs = some r' := by
        cases h1 : foldOpt (fun j cs => dfs P n (q₀.length + 1)
            (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
            (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
            (cond (isStart P.lens q₀.length) (Nat.lor S (Nat.shiftLeft 1 j)) S)
            (cond (isEnd P.lens q₀.length) (Nat.lor E (Nat.shiftLeft 1 j)) E)
            (8 * code q₀ + j) cs) 0 (minN (u + 1) P.s) certs with
        | none => rw [h1] at h; simp at h
        | some cs =>
          rw [h1] at h
          rcases hext with ⟨hj1, hj2, -⟩ | ⟨hj1, hj2, -⟩
          · exact foldOpt_spec _ _ _ _ _ h1 j (by omega) (by rw [minN_eq]; omega)
          · exact foldOpt_spec _ _ _ _ _ h j hj1 (by omega)
      obtain ⟨cs, r', hr'⟩ := hchild
      have hj : (j < P.s ∧ j ≤ u) ∨ (P.s ≤ j ∧ j ≤ k) := by
        rcases hext with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
        exacts [Or.inl ⟨h1, h2⟩, Or.inr ⟨h1, h2⟩]
      have hinv' := hinv.child hP hk hj
      have hext' : Ext P.s (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
          (cond (Nat.ble P.s j) (maxN k (j + 1)) k) q'' := by
        rcases hext with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · simpa [Nat.blt_eq, h1, Nat.ble_eq, show ¬ P.s ≤ j by omega, maxN_eq] using h3
        · simpa [Nat.blt_eq, show ¬ j < P.s by omega, Nat.ble_eq, h1, maxN_eq] using h3
      have := dfs_sound hP n (q₀ ++ [j]) _ _ _ _ cs r' hinv' (by simp at hq' ⊢; omega)
        (by rw [List.length_append, List.length_singleton, code_concat]; exact hr')
        q'' hext' (by simpa using hq')
      simpa using this

/-- The initial invariant. -/
theorem Inv.init (P : Prof) : Inv P [] 0 P.s 0 0 := by
  refine ⟨Nat.zero_le _, le_rfl, Nat.le_add_right _ _, by simp, fun x h1 h2 => by omega, ?_, ?_⟩
  all_goals intro x; simp [bit_eq]

/-- **Soundness of a run.** -/
theorem run_sound {P : Prof} (hP : P.Valid) {certs : List ℕ} (h : run P certs = true) :
    ∀ q, Ext P.s 0 P.s q → q.length = P.m → Good (wordsOf P q) := by
  intro q hext hq
  unfold run at h
  split at h
  · rename_i r hr
    have := dfs_sound hP P.m [] 0 P.s 0 0 certs [] (Inv.init P) (by simp) hr q hext hq
    simpa using this
  · simp at h

end SmallestNoncompletable.Search
