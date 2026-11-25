module

public import ThreeWordCodes.GapComparison

/-! # Uniform internal gaps and bounded margins of an ambiguous triple (Lemma 2) -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def atGap (g : List ℕ) (k : ℕ) : ℕ := (g[k]?).getD 0

private theorem copies_info {g e : List ℕ} {j : ℕ} (rep : Copies g j e) :
    (g.length+1) ∣ (e.length+1) ∧
    ∀ k, k < e.length →
      (k % (g.length+1) = g.length → j ≤ atGap e k) ∧
      (k % (g.length+1) ≠ g.length → atGap e k = atGap g (k % (g.length+1))) := by
  induction rep with
  | one =>
    refine ⟨dvd_rfl,?_⟩
    intro k hk
    simp [Nat.mod_eq_of_lt (by omega : k < g.length+1), Nat.ne_of_lt hk]
  | @more e rep h ih =>
    obtain ⟨div,rest⟩ := ih
    refine ⟨?_,?_⟩
    · have eqn : (g ++ (j+h)::e).length+1 = (g.length+1)+(e.length+1) := by simp; omega
      rw [eqn]
      exact dvd_add dvd_rfl div
    · intro k hk
      by_cases lt : k < g.length
      · simp [atGap, List.getElem?_append_left lt, Nat.mod_eq_of_lt (by omega : k < g.length+1),Nat.ne_of_lt lt]
      by_cases eqn : k = g.length
      · subst k
        simp [atGap,Nat.mod_eq_of_lt (Nat.lt_succ_self _)]
      · let t := k - (g.length+1)
        have len : k = (g.length+1)+t := by dsimp [t]; omega
        have small : t < e.length := by simp at hk; omega
        have hk' : atGap (g ++ (j+h)::e) k = atGap e t := by
          simp only [atGap, List.getElem?_append_right (by omega : g.length ≤ k)]
          rw [show k-g.length = t+1 by omega]
          rfl
        rw [hk', len, Nat.add_mod_left]
        exact rest t small

private theorem successor_mod {k m : ℕ} (hm : 0 < m) (hn : (k+1)%m ≠ 0) :
    k%m + 1 = (k+1)%m := by
  have small := Nat.mod_lt k hm
  have b : k%m+1 ≠ m := by
    intro e
    apply hn
    rw [← Nat.mod_add_mod k m 1, e, Nat.mod_self]
  exact (Nat.mod_eq_of_lt (show k%m+1 < m by omega)).symm.trans (Nat.mod_add_mod k m 1)

private theorem read_forward {g j e q} (read : ∃ s, mixed 0 e q <+: spell (stripped g j) s)
    (long : g.length < e.length) (nr : (e.length+1) % (g.length+1) ≠ 0) :
    (∀ k, k < e.length → (k+1) % (g.length+1) ≠ 0 →
      atGap e k = atGap g (((k+1)%(g.length+1))-1)) ∧
    j ≤ atGap e g.length ∧ q ≤ atGap g (((e.length+1)%(g.length+1))-1) := by
  obtain ⟨full,last,rep,_,pr,margin⟩ := gap_list_of_reading read
  obtain ⟨div,lookup⟩ := copies_info rep
  have fits := pr.length_le
  have strict : e.length < full.length := by
    have ne : e.length ≠ full.length := by
      intro eqn
      exact nr (eqn ▸ Nat.mod_eq_zero_of_dvd div)
    omega
  have prefixRead (k : ℕ) (hk : k < e.length) : atGap full k = atGap e k := by
    obtain ⟨r,hr⟩ := pr
    simp [← hr,atGap,List.getElem?_append_left hk]
  have key (k : ℕ) (hk : k < full.length) (mod : (k+1)%(g.length+1) ≠ 0) :
      atGap full k = atGap g (((k+1)%(g.length+1))-1) := by
    have next : k%(g.length+1) + 1 = (k+1)%(g.length+1) := successor_mod (by omega) mod
    have lt : (k+1)%(g.length+1) < g.length+1 := Nat.mod_lt _ (Nat.zero_lt_succ _)
    rw [←next,Nat.add_sub_cancel]
    apply (lookup k hk).2
    intro eqn
    rw [←next,eqn] at lt
    exact (Nat.lt_irrefl _) lt
  refine ⟨fun k hk mod => (prefixRead k hk).symm.trans (key k (hk.trans_le fits) mod), ?_, ?_⟩
  · have bound := (lookup g.length (long.trans strict)).1 (Nat.mod_eq_of_lt (Nat.lt_succ_self _))
    rwa [prefixRead _ long] at bound
  · have same : (full[e.length]?).getD last = atGap full e.length := by
      simp [atGap,List.getElem?_eq_getElem strict]
    exact (margin.trans_eq same).trans_eq (key _ strict nr)

/-- In the canonical run notation the two mixed words have |g|+1 and |e|+1
occurrences of b. The gaps and all four margins are quantified independently. -/
theorem uniform_gaps_of_readings {i g j h e q}
    (forward : ∃ s, mixed 0 e q <+: spell (stripped g j) s)
    (backward : ∃ s, mixed 0 e.reverse h <+: spell (stripped g.reverse i) s)
    (two : 2 ≤ g.length+1) (long : g.length < e.length)
    (cop : (e.length+1).Coprime (g.length+1)) :
    ∃ c : ℕ, (∀ z ∈ g, z = c) ∧ (∀ z ∈ e, z = c) ∧ i ≤ c ∧ j ≤ c ∧ h ≤ c ∧ q ≤ c := by
  let m := g.length+1
  let n := e.length+1
  have : NeZero m := ⟨by dsimp [m]; omega⟩
  have nr : n%m ≠ 0 := by
    intro eqn
    have dv := Nat.dvd_of_mod_eq_zero eqn
    have one : m = 1 := cop.symm.eq_one_of_dvd dv
    dsimp [m] at one
    omega
  obtain ⟨fwd,bj,bq⟩ := read_forward forward long nr
  have nr' : (e.reverse.length+1)%(g.reverse.length+1) ≠ 0 := by simpa only [List.length_reverse] using nr
  obtain ⟨bwd,bi,bh⟩ := read_forward backward (by simpa) nr'
  simp only [List.length_reverse] at bwd bi bh
  let G (x : ZMod m) := atGap g (x.val-1)
  let E (k : ℕ) := atGap e (k-1)
  have lgn : m < n := by dsimp [m,n]; omega
  have mod_nonzero (k : ℕ) (hz : (k : ZMod m) ≠ 0) : k%m ≠ 0 := by
    intro h
    apply hz
    rw [←ZMod.natCast_zmod_val (k : ZMod m), ZMod.val_natCast, h, Nat.cast_zero]
  obtain ⟨c,hg,he⟩ := gaps_of_alignments (m:=m) (n:=n) two lgn cop G E (by
    intro k pos small nz
    have bound : k-1 < e.length := by dsimp [n] at small; omega
    have hk : k-1+1 = k := by omega
    simpa only [E,G,ZMod.val_natCast, hk] using fwd (k-1) bound (hk ▸ mod_nonzero k nz)) (by
    intro k pos small nz
    let z := (k : ZMod m) - n
    have other : ((n-k : ℕ) : ZMod m) = -z := by
      rw [Nat.cast_sub small.le]
      simp [z]
    have nonzero : ((n-k : ℕ) : ZMod m) ≠ 0 := by rw [other, neg_ne_zero]; exact nz
    have id₁ : n-k-1+1 = n-k := by omega
    have bound : n-k-1 < e.length := by dsimp [n] at *; omega
    have line := bwd (n-k-1) (by simpa only [List.length_reverse] using bound)
      (by rw [id₁]; exact mod_nonzero _ nonzero)
    rw [id₁] at line
    have res : (n-k)%m = m-z.val := by
      rw [← ZMod.val_natCast, other, ZMod.neg_val, ite_eq_right nz]
    change atGap e.reverse (n-k-1) = atGap g.reverse (((n-k)%m)-1) at line
    rw [res] at line
    have zpos : 0 < z.val := by
      by_contra! hz
      apply nz
      change z = 0
      rw [← ZMod.natCast_zmod_val z, show z.val = 0 by omega, Nat.cast_zero]
    have zlt := z.val_lt
    have size₁ : (n-k-1)+(k-1)+1 = e.length := by dsimp [n] at *; omega
    have size₂ : (m-z.val-1)+(z.val-1)+1 = g.length := by dsimp [m] at *; omega
    simpa only [E,G,atGap,List.getElem?_reverse' size₁,List.getElem?_reverse' size₂] using line)
  have eg (idx : ℕ) (small : idx < g.length) : atGap g idx = c := by
    have bound : idx+1 < m := by dsimp [m]; omega
    have zero : ((idx+1 : ℕ) : ZMod m) ≠ 0 := by
      intro z
      have := congrArg ZMod.val z
      rw [ZMod.val_natCast_of_lt bound, ZMod.val_zero] at this
      omega
    simpa only [G,ZMod.val_natCast_of_lt bound,Nat.add_sub_cancel] using hg ((idx+1 : ℕ) : ZMod m) zero
  have ee (idx : ℕ) (small : idx < e.length) : atGap e idx = c := by
    simpa [E] using he (idx+1) (by omega) (by dsimp [n]; omega)
  have all (v : List ℕ) (hv : ∀ k, k < v.length → atGap v k = c) : ∀ z ∈ v, z = c := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hz
    simpa [atGap,List.getElem?_eq_getElem hk] using hv k hk
  have rem := Nat.mod_lt n (show 0 < m by dsimp [m]; omega)
  have remLt : n%m-1 < g.length := by dsimp [m] at *; omega
  have readReverse (v : List ℕ) (k : ℕ) (hk : k < v.length) :
      atGap v.reverse k = atGap v (v.length-1-k) := by simp [atGap,List.getElem?_reverse hk]
  change h ≤ atGap g.reverse (n%m-1) at bh
  change q ≤ atGap g (n%m-1) at bq
  rw [readReverse _ _ long, ee _ (by omega)] at bi
  rw [ee _ long] at bj
  rw [readReverse _ _ remLt, eg _ (by omega)] at bh
  rw [eg _ remLt] at bq
  exact ⟨c,all g eg,all e ee,bi,bj,bh,bq⟩

theorem uniform_gaps_of_no_completion {i g j h e q} (bad : ¬ Completable (layout i g j h e q))
    (two : 2 ≤ g.length+1) (long : g.length < e.length) (cop : (e.length+1).Coprime (g.length+1)) :
    ∃ c : ℕ, (∀ z ∈ g, z = c) ∧ (∀ z ∈ e, z = c) ∧ i ≤ c ∧ j ≤ c ∧ h ≤ c ∧ q ≤ c := by
  obtain ⟨f,r⟩ := directed_comparisons bad
  exact uniform_gaps_of_readings f r two long cop

/-- The ambiguity hypothesis of Lemma 2 implies the stronger theorem's hypothesis. -/
theorem uniform_gaps_of_ambiguity {i g j h e q} (bad : ¬ NamedCode (layout i g j h e q))
    (two : 2 ≤ g.length+1) (long : g.length < e.length) (cop : (e.length+1).Coprime (g.length+1)) :
    ∃ c : ℕ, (∀ z ∈ g, z = c) ∧ (∀ z ∈ e, z = c) ∧ i ≤ c ∧ j ≤ c ∧ h ≤ c ∧ q ≤ c :=
  uniform_gaps_of_no_completion (fun h => bad h.1) two long cop

/-- The two mixed names can occur in either order. -/
theorem uniform_gaps_of_distinct_counts {i g j h e q}
    (bad : ¬ NamedCode (layout i g j h e q)) (pg : 0 < g.length) (pe : 0 < e.length)
    (ne : g.length ≠ e.length) (cop : (e.length+1).Coprime (g.length+1)) :
    ∃ c : ℕ, (∀ z ∈ g, z = c) ∧ (∀ z ∈ e, z = c) ∧ i ≤ c ∧ j ≤ c ∧ h ≤ c ∧ q ≤ c := by
  by_cases lt : g.length < e.length
  · exact uniform_gaps_of_ambiguity bad (by omega) lt cop
  · obtain ⟨c,he,hg,bh,bq,bi,bj⟩ := uniform_gaps_of_ambiguity (swapped_ambiguity bad)
      (by omega) (by omega) cop.symm
    exact ⟨c,hg,he,bi,bj,bh,bq⟩

/-- The same conclusion stated directly for arbitrary binary words with actual marker counts. -/
theorem uniform_gaps_of_words (x y : Word Bool)
    (bad : ¬ NamedCode (addToken (pair [a] x) y))
    (two : 2 ≤ x.count b) (long : x.count b < y.count b) (cop : (y.count b).Coprime (x.count b)) :
    ∃ i j h q c : ℕ, ∃ g e : List ℕ, x = mixed i g j ∧ y = mixed h e q ∧
      (∀ z ∈ g, z = c) ∧ (∀ z ∈ e, z = c) ∧ i ≤ c ∧ j ≤ c ∧ h ≤ c ∧ q ≤ c := by
  obtain ⟨i,g,j,rfl⟩ := mixed_of_contains_marker (w := x) (List.count_pos_iff.mp (by omega))
  obtain ⟨h,e,q,rfl⟩ := mixed_of_contains_marker (w := y) (List.count_pos_iff.mp (by omega))
  simp only [mixed_count] at two long cop
  obtain ⟨c,gu,gv,bi,bj,bh,bq⟩ := uniform_gaps_of_ambiguity bad two (by omega) cop
  exact ⟨i,j,h,q,c,g,e,rfl,rfl,gu,gv,bi,bj,bh,bq⟩

end ThreeWordCodes.BinaryGaps
