module

public import ThreeWordCodes.Powers

/-! # Removing initial powers inside a language

If prefixing a nonempty block preserves a language, each member starts with
a unique power of that block whose remainder admits no further such removal
inside the language. We apply this twice, first to all words and then to the
words avoiding a prescribed prefix. -/

@[expose] public section
namespace NonfreeBinaryFactor

open ThreeWordCodes (Word wordPow wordPow_zero wordPow_succ')

variable {A : Type*}

/-- A word has no prefix `p`, and any initial `c` is followed by `p`. -/
def Reduced (p : Word A) (c : A) (w : Word A) : Prop :=
  ¬ p <+: w ∧ ([c] <+: w → c :: p <+: w)

/-- Reinsert the two initial powers. -/
def prepend (p : Word A) (c : A) (i j : ℕ) (v : Word A) : Word A :=
  wordPow p i ++ (wordPow [c] j ++ v)

private def Remainder (D : Word A → Prop) (p v : Word A) : Prop :=
  D v ∧ ¬ ∃ t, p ++ t = v ∧ D t

private theorem power_mem {D : Word A → Prop} {p : Word A}
    (step : ∀ t, D t → D (p ++ t)) {v : Word A} (hv : D v) (n : ℕ) :
    D (wordPow p n ++ v) := by
  induction n with
  | zero => exact hv
  | succ n ih => simpa only [wordPow_succ', List.append_assoc] using step _ ih

private theorem exists_remainder {D : Word A → Prop} {p : Word A} (hp : p ≠ [])
    (w : Word A) (hw : D w) :
    ∃ n v, Remainder D p v ∧ wordPow p n ++ v = w := by
  by_cases cut : ∃ t, p ++ t = w ∧ D t
  · obtain ⟨t, ht, hD⟩ := cut
    have shorter : t.length < w.length := by
      rw [← ht, List.length_append]
      have := List.length_pos_iff.mpr hp
      omega
    obtain ⟨n, v, hv, hn⟩ := exists_remainder hp t hD
    exact ⟨n+1, v, hv, by rw [wordPow_succ', List.append_assoc, hn, ht]⟩
  · exact ⟨0, w, ⟨hw, cut⟩, rfl⟩
termination_by w.length

private theorem unique_remainder {D : Word A → Prop} {p u v : Word A}
    (step : ∀ t, D t → D (p ++ t)) (hu : Remainder D p u) (hv : Remainder D p v)
    {i j : ℕ} (e : wordPow p i ++ u = wordPow p j ++ v) : i = j ∧ u = v := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨rfl, e⟩
    | succ j =>
      rw [wordPow_succ', List.append_assoc] at e
      exact (hu.2 ⟨_, e.symm, power_mem step hv.1 j⟩).elim
  | succ i ih =>
    cases j with
    | zero =>
      rw [wordPow_succ', List.append_assoc] at e
      exact (hv.2 ⟨_, e, power_mem step hu.1 i⟩).elim
    | succ j =>
      simp only [wordPow_succ', List.append_assoc, List.append_cancel_left_eq] at e
      obtain ⟨h, huv⟩ := ih e
      exact ⟨congrArg Nat.succ h, huv⟩

private theorem unrestricted {p w : Word A} :
    Remainder (fun _ => True) p w ↔ ¬ p <+: w := by
  simp [Remainder, List.prefix_iff_exists_append_eq]

private theorem reduced_iff {p w : Word A} {c : A} :
    Reduced p c w ↔ Remainder (fun t => ¬ p <+: t) [c] w := by
  classical
  cases w with
  | nil => simp [Reduced, Remainder]
  | cons d t =>
    by_cases h : c = d
    · subst d
      simp [Reduced, Remainder]
    · simp [Reduced, Remainder, h]

private theorem avoids_after_cons {h c : A} (hc : h ≠ c) (p v : Word A) :
    ¬ h :: p <+: [c] ++ v := by simp [hc]

theorem exists_prepend {h c : A} (p w : Word A) :
    ∃ i j v, Reduced (h :: p) c v ∧ prepend (h :: p) c i j v = w := by
  obtain ⟨i, u, hu, hi⟩ := exists_remainder (D := fun _ => True)
    (p := h :: p) (by simp) w trivial
  obtain ⟨j, v, hv, hj⟩ := exists_remainder (D := fun t => ¬ h :: p <+: t)
    (p := [c]) (by simp) u (unrestricted.mp hu)
  exact ⟨i, j, v, reduced_iff.mpr hv, by rw [prepend, hj, hi]⟩

theorem prepend_unique {h c : A} (hc : h ≠ c) {p u v : Word A} {i j i' j' : ℕ}
    (hu : Reduced (h :: p) c u) (hv : Reduced (h :: p) c v)
    (e : prepend (h :: p) c i j u = prepend (h :: p) c i' j' v) :
    i = i' ∧ j = j' ∧ u = v := by
  let D := fun t => ¬ h :: p <+: t
  have step : ∀ t, D t → D ([c] ++ t) := fun t _ => avoids_after_cons hc p t
  obtain ⟨hi, he⟩ := unique_remainder (D := fun _ => True)
    (fun _ _ => trivial) (unrestricted.mpr (power_mem step hu.1 j))
    (unrestricted.mpr (power_mem step hv.1 j')) e
  exact ⟨hi, unique_remainder step (reduced_iff.mp hu) (reduced_iff.mp hv) he⟩

end NonfreeBinaryFactor
