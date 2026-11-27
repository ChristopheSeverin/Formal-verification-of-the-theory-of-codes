module

public import SmallestNoncompletable.Residual
public import SmallestNoncompletable.Reductions
public import Mathlib.Data.Set.Finite.List

/-! # Proposition 5: codes with words of length at most three

With `D = D(C)`, the letters split into `A ∩ C`, `V = A ∩ D` and `U = A \ (C ∪ D)`. Put
`H = UA ∪ AV`, `P₂ = H \ (C ∪ D)`, `S₂ = H ∩ D`,
`P₃ = {xyz : xy ∈ P₂, x ∉ U, z ∈ U, yz ∉ D}`, `S₃ = {xyz : yz ∈ S₂, z ∉ V, x ∈ V, xy ∈ D}`,
`P = {ε} ∪ U ∪ P₂ ∪ P₃` and `S = {ε} ∪ V ∪ S₂ ∪ S₃`. Then `F = 1 + P(χ_A - 1)S` has nonnegative
coefficients and contains `C` in its support. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory WordSeries

variable {A : Type*}

section Sets

variable (C : Set (Word A))

def InU (x : A) : Prop := [x] ∉ C ∧ ¬ Res C [x]
def InV (x : A) : Prop := Res C [x]
def InH (x y : A) : Prop := InU C x ∨ InV C y
def InP2 (x y : A) : Prop := InH C x y ∧ [x, y] ∉ C ∧ ¬ Res C [x, y]
def InS2 (x y : A) : Prop := InH C x y ∧ Res C [x, y]
def InP3 (x y z : A) : Prop := InP2 C x y ∧ ¬ InU C x ∧ InU C z ∧ ¬ Res C [y, z]
def InS3 (x y z : A) : Prop := InS2 C y z ∧ ¬ InV C z ∧ InV C x ∧ Res C [x, y]

open Classical in
/-- The left factor. -/
noncomputable def pS : Series A
  | [] => 1
  | [x] => if InU C x then 1 else 0
  | [x, y] => if InP2 C x y then 1 else 0
  | [x, y, z] => if InP3 C x y z then 1 else 0
  | _ => 0

open Classical in
/-- The right factor. -/
noncomputable def qS : Series A
  | [] => 1
  | [x] => if InV C x then 1 else 0
  | [x, y] => if InS2 C x y then 1 else 0
  | [x, y, z] => if InS3 C x y z then 1 else 0
  | _ => 0

theorem pS_long : ∀ w : Word A, 4 ≤ w.length → pS C w = 0
  | _ :: _ :: _ :: _ :: _, _ => rfl
  | [], h | [_], h | [_, _], h | [_, _, _], h => by simp at h

theorem qS_long : ∀ w : Word A, 4 ≤ w.length → qS C w = 0
  | _ :: _ :: _ :: _ :: _, _ => rfl
  | [], h | [_], h | [_, _], h | [_, _, _], h => by simp at h

end Sets

/-! ## Convolutions on short words -/

theorem conv_letters (f : Series A) (u : Word A) (x : A) : (f ⋆ letters) (u ++ [x]) = f u := by
  rw [conv_eq_sum, Finset.sum_eq_single u.length]
  · simp [letters, epsilon]
  · intro i hi hne
    simp only [Finset.mem_range, List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : ((u ++ [x]).drop i).length ≥ 2 := by simp; omega
      obtain ⟨a, b, t, ht⟩ : ∃ a b t, (u ++ [x]).drop i = a :: b :: t := by
        rcases hd : (u ++ [x]).drop i with _ | ⟨a, _ | ⟨b, t⟩⟩
        · rw [hd] at this; simp at this
        · rw [hd] at this; simp at this
        · exact ⟨a, b, t, rfl⟩
      rw [ht]; simp [letters, epsilon]
    · have : i = u.length + 1 := by omega
      subst this
      simp [letters]
  · intro h; simp at h

theorem letters_nil (f : Series A) : (f ⋆ letters) [] = 0 := by simp [letters]

theorem conv_letters' (f : Series A) {u : Word A} (hu : u ≠ []) :
    (f ⋆ letters) u = f u.dropLast := by
  conv_lhs => rw [← List.dropLast_append_getLast hu]
  exact conv_letters f _ _

section Coefficients

variable (C : Set (Word A))

/-- From length seven on, no cut leaves at most three letters on both sides. -/
theorem lhs_long (w : Word A) (hw : 7 ≤ w.length) : (pS C ⋆ qS C) w = 0 := by
  rw [conv_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : i ≤ 3
  · rw [qS_long C _ (by simp; omega), mul_zero]
  · rw [pS_long C _ (by simp; omega), zero_mul]

open Classical in
/-- The coefficients of the words of length at least four are nonnegative. -/
theorem coeff_long_words (w : Word A) (hw : 4 ≤ w.length) :
    (pS C ⋆ qS C) w ≤ WordSeries.epsilon w + ((pS C ⋆ letters) ⋆ qS C) w := by
  by_cases h7 : 7 ≤ w.length
  · rw [lhs_long C w h7]; exact Nat.zero_le _
  rw [conv_eq_sum (pS C ⋆ letters) (qS C), conv_eq_sum (pS C) (qS C)]
  match w, hw, h7 with
  | [x₁, x₂, x₃, x₄], _, _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, mul_zero, one_mul, mul_one, add_zero]
    -- constraints
    have hP3 : InP3 C x₁ x₂ x₃ → InP2 C x₁ x₂ := fun h => h.1
    have hS3 : InS3 C x₂ x₃ x₄ → InS2 C x₃ x₄ := fun h => h.1
    have hgap : ¬ InU C x₁ → InP2 C x₁ x₂ → ¬ InV C x₄ → InS2 C x₃ x₄ →
        (InP3 C x₁ x₂ x₃ ↔ ¬ InS3 C x₂ x₃ x₄) := by
      intro hu hp hv hs
      have hV2 : InV C x₂ := hp.1.resolve_left hu
      have hU3 : InU C x₃ := hs.1.resolve_right hv
      constructor
      · rintro ⟨-, -, -, hr⟩ ⟨-, -, -, hr'⟩; exact hr hr'
      · intro h
        refine ⟨hp, hu, hU3, fun hr => h ⟨hs, hv, hV2, hr⟩⟩
    split_ifs <;> simp_all
  | [x₁, x₂, x₃, x₄, x₅], _, _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, mul_zero, zero_mul, mul_one, add_zero]
    have hP3 : InP3 C x₁ x₂ x₃ → InP2 C x₁ x₂ := fun h => h.1
    have hS3 : InS3 C x₃ x₄ x₅ → InS2 C x₄ x₅ := fun h => h.1
    have hmid : ¬ (InP3 C x₁ x₂ x₃ ∧ InS3 C x₃ x₄ x₅) := fun ⟨h, h'⟩ => h.2.2.1.2 h'.2.2.1
    split_ifs <;> simp_all
  | [x₁, x₂, x₃, x₄, x₅, x₆], _, _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, mul_zero, zero_mul, mul_one, add_zero]
    have hP3 : InP3 C x₁ x₂ x₃ → InP2 C x₁ x₂ := fun h => h.1
    have hS3 : InS3 C x₄ x₅ x₆ → InS2 C x₅ x₆ := fun h => h.1
    split_ifs <;> simp_all
  | [], h, _ | [_], h, _ | [_, _], h, _ | [_, _, _], h, _ => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, h7 => simp at h7

open Classical in
/-- The coefficients of the words of length at most three, with one more on the codewords. -/
theorem coeff_short (hC : IsUniquelyDecodable C) (w : Word A) (hw : w.length ≤ 3) :
    (pS C ⋆ qS C) w + (if w ∈ C then 1 else 0) ≤
      WordSeries.epsilon w + ((pS C ⋆ letters) ⋆ qS C) w := by
  rw [conv_eq_sum (pS C ⋆ letters) (qS C), conv_eq_sum (pS C) (qS C)]
  match w, hw with
  | [], _ =>
    have : ([] : Word A) ∉ C := hC.epsilon_notMem
    simp [this, pS, qS, WordSeries.epsilon]
  | [x], _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, zero_mul, one_mul, mul_one,
      add_zero]
    have h1 : InU C x → ¬ InV C x ∧ [x] ∉ C := fun h => ⟨h.2, h.1⟩
    have h2 : InV C x → [x] ∉ C := fun h => Res.not_mem hC h
    split_ifs <;> simp_all
  | [x, y], _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, zero_mul, one_mul, mul_one,
      add_zero]
    have h1 : InS2 C x y → (InU C x ∨ InV C y) ∧ ¬ InP2 C x y ∧ [x, y] ∉ C :=
      fun h => ⟨h.1, fun h' => h'.2.2 h.2, Res.not_mem hC h.2⟩
    have h2 : InP2 C x y → (InU C x ∨ InV C y) ∧ [x, y] ∉ C := fun h => ⟨h.1, h.2.1⟩
    have h3 : [x, y] ∈ C → InU C x ∨ InV C y := by
      intro hc
      by_cases hu : InU C x
      · exact Or.inl hu
      · right
        have : [x] ∈ C ∨ Res C [x] := by
          unfold InU at hu; tauto
        exact Res.of_mem_mem this (by simpa using hc) (by simp)
    split_ifs <;> simp_all
  | [x, y, z], _ =>
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.take, List.drop, letters_nil, ne_eq, reduceCtorEq, not_false_eq_true, conv_letters',
      List.dropLast, WordSeries.epsilon, pS, qS, zero_add, zero_mul, one_mul, mul_one,
      add_zero]
    -- the facts of the paper for a codeword `xyz`
    have i1 : [x, y, z] ∈ C → ¬ InV C z → [x, y] ∉ C ∧ ¬ Res C [x, y] := by
      intro hc hv
      constructor
      · intro hxy; exact hv (Res.of_mem_mem (Or.inl hxy) (by simpa using hc) (by simp))
      · intro hxy; exact hv (Res.of_mem_mem (Or.inr hxy) (by simpa using hc) (by simp))
    have i2 : [x, y, z] ∈ C → ¬ InU C x → Res C [y, z] := by
      intro hc hu
      have : [x] ∈ C ∨ Res C [x] := by unfold InU at hu; tauto
      exact Res.of_mem_mem this (by simpa using hc) (by simp)
    have hP3 : InP3 C x y z → InP2 C x y ∧ ¬ InU C x ∧ ¬ InV C z ∧ ¬ InS3 C x y z ∧
        [x, y, z] ∉ C := by
      intro h
      refine ⟨h.1, h.2.1, h.2.2.1.2, fun h' => h.1.2.2 h'.2.2.2, fun hc => h.2.2.2 (i2 hc h.2.1)⟩
    have hS3 : InS3 C x y z → InS2 C y z ∧ ¬ InV C z ∧ ¬ InU C x ∧ [x, y, z] ∉ C := by
      intro h
      refine ⟨h.1, h.2.1, fun hu => hu.2 h.2.2.1, fun hc => (i1 hc h.2.1).2 h.2.2.2⟩
    have hc : [x, y, z] ∈ C → (InU C x ∧ InV C z) ∨ (InU C x ∧ ¬ InV C z ∧ InP2 C x y) ∨
        (¬ InU C x ∧ InV C z ∧ InS2 C y z) ∨
        (¬ InU C x ∧ ¬ InV C z ∧ (InP2 C x y ∨ InS2 C y z)) := by
      intro hc
      by_cases hu : InU C x <;> by_cases hv : InV C z
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr (Or.inl ⟨hu, hv, Or.inl hu, (i1 hc hv).1, (i1 hc hv).2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hu, hv, Or.inr hv, i2 hc hu⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨hu, hv, ?_⟩))
        have hyz := i2 hc hu
        have hy : [y] ∉ C := fun hy => hv (Res.of_mem_res hy (by simpa using hyz) (by simp))
        by_cases hvy : InV C y
        · exact Or.inl ⟨Or.inr hvy, (i1 hc hv).1, (i1 hc hv).2⟩
        · exact Or.inr ⟨Or.inl ⟨hy, hvy⟩, hyz⟩
    split_ifs <;> simp_all

end Coefficients

/-! ## The certificate -/

theorem coeff_le (C : Set (Word A)) (hC : IsUniquelyDecodable C) (w : Word A) :
    (pS C ⋆ qS C) w ≤ WordSeries.epsilon w + ((pS C ⋆ letters) ⋆ qS C) w := by
  classical
  by_cases hw : w.length ≤ 3
  · exact le_trans (Nat.le_add_right _ _) (coeff_short C hC w hw)
  · exact coeff_long_words C w (by omega)

theorem coeff_lt (C : Set (Word A)) (hC : IsUniquelyDecodable C) {w : Word A} (hwC : w ∈ C)
    (hw : w.length ≤ 3) : (pS C ⋆ qS C) w < WordSeries.epsilon w + ((pS C ⋆ letters) ⋆ qS C) w := by
  classical
  have := coeff_short C hC w hw
  rw [ite_eq_left hwC] at this
  omega

theorem finite_pS [Finite A] (C : Set (Word A)) : Set.Finite {w | 0 < pS C w} :=
  (List.finite_length_le A 3).subset fun w hw => by
    by_contra h
    simp only [Set.mem_ofPred_eq, not_le] at hw h
    rw [pS_long C w h] at hw
    exact lt_irrefl 0 hw

theorem finite_qS [Finite A] (C : Set (Word A)) : Set.Finite {w | 0 < qS C w} :=
  (List.finite_length_le A 3).subset fun w hw => by
    by_contra h
    simp only [Set.mem_ofPred_eq, not_le] at hw h
    rw [qS_long C w h] at hw
    exact lt_irrefl 0 hw

/-- **Proposition 5.** Every code whose words have length at most three has a positive finite
completion. -/
theorem prop5 [Fintype A] (C : Finset (Word A)) (hC : IsUniquelyDecodable (C : Set (Word A)))
    (h3 : ∀ w ∈ C, w.length ≤ 3) : HasPositiveCompletion (C : Set (Word A)) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    have hC0 : C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rcases w with _ | ⟨a, _⟩
      · exact hC.epsilon_notMem hw
      · exact isEmptyElim a
    exact small_code_completion C (by simp [hC0]) hC
  | inr hA =>
    apply HasFiniteCertificate.toPositive
    refine ⟨pS (C : Set (Word A)), qS (C : Set (Word A)),
      fun w => WordSeries.epsilon w + ((pS (C : Set (Word A)) ⋆ letters) ⋆ qS (C : Set (Word A))) w -
        (pS (C : Set (Word A)) ⋆ qS (C : Set (Word A))) w, rfl, rfl,
      finite_pS _, finite_qS _, ?_, ?_⟩
    · funext w
      have := coeff_le (C : Set (Word A)) hC w
      simp only [Pi.add_apply]
      omega
    · intro w hw
      have := coeff_lt (C : Set (Word A)) hC hw (h3 w hw)
      simp only
      omega

end SmallestNoncompletable
