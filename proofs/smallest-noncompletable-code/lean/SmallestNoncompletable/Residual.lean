module

public import ThreeWordCodes.Certificate
public import Mathlib.Algebra.BigOperators.Intervals

/-! # The residual closure

`D(C)` is the least set of nonempty words closed under the three residual rules. A residual is
realized by two partial parsings with different first words, so a code meets no residual
(Lemma 3, the direction used here). -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

variable {A : Type*}

/-- The residual closure `D(C)`: `∂(C, C) ∪ ∂(D, C) ∪ ∂(C, D) ⊆ D`. -/
inductive Res (C : Set (Word A)) : Word A → Prop
  | base {u r : Word A} : u ∈ C → u ++ r ∈ C → r ≠ [] → Res C r
  | left {u r : Word A} : Res C u → u ++ r ∈ C → r ≠ [] → Res C r
  | right {u r : Word A} : u ∈ C → Res C (u ++ r) → r ≠ [] → Res C r

/-- Each residual is realized by two parsings with different first words, one concatenation
extending the other by the residual. -/
theorem Res.realized {C : Set (Word A)} {r : Word A} (h : Res C r) :
    ∃ x y : Word A, ∃ L₁ L₂ : List (Word A), x ≠ y ∧ x ∈ C ∧ y ∈ C ∧
      (∀ z ∈ L₁, z ∈ C) ∧ (∀ z ∈ L₂, z ∈ C) ∧
      (x :: L₁).flatten = (y :: L₂).flatten ++ r := by
  induction h with
  | @base u r hu hur hr =>
    refine ⟨u ++ r, u, [], [], ?_, hur, hu, by simp, by simp, by simp⟩
    intro e
    have := congrArg List.length e
    simp at this
    exact hr this
  | @left u r _ hur hr ih =>
    obtain ⟨x, y, L₁, L₂, hxy, hx, hy, h1, h2, e⟩ := ih
    refine ⟨y, x, L₂ ++ [u ++ r], L₁, hxy.symm, hy, hx, ?_, h1, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact h2 z hz
      · rw [List.mem_singleton.mp hz]; exact hur
    · simp only [List.flatten_cons, List.flatten_append] at e ⊢
      rw [e]; simp
  | @right u r hu _ hr ih =>
    obtain ⟨x, y, L₁, L₂, hxy, hx, hy, h1, h2, e⟩ := ih
    refine ⟨x, y, L₁, L₂ ++ [u], hxy, hx, hy, h1, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact h2 z hz
      · rw [List.mem_singleton.mp hz]; exact hu
    · simp only [List.flatten_cons, List.flatten_append] at e ⊢
      rw [e]; simp

/-- **Lemma 3, one direction.** A code contains none of its residuals. -/
theorem Res.not_mem {C : Set (Word A)} (hC : IsUniquelyDecodable C) {r : Word A} (h : Res C r) :
    r ∉ C := by
  intro hr
  obtain ⟨x, y, L₁, L₂, hxy, hx, hy, h1, h2, e⟩ := h.realized
  have := hC (x :: L₁) (y :: L₂ ++ [r])
    (by intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exacts [hx, h1 z hz])
    (by
      intro z hz
      simp only [List.cons_append, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hz
      rcases hz with rfl | hz | rfl
      exacts [hy, h2 z hz, hr])
    (by rw [e]; simp)
  simp only [List.cons_append, List.cons.injEq] at this
  exact hxy this.1

/-- The closure rules (8). -/
theorem Res.of_mem_mem {C : Set (Word A)} {x r : Word A} (hx : x ∈ C ∨ Res C x)
    (hxr : x ++ r ∈ C) (hr : r ≠ []) : Res C r := by
  rcases hx with hx | hx
  exacts [Res.base hx hxr hr, Res.left hx hxr hr]

theorem Res.of_mem_res {C : Set (Word A)} {x r : Word A} (hx : x ∈ C) (hxr : Res C (x ++ r))
    (hr : r ≠ []) : Res C r := Res.right hx hxr hr

/-! ## Convolution as a sum over cuts -/

open WordSeries in
theorem conv_eq_sum (f g : Series A) : ∀ w : Word A,
    (f ⋆ g) w = ∑ i ∈ Finset.range (w.length + 1), f (w.take i) * g (w.drop i)
  | [] => by simp
  | a :: w => by
    rw [conv_cons, conv_eq_sum (shift a f) g w, List.length_cons,
      Finset.sum_range_succ' _ (w.length + 1)]
    simp [shift, add_comm]

end SmallestNoncompletable
