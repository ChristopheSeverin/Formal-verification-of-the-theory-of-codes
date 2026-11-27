module

public import SubalgebraFreeness.Machine
public import Mathlib.Order.Prod.Lex.Basic

/-! # Cycles of the rewriting graph

The graph contains every word with one control letter, not only the reachable ones.

* `potential_lt`: every rule other than the reset strictly increases a lexicographic potential.
  Outside the cleanup the length never decreases, and a length-preserving simulation step moves
  forward in the order `B < H < U < P < F`, with sweeps moving in one direction. In the cleanup
  `C` moves right and `E` erases. Hence every cycle uses the reset `L E → L H_{q₀} w`.
* `rt_after_E`: on a cycle, the symbol after `E` is the right delimiter, since `E` is created by
  `C R → E R` and erasing keeps its right neighbour. The reset therefore produces
  `u L H_{q₀} w R v`, from which the run simulates the machine on `w`.
* `delims_edge`: each rule preserves the numbers of `L` and of `R`. Every cycle contains both
  delimiters, whereas a bare left side contains at most one. -/

@[expose] public section
namespace SubalgebraFreeness

open Turing

namespace Machine

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (w : List Γ)

/-! ### A potential increased by every rule except the reset -/

/-- A point of `ℕ ×ₗ ℤ ×ₗ ℤ`, ordered lexicographically. -/
def pot (a : ℕ) (b c : ℤ) : ℕ ×ₗ (ℤ ×ₗ ℤ) := toLex (a, toLex (b, c))

theorem pot_lt_iff {a a' : ℕ} {b b' c c' : ℤ} :
    pot a b c < pot a' b' c' ↔ a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ c < c') := by
  simp [pot, Prod.Lex.toLex_lt_toLex]

/-- The phase, then the length or the position of the control letter. -/
def potential (x : Vertex (Cell Γ) (Ctrl Λ)) : ℕ ×ₗ (ℤ ×ₗ ℤ) :=
  match x.2.1 with
  | .H _ => pot 0 (x.1.length + x.2.2.length) 1
  | .U _ => pot 0 (x.1.length + x.2.2.length) 2
  | .P _ => pot 0 (x.1.length + x.2.2.length) 3
  | .F _ => pot 0 (x.1.length + x.2.2.length) (4 + x.1.length)
  | .B _ => pot 0 (x.1.length + x.2.2.length) (-(x.1.length : ℤ))
  | .C => pot 1 x.1.length 0
  | .E => pot 2 (-((x.1.length : ℤ) + x.2.2.length)) 0

-- Depending on the rule, `simp` alone or `simp` followed by `omega` closes the goal.
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
theorem potential_lt (e : Edge (Cell Γ) (Rule Γ Λ)) (he : e.2.1 ≠ .reset) :
    potential ((rules M w).src e) < potential ((rules M w).tgt e) := by
  obtain ⟨u, i, v⟩ := e
  cases i
  case instr q c =>
    cases hM : M q c with
    | none =>
      simp [Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight,
        potential, pot_lt_iff, hM]
    | some p =>
      obtain ⟨r, s⟩ := p
      cases s with
      | write d =>
        simp [Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
          Ctrl.inspectsRight, potential, pot_lt_iff, hM]
      | move d =>
        cases d <;>
        simp [Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
            Ctrl.inspectsRight, potential, pot_lt_iff, hM] <;> omega
  case reset => exact absurd rfl he
  all_goals
    simp [Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight,
      potential, pot_lt_iff] <;> omega

/-- **Every cycle uses the reset.** -/
theorem reset_in_cycle {x : Vertex (Cell Γ) (Ctrl Λ)} (hx : (rules M w).Periodic x) :
    ∃ j e, e.2.1 = Rule.reset ∧ (rules M w).nextO^[j] (some x) = some ((rules M w).src e) := by
  by_contra hno
  push Not at hno
  obtain ⟨p, hp, hxp⟩ := hx
  have hsome := Rules.Periodic.iterate_isSome (rules M w) ⟨p, hp, hxp⟩
  have key : ∀ j, ∃ y, (rules M w).nextO^[j + 1] (some x) = some y ∧ potential x < potential y := by
    intro j
    induction j with
    | zero =>
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hsome 1)
      obtain ⟨e, hsrc, htgt⟩ := (rules M w).next_eq_some hy
      refine ⟨y, hy, ?_⟩
      rw [← hsrc, ← htgt]
      refine potential_lt M w e fun hreset => hno 0 e hreset ?_
      rw [hsrc]; rfl
    | succ j ih =>
      obtain ⟨y, hy, hlt⟩ := ih
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hsome (j + 2))
      have hnext : (rules M w).next y = some z := by
        rw [← hz, Function.iterate_succ_apply', hy]; rfl
      obtain ⟨e, hsrc, htgt⟩ := (rules M w).next_eq_some hnext
      refine ⟨z, hz, hlt.trans ?_⟩
      rw [← hsrc, ← htgt]
      refine potential_lt M w e fun hreset => hno (j + 1) e hreset ?_
      rw [hsrc, hy]
  obtain ⟨y, hy, hlt⟩ := key (p - 1)
  rw [Nat.sub_add_cancel hp, hxp] at hy
  cases hy
  exact lt_irrefl _ hlt

/-! ### The right neighbour of `E` -/

/-- Along every edge, if the target carries `E`, the symbol after it is `R` as soon as this holds
at the source. -/
theorem rt_after_E_edge (e : Edge (Cell Γ) (Rule Γ Λ))
    (h : ((rules M w).src e).2.1 = .E → ∃ v', ((rules M w).src e).2.2 = .rt :: v') :
    ((rules M w).tgt e).2.1 = .E → ∃ v', ((rules M w).tgt e).2.2 = .rt :: v' := by
  obtain ⟨u, i, v⟩ := e
  cases i
  case instr q c =>
    cases hM : M q c with
    | none => simp [Rules.tgt, put, rules, rhs, hM]
    | some p =>
      obtain ⟨r, s⟩ := p
      cases s with
      | write d => simp [Rules.tgt, put, rules, rhs, hM]
      | move d => cases d <;> simp [Rules.tgt, put, rules, rhs, hM]
  case erase m c =>
    simpa [Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight]
      using h
  all_goals simp [Rules.tgt, put, rules, rhs]

theorem rt_after_E {y z : Vertex (Cell Γ) (Ctrl Λ)} (hy : y.2.1 = .E → ∃ v', y.2.2 = .rt :: v')
    {m : ℕ} (hz : (rules M w).nextO^[m] (some y) = some z) :
    z.2.1 = .E → ∃ v', z.2.2 = .rt :: v' := by
  induction m generalizing z with
  | zero => cases hz; exact hy
  | succ m ih =>
    rw [Function.iterate_succ_apply'] at hz
    cases hm : (rules M w).nextO^[m] (some y) with
    | none => rw [hm] at hz; cases hz
    | some y' =>
      rw [hm] at hz
      obtain ⟨e, hsrc, htgt⟩ := (rules M w).next_eq_some hz
      rw [← htgt]
      exact rt_after_E_edge M w e (hsrc ▸ ih hm)

/-- **A cycle passes through the initial word with some outside context.** -/
theorem periodic_reaches_start {x : Vertex (Cell Γ) (Ctrl Λ)} (hx : (rules M w).Periodic x) :
    ∃ m u v, (rules M w).nextO^[m] (some x) = some (u ++ [.lt], .H default, input w ++ .rt :: v) := by
  obtain ⟨j, e, hreset, hj⟩ := reset_in_cycle M w hx
  obtain ⟨u, i, v⟩ := e
  simp only at hreset
  subst hreset
  have hsrc : (rules M w).src (u, Rule.reset, v) = (u ++ [.lt], .E, v) := by
    simp [Rules.src, put, rules, lhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight]
  have htgt : (rules M w).tgt (u, Rule.reset, v) = (u ++ [.lt], .H default, input w ++ v) := by
    simp [Rules.tgt, put, rules, rhs]
  have hz : (rules M w).nextO^[j + 1] (some x) = some (u ++ [.lt], .H default, input w ++ v) := by
    rw [Function.iterate_succ_apply', hj, Rules.nextO_some,
      (rules M w).next_src (functional M w), htgt]
  -- The reset source lies on the cycle after the reset target.
  obtain ⟨p, hp, hxp⟩ := hx
  have hback : (rules M w).nextO^[p - 1] (some (u ++ [.lt], .H default, input w ++ v)) =
      some (u ++ [.lt], .E, v) := by
    rw [← hz, ← Function.iterate_add_apply, show p - 1 + (j + 1) = j + p by omega,
      Function.iterate_add_apply, hxp, hj, hsrc]
  obtain ⟨v', hv'⟩ := rt_after_E M w (y := (u ++ [.lt], .H default, input w ++ v))
    (by intro h; cases h) hback rfl
  simp only at hv'
  subst hv'
  exact ⟨j + 1, u, v', hz⟩

/-- **A cycle exists exactly when the machine halts.** -/
theorem periodic_iff_halts :
    (∃ x, (rules M w).Periodic x) ↔ Halts M w := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨m, u, v, hm⟩ := periodic_reaches_start M w hx
    have hz : (rules M w).Periodic (u ++ [.lt], .H default, input w ++ .rt :: v) :=
      Rules.Periodic.of_reach _ hx hm
    obtain ⟨j, e, hreset, hj⟩ := reset_in_cycle M w hz
    obtain ⟨u', i, v''⟩ := e
    simp only at hreset
    subst hreset
    exact halts_of_cleanup M w j (enc_init w u v) ⟨_, hj, by
      simp [Rules.src, put, rules, lhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight, Ctrl.cleanup]⟩
  · intro h
    exact ⟨start w, periodic_of_halts M w h⟩

/-! ### Delimiters -/

/-- The left delimiter. -/
def isLt : Cell Γ → Bool
  | .lt => true
  | _ => false

/-- The right delimiter. -/
def isRt : Cell Γ → Bool
  | .rt => true
  | _ => false

/-- The numbers of left and right delimiters in a vertex. -/
def delims (x : Vertex (Cell Γ) (Ctrl Λ)) : ℕ × ℕ :=
  ((x.1 ++ x.2.2).countP isLt, (x.1 ++ x.2.2).countP isRt)

omit [Inhabited Λ] in
theorem countP_input_lt : (input w).countP (isLt (Γ := Γ)) = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  simp only [input, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  simp [isLt]

omit [Inhabited Λ] in
theorem countP_input_rt : (input w).countP (isRt (Γ := Γ)) = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  simp only [input, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  simp [isRt]

theorem delims_edge (e : Edge (Cell Γ) (Rule Γ Λ)) :
    delims ((rules M w).src e) = delims ((rules M w).tgt e) := by
  obtain ⟨u, i, v⟩ := e
  cases i
  case instr q c =>
    cases hM : M q c with
    | none =>
      simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
        Ctrl.inspectsRight, hM, List.countP_append, isLt, isRt]
    | some p =>
      obtain ⟨r, s⟩ := p
      cases s with
      | write d =>
        simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
          Ctrl.inspectsRight, hM, List.countP_append, isLt, isRt]
      | move d =>
        cases d <;>
        · simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
            Ctrl.inspectsRight, hM, List.countP_append, isLt, isRt]
  case carry m c =>
    cases m <;> simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
      Ctrl.inspectsRight, List.countP_append, isLt, isRt]
  case erase m c =>
    cases m <;> simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
      Ctrl.inspectsRight, List.countP_append, isLt, isRt]
  case reset =>
    simp only [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
      Ctrl.inspectsRight, List.countP_append, countP_input_lt, countP_input_rt]
    simp [isLt, isRt]
  all_goals
    simp [delims, Rules.src, Rules.tgt, put, rules, lhs, rhs, Rule.ctrl, Rule.cell,
      Ctrl.inspectsRight, List.countP_append, List.countP_cons, isLt, isRt, blank]

theorem delims_iterate {x y : Vertex (Cell Γ) (Ctrl Λ)} {m : ℕ}
    (h : (rules M w).nextO^[m] (some x) = some y) : delims y = delims x := by
  induction m generalizing y with
  | zero => cases h; rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hm : (rules M w).nextO^[m] (some x) with
    | none => rw [hm] at h; cases h
    | some y' =>
      rw [hm] at h
      obtain ⟨e, hsrc, htgt⟩ := (rules M w).next_eq_some h
      rw [← htgt, ← delims_edge, hsrc, ih hm]

/-- **Bare left sides lie on no cycle.** Every cycle contains both delimiters, while a left side
contains at most one of them. -/
theorem lhs_not_periodic (i : Rule Γ Λ) : ¬ (rules M w).Periodic (lhs i) := by
  intro hi
  obtain ⟨m, u, v, hm⟩ := periodic_reaches_start M w hi
  have h := delims_iterate M w hm
  have hl : 1 ≤ (delims (u ++ [.lt], (.H default : Ctrl Λ), input w ++ .rt :: v)).1 := by
    simp only [delims, List.countP_append, List.countP_cons, List.countP_nil, countP_input_lt]
    simp [isLt]
    omega
  have hr : 1 ≤ (delims (u ++ [.lt], (.H default : Ctrl Λ), input w ++ .rt :: v)).2 := by
    simp only [delims, List.countP_append, List.countP_cons, List.countP_nil, countP_input_rt]
    simp [isRt]
    omega
  rw [h] at hl hr
  have hsum : (delims (lhs i : Vertex (Cell Γ) (Ctrl Λ))).1 +
      (delims (lhs i : Vertex (Cell Γ) (Ctrl Λ))).2 ≤ 1 := by
    simp only [delims, lhs]
    split_ifs <;> cases i.cell <;> simp [isLt, isRt]
  omega

end Machine

end SubalgebraFreeness
