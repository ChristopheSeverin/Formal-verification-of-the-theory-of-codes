module

public import SubalgebraFreeness.GraphCriterion
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-! # Encoding a computation by rewriting rules

We encode a Turing machine in Mathlib's `TM0` model. In this model each step either writes a
symbol or moves the head, and the machine halts when its transition is undefined. The rules are
those of the manuscript with this adaptation.

* An instruction `H_q c → d P_r` (write and move right) becomes either `H_q c → P_r d` (write),
  `H_q c → c P_r` (move right) or `H_q c → U_r c` (move left).
* The manuscript's halting rule `H_h → C` becomes `H_q c → C c` for every pair `(q, c)` on which
  the machine halts.
* The initial state is `default`, the blank is `default`, and the initial word is
  `L H_{q₀} w R`, where an empty input is replaced by a single blank.

The other rules are copied verbatim. The marking round `P_r c → c̄ F_r`, the sweep of `F_r` to the
right delimiter, `F_r R → B_r □ R`, the sweep of `B_r` back and `c̄ B_r → H_r c` simulate one
step and add a blank at the right end. -/

@[expose] public section
namespace SubalgebraFreeness

open Turing

/-- The alphabet `D`: tape symbols, marked tape symbols, and the delimiters `L` and `R`. -/
inductive Cell (Γ : Type*)
  | plain (c : Γ)
  | marked (c : Γ)
  | lt
  | rt
  deriving DecidableEq, Fintype

/-- The alphabet `S` of control letters `H_q`, `P_q`, `U_q`, `F_q`, `B_q`, `C` and `E`. -/
inductive Ctrl (Λ : Type*)
  | H (q : Λ)
  | P (q : Λ)
  | U (q : Λ)
  | F (q : Λ)
  | B (q : Λ)
  | C
  | E
  deriving DecidableEq, Fintype

/-- The names of the rules, one constructor for each family of the manuscript. -/
inductive Rule (Γ Λ : Type*)
  /-- `H_q c → ⋯`: the instruction for state `q` reading `c`, or the start of the cleanup. -/
  | instr (q : Λ) (c : Γ)
  /-- `c U_r → P_r c`. -/
  | shiftU (r : Λ) (c : Γ)
  /-- `L U_r → L P_r □`. -/
  | edgeU (r : Λ)
  /-- `P_r R → P_r □ R`. -/
  | edgeP (r : Λ)
  /-- `P_r c → c̄ F_r`. -/
  | mark (r : Λ) (c : Γ)
  /-- `F_r c → c F_r`. -/
  | sweepF (r : Λ) (c : Γ)
  /-- `F_r R → B_r □ R`. -/
  | turn (r : Λ)
  /-- `c B_r → B_r c`. -/
  | sweepB (r : Λ) (c : Γ)
  /-- `c̄ B_r → H_r c`. -/
  | unmark (r : Λ) (c : Γ)
  /-- `C x → x C` for a plain (`false`) or marked (`true`) symbol `x`. -/
  | carry (m : Bool) (c : Γ)
  /-- `C R → E R`. -/
  | drop
  /-- `x E → E` for a plain (`false`) or marked (`true`) symbol `x`. -/
  | erase (m : Bool) (c : Γ)
  /-- `L E → L H_{q₀} w`. -/
  | reset
  deriving DecidableEq, Fintype

variable {Γ Λ : Type*}

/-- A plain (`false`) or marked (`true`) tape symbol. -/
def sym : Bool → Γ → Cell Γ
  | false, c => .plain c
  | true, c => .marked c

@[simp] theorem sym_false (c : Γ) : sym false c = .plain c := rfl
@[simp] theorem sym_true (c : Γ) : sym true c = .marked c := rfl

@[simp] theorem sym_ne_lt (m : Bool) (c : Γ) : sym m c ≠ .lt := by cases m <;> simp
@[simp] theorem sym_ne_rt (m : Bool) (c : Γ) : sym m c ≠ .rt := by cases m <;> simp

@[simp] theorem lt_ne_sym (m : Bool) (c : Γ) : .lt ≠ sym m c := (sym_ne_lt m c).symm
@[simp] theorem rt_ne_sym (m : Bool) (c : Γ) : .rt ≠ sym m c := (sym_ne_rt m c).symm

@[simp] theorem sym_inj {m m' : Bool} {c c' : Γ} : sym m c = sym m' c' ↔ m = m' ∧ c = c' := by
  cases m <;> cases m' <;> simp

/-- Whether the rules for a control letter inspect its right neighbour. -/
def Ctrl.inspectsRight : Ctrl Λ → Bool
  | .H _ | .P _ | .F _ | .C => true
  | .U _ | .B _ | .E => false

/-- The control letter of the left side of a rule. -/
def Rule.ctrl : Rule Γ Λ → Ctrl Λ
  | .instr q _ => .H q
  | .shiftU r _ => .U r
  | .edgeU r => .U r
  | .edgeP r => .P r
  | .mark r _ => .P r
  | .sweepF r _ => .F r
  | .turn r => .F r
  | .sweepB r _ => .B r
  | .unmark r _ => .B r
  | .carry _ _ => .C
  | .drop => .C
  | .erase _ _ => .E
  | .reset => .E

/-- The inspected neighbour in the left side of a rule. -/
def Rule.cell : Rule Γ Λ → Cell Γ
  | .instr _ c => .plain c
  | .shiftU _ c => .plain c
  | .edgeU _ => .lt
  | .edgeP _ => .rt
  | .mark _ c => .plain c
  | .sweepF _ c => .plain c
  | .turn _ => .rt
  | .sweepB _ c => .plain c
  | .unmark _ c => .marked c
  | .carry m c => sym m c
  | .drop => .rt
  | .erase m c => sym m c
  | .reset => .lt

/-- The left side of a rule: the control letter followed or preceded by the inspected symbol. -/
def lhs (i : Rule Γ Λ) : Vertex (Cell Γ) (Ctrl Λ) :=
  if i.ctrl.inspectsRight then ([], i.ctrl, [i.cell]) else ([i.cell], i.ctrl, [])

theorem ctrl_cell_injective : Function.Injective (fun i : Rule Γ Λ => (i.ctrl, i.cell)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [Rule.ctrl, Rule.cell]

/-- The cleanup letters `C` and `E`. -/
def Ctrl.cleanup : Ctrl Λ → Bool
  | .C | .E => true
  | _ => false

namespace Machine

variable [Inhabited Γ] [Inhabited Λ]

/-- The blank symbol `□`. -/
def blank : Cell Γ := .plain default

/-- The input word, with a blank for the empty input. -/
def input (w : List Γ) : List (Cell Γ) := (w.headI :: w.tail).map .plain

/-- The right sides of the rules for the machine `M` and the input `w`. -/
def rhs (M : TM0.Machine Γ Λ) (w : List Γ) : Rule Γ Λ → Vertex (Cell Γ) (Ctrl Λ)
  | .instr q c =>
    match M q c with
    | none => ([], .C, [.plain c])
    | some (r, .write d) => ([], .P r, [.plain d])
    | some (r, .move .right) => ([.plain c], .P r, [])
    | some (r, .move .left) => ([], .U r, [.plain c])
  | .shiftU r c => ([], .P r, [.plain c])
  | .edgeU r => ([.lt], .P r, [blank])
  | .edgeP r => ([], .P r, [blank, .rt])
  | .mark r c => ([.marked c], .F r, [])
  | .sweepF r c => ([.plain c], .F r, [])
  | .turn r => ([], .B r, [blank, .rt])
  | .sweepB r c => ([], .B r, [.plain c])
  | .unmark r c => ([], .H r, [.plain c])
  | .carry m c => ([sym m c], .C, [])
  | .drop => ([], .E, [.rt])
  | .erase _ _ => ([], .E, [])
  | .reset => ([.lt], .H default, input w)

/-- The rewriting rules encoding the machine `M` on the input `w`. -/
def rules (M : TM0.Machine Γ Λ) (w : List Γ) : Rules (Cell Γ) (Ctrl Λ) (Rule Γ Λ) :=
  ⟨lhs, rhs M w⟩

variable (M : TM0.Machine Γ Λ) (w : List Γ)

/-- **At most one rule applies.** The control letter fixes the direction of inspection, and the
inspected symbol selects the rule. -/
theorem functional : (rules M w).Functional := by
  rintro ⟨u, i, v⟩ ⟨u', i', v'⟩ h
  simp only [Rules.src, put, rules, lhs] at h
  have hc : i.ctrl = i'.ctrl := by split_ifs at h <;> exact (Prod.mk.inj (Prod.mk.inj h).2).1
  by_cases hi : i.ctrl.inspectsRight = true <;> by_cases hi' : i'.ctrl.inspectsRight = true
  · simp only [hi, hi', ite_true, List.append_nil, List.singleton_append, Prod.mk.injEq,
      List.cons.injEq] at h
    obtain ⟨rfl, -, hy, rfl⟩ := h
    rw [ctrl_cell_injective (show (i.ctrl, i.cell) = (i'.ctrl, i'.cell) by rw [hc, hy])]
  · exact absurd (hc ▸ hi) hi'
  · exact absurd (hc ▸ hi') hi
  · simp only [hi, hi', Bool.false_eq_true, ite_false, List.nil_append, Prod.mk.injEq] at h
    obtain ⟨h₁, -, rfl⟩ := h
    obtain ⟨rfl, hy⟩ := List.append_inj' h₁ rfl
    simp only [List.cons.injEq, and_true] at hy
    rw [ctrl_cell_injective (show (i.ctrl, i.cell) = (i'.ctrl, i'.cell) by rw [hc, hy])]

theorem next_rule (i : Rule Γ Λ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ (lhs i).1, (lhs i).2.1, (lhs i).2.2 ++ v) =
      some (u ++ (rhs M w i).1, (rhs M w i).2.1, (rhs M w i).2.2 ++ v) :=
  (rules M w).next_src (functional M w) (u, i, v)

/-! ### Individual steps -/

section Steps

variable {M w}

theorem next_halt {q : Λ} {c : Γ} (h : M q c = none) (u v : List (Cell Γ)) :
    (rules M w).next (u, .H q, .plain c :: v) = some (u, .C, .plain c :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight, h] using
    next_rule M w (.instr q c) u v

theorem next_write {q r : Λ} {c d : Γ} (h : M q c = some (r, .write d)) (u v : List (Cell Γ)) :
    (rules M w).next (u, .H q, .plain c :: v) = some (u, .P r, .plain d :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight, h] using
    next_rule M w (.instr q c) u v

theorem next_right {q r : Λ} {c : Γ} (h : M q c = some (r, .move .right)) (u v : List (Cell Γ)) :
    (rules M w).next (u, .H q, .plain c :: v) = some (u ++ [.plain c], .P r, v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight, h] using
    next_rule M w (.instr q c) u v

theorem next_left {q r : Λ} {c : Γ} (h : M q c = some (r, .move .left)) (u v : List (Cell Γ)) :
    (rules M w).next (u, .H q, .plain c :: v) = some (u, .U r, .plain c :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight, h] using
    next_rule M w (.instr q c) u v

variable (M w)

theorem next_shiftU (r : Λ) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [.plain c], .U r, v) = some (u, .P r, .plain c :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.shiftU r c) u v

theorem next_edgeU (r : Λ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [.lt], .U r, v) = some (u ++ [.lt], .P r, blank :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w (.edgeU r) u v

theorem next_edgeP (r : Λ) (u v : List (Cell Γ)) :
    (rules M w).next (u, .P r, .rt :: v) = some (u, .P r, blank :: .rt :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w (.edgeP r) u v

theorem next_mark (r : Λ) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u, .P r, .plain c :: v) = some (u ++ [.marked c], .F r, v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w (.mark r c) u v

theorem next_sweepF (r : Λ) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u, .F r, .plain c :: v) = some (u ++ [.plain c], .F r, v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.sweepF r c) u v

theorem next_turn (r : Λ) (u v : List (Cell Γ)) :
    (rules M w).next (u, .F r, .rt :: v) = some (u, .B r, blank :: .rt :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w (.turn r) u v

theorem next_sweepB (r : Λ) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [.plain c], .B r, v) = some (u, .B r, .plain c :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.sweepB r c) u v

theorem next_unmark (r : Λ) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [.marked c], .B r, v) = some (u, .H r, .plain c :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.unmark r c) u v

theorem next_carry (m : Bool) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u, .C, sym m c :: v) = some (u ++ [sym m c], .C, v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.carry m c) u v

theorem next_drop (u v : List (Cell Γ)) :
    (rules M w).next (u, .C, .rt :: v) = some (u, .E, .rt :: v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w .drop u v

theorem next_erase (m : Bool) (c : Γ) (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [sym m c], .E, v) = some (u, .E, v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using
    next_rule M w (.erase m c) u v

theorem next_reset (u v : List (Cell Γ)) :
    (rules M w).next (u ++ [.lt], .E, v) = some (u ++ [.lt], .H default, input w ++ v) := by
  simpa [lhs, rhs, Rule.ctrl, Rule.cell, Ctrl.inspectsRight] using next_rule M w .reset u v

end Steps

/-! ### Runs through the simulation phases -/

/-- `x` reaches `y` in exactly `k` steps, all taken from vertices outside the cleanup phase. -/
def SimReach (x y : Vertex (Cell Γ) (Ctrl Λ)) (k : ℕ) : Prop :=
  (rules M w).nextO^[k] (some x) = some y ∧
    ∀ j < k, ∃ z, (rules M w).nextO^[j] (some x) = some z ∧ z.2.1.cleanup = false

variable {M w}

theorem SimReach.refl (x : Vertex (Cell Γ) (Ctrl Λ)) : SimReach M w x x 0 :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem SimReach.single {x y : Vertex (Cell Γ) (Ctrl Λ)} (h : (rules M w).next x = some y)
    (hx : x.2.1.cleanup = false) : SimReach M w x y 1 :=
  ⟨h, fun j hj => ⟨x, by rw [Nat.lt_one_iff.mp hj]; rfl, hx⟩⟩

theorem SimReach.trans {x y z : Vertex (Cell Γ) (Ctrl Λ)} {a b : ℕ} (h₁ : SimReach M w x y a)
    (h₂ : SimReach M w y z b) : SimReach M w x z (a + b) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [add_comm, Function.iterate_add_apply, h₁.1, h₂.1]
  · by_cases hja : j < a
    · exact h₁.2 j hja
    · obtain ⟨z', hz', hc⟩ := h₂.2 (j - a) (by omega)
      refine ⟨z', ?_, hc⟩
      rw [show j = (j - a) + a by omega, Function.iterate_add_apply, h₁.1, hz']

theorem SimReach.cast {x y : Vertex (Cell Γ) (Ctrl Λ)} {a b : ℕ} (h : SimReach M w x y a)
    (hab : a = b) : SimReach M w x y b := hab ▸ h

variable (M w)

theorem sweepF (r : Λ) (v : List (Cell Γ)) :
    ∀ (β : List Γ) (α : List (Cell Γ)),
      SimReach M w (α, .F r, β.map .plain ++ .rt :: v) (α ++ β.map .plain, .F r, .rt :: v)
        β.length
  | [], α => by simpa using SimReach.refl (M := M) (w := w) (α, .F r, .rt :: v)
  | c :: β, α => by
    have h := (SimReach.single (next_sweepF M w r c α _) rfl).trans (sweepF r v β (α ++ [.plain c]))
    simpa [add_comm] using h

theorem sweepB (r : Λ) (α : List (Cell Γ)) :
    ∀ (β : List Γ) (γ : List (Cell Γ)),
      SimReach M w (α ++ β.map .plain, .B r, γ) (α, .B r, β.map .plain ++ γ) β.length := by
  intro β
  induction β using List.reverseRecOn with
  | nil => intro γ; simpa using SimReach.refl (M := M) (w := w) (α, .B r, γ)
  | append_singleton β c ih =>
    intro γ
    have h₁ := next_sweepB M w r c (α ++ β.map .plain) γ
    have h := (SimReach.single (x := ((α ++ β.map .plain) ++ [.plain c], .B r, γ)) h₁ rfl).trans
      (ih (.plain c :: γ))
    simpa [add_comm] using h

/-- One marking round: from `P_r` before the head cell back to `H_r`, adding a blank at `R`. -/
theorem round (α : List (Cell Γ)) (r : Λ) (c : Γ) (β : List Γ) (v : List (Cell Γ)) :
    SimReach M w (α, .P r, .plain c :: (β.map .plain ++ .rt :: v))
      (α, .H r, .plain c :: (β.map .plain ++ blank :: .rt :: v)) (2 * β.length + 3) := by
  have h₁ := SimReach.single (M := M) (w := w) (next_mark M w r c α (β.map .plain ++ .rt :: v)) rfl
  have h₂ := sweepF M w r v β (α ++ [.marked c])
  have h₃ := SimReach.single (M := M) (w := w) (next_turn M w r (α ++ [.marked c] ++ β.map .plain) v)
    rfl
  have h₄ := sweepB M w r (α ++ [.marked c]) β (blank :: .rt :: v)
  have h₅ := SimReach.single (M := M) (w := w) (next_unmark M w r c α (β.map .plain ++ blank :: .rt :: v))
    rfl
  exact (((h₁.trans h₂).trans h₃).trans h₄).trans h₅ |>.cast (by ring)

/-! ### One step of the machine -/

@[simp] theorem listBlank_mk_append_default (l : List Γ) :
    ListBlank.mk (l ++ [default]) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨1, by simp⟩)

@[simp] theorem listBlank_mk_cons_append_default (a : Γ) (l : List Γ) :
    ListBlank.mk (a :: (l ++ [default])) = ListBlank.mk (a :: l) := by
  rw [← List.cons_append, listBlank_mk_append_default]

/-- `x` encodes the configuration `cfg` in phase `H`, between the delimiters, with an arbitrary
outside context `u` and `v`. -/
def Enc (u v : List (Cell Γ)) (cfg : TM0.Cfg Γ Λ) (x : Vertex (Cell Γ) (Ctrl Λ)) : Prop :=
  ∃ pre post : List Γ,
    x = (u ++ .lt :: pre.map .plain, .H cfg.q, .plain cfg.Tape.head :: (post.map .plain ++ .rt :: v)) ∧
      cfg.Tape.left = ListBlank.mk pre.reverse ∧ cfg.Tape.right = ListBlank.mk post

theorem enc_init (u v : List (Cell Γ)) :
    Enc u v (TM0.init w : TM0.Cfg Γ Λ) (u ++ [.lt], .H default, input w ++ .rt :: v) := by
  refine ⟨[], w.tail, ?_, ?_, ?_⟩
  · simp [input, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']
  · simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']
  · simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']

/-- **Simulation of one step.** The rewriting from an encoding of a configuration reaches an
encoding of the next configuration, through simulation phases only. -/
theorem step_sim {u v : List (Cell Γ)} {cfg cfg' : TM0.Cfg Γ Λ} {x : Vertex (Cell Γ) (Ctrl Λ)}
    (hx : Enc u v cfg x) (hstep : TM0.step M cfg = some cfg') :
    ∃ k y, 0 < k ∧ SimReach M w x y k ∧ Enc u v cfg' y := by
  obtain ⟨q, T⟩ := cfg
  obtain ⟨pre, post, rfl, hL, hR⟩ := hx
  obtain ⟨h, L, Rt⟩ := T
  simp only at hL hR
  subst hL hR
  simp only [TM0.step] at hstep
  cases hM : M q h with
  | none => simp [hM] at hstep
  | some p =>
    obtain ⟨r, s⟩ := p
    simp only [hM, Option.map_some, Option.some.injEq] at hstep
    subst hstep
    cases s with
    | write d =>
      refine ⟨1 + (2 * post.length + 3), _, by omega,
        (SimReach.single (next_write hM _ _) rfl).trans (round M w _ r d post v), ?_⟩
      refine ⟨pre, post ++ [default], ?_, rfl, ?_⟩
      · simp [Tape.write, blank]
      · simp [Tape.write, listBlank_mk_append_default]
    | move dir =>
      cases dir with
      | right =>
        cases post with
        | nil =>
          have h₁ := SimReach.single (M := M) (w := w) (next_right hM (u ++ .lt :: pre.map .plain)
            (List.map Cell.plain [] ++ Cell.rt :: v)) rfl
          have h₂ := SimReach.single (M := M) (w := w)
            (next_edgeP M w r (u ++ .lt :: pre.map .plain ++ [.plain h]) v) rfl
          have h₃ := round M w (u ++ .lt :: pre.map .plain ++ [.plain h]) r default [] v
          refine ⟨_, _, by omega, (h₁.trans h₂).trans (by simpa [blank] using h₃), ?_⟩
          refine ⟨pre ++ [h], [default], ?_, ?_, ?_⟩
          · simp [Tape.move]
          · simp [Tape.move]
          · simp [Tape.move]
            exact (listBlank_mk_append_default []).symm
        | cons d post =>
          have h₁ := SimReach.single (M := M) (w := w) (next_right hM (u ++ .lt :: pre.map .plain)
            (List.map Cell.plain (d :: post) ++ Cell.rt :: v)) rfl
          have h₃ := round M w (u ++ .lt :: pre.map .plain ++ [.plain h]) r d post v
          refine ⟨_, _, by omega, h₁.trans (by simpa using h₃), ?_⟩
          refine ⟨pre ++ [h], post ++ [default], ?_, ?_, ?_⟩
          · simp [Tape.move, blank]
          · simp [Tape.move]
          · simp [Tape.move, listBlank_mk_append_default]
      | left =>
        have h₁ := SimReach.single (M := M) (w := w) (next_left hM (u ++ .lt :: pre.map .plain)
          (List.map Cell.plain post ++ Cell.rt :: v)) rfl
        induction pre using List.reverseRecOn with
        | nil =>
          have h₂ := SimReach.single (M := M) (w := w)
            (next_edgeU M w r u (.plain h :: (List.map Cell.plain post ++ Cell.rt :: v))) rfl
          have h₃ := round M w (u ++ [.lt]) r default (h :: post) v
          refine ⟨_, _, by omega, (h₁.trans (by simpa using h₂)).trans (by simpa [blank] using h₃), ?_⟩
          refine ⟨[], h :: post ++ [default], ?_, ?_, ?_⟩
          · simp [Tape.move]
          · simp [Tape.move]
          · simp [Tape.move]
        | append_singleton pre c _ =>
          have h₂ := SimReach.single (M := M) (w := w)
            (next_shiftU M w r c (u ++ .lt :: pre.map .plain)
              (.plain h :: (List.map Cell.plain post ++ Cell.rt :: v))) rfl
          have h₃ := round M w (u ++ .lt :: pre.map .plain) r c (h :: post) v
          refine ⟨_, _, by omega, (h₁.trans (by simpa using h₂)).trans (by simpa using h₃), ?_⟩
          refine ⟨pre, h :: post ++ [default], ?_, ?_, ?_⟩
          · simp [Tape.move, blank]
          · simp [Tape.move]
          · simp [Tape.move]

/-! ### Cleanup -/

theorem carry_sweep (v : List (Cell Γ)) :
    ∀ (β : List Γ) (α : List (Cell Γ)),
      (rules M w).nextO^[β.length] (some (α, .C, β.map .plain ++ v)) =
        some (α ++ β.map .plain, .C, v)
  | [], α => by simp
  | c :: β, α => by
    rw [List.length_cons, Function.iterate_succ_apply, Rules.nextO_some, List.map_cons,
      List.cons_append, show (Cell.plain c : Cell Γ) = sym false c from rfl, next_carry]
    simpa using carry_sweep v β (α ++ [sym false c])

theorem erase_sweep (α v : List (Cell Γ)) :
    ∀ β : List Γ,
      (rules M w).nextO^[β.length] (some (α ++ β.map .plain, .E, v)) = some (α, .E, v) := by
  intro β
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β c ih =>
    rw [List.length_append, List.length_singleton, Function.iterate_succ_apply, Rules.nextO_some,
      List.map_append, List.map_singleton, ← List.append_assoc,
      show (Cell.plain c : Cell Γ) = sym false c from rfl, next_erase]
    exact ih

theorem iter_comp {a b : ℕ} {x y z : Vertex (Cell Γ) (Ctrl Λ)}
    (h₁ : (rules M w).nextO^[a] (some x) = some y) (h₂ : (rules M w).nextO^[b] (some y) = some z) :
    (rules M w).nextO^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

/-- **Cleanup.** After a halt, `C` reaches the right delimiter, `E` erases the tape back to the left
delimiter, and the last rule restores the initial word. -/
theorem cleanup_sim {u v : List (Cell Γ)} {cfg : TM0.Cfg Γ Λ} {x : Vertex (Cell Γ) (Ctrl Λ)}
    (hx : Enc u v cfg x) (hstep : TM0.step M cfg = none) :
    ∃ k, 0 < k ∧
      (rules M w).nextO^[k] (some x) = some (u ++ [.lt], .H default, input w ++ .rt :: v) := by
  obtain ⟨q, T⟩ := cfg
  obtain ⟨pre, post, rfl, -, -⟩ := hx
  have hM : M q T.head = none := by
    simp only [TM0.step, Option.map_eq_none_iff] at hstep
    exact hstep
  have s₁ : (rules M w).nextO^[1] (some (u ++ Cell.lt :: pre.map Cell.plain, Ctrl.H q,
      Cell.plain T.head :: (post.map Cell.plain ++ Cell.rt :: v))) =
      some (u ++ Cell.lt :: pre.map Cell.plain, Ctrl.C,
        Cell.plain T.head :: (post.map Cell.plain ++ Cell.rt :: v)) :=
    next_halt (w := w) hM (u ++ Cell.lt :: pre.map Cell.plain) (post.map Cell.plain ++ Cell.rt :: v)
  have s₂ := carry_sweep M w (.rt :: v) (T.head :: post) (u ++ .lt :: pre.map .plain)
  simp only [List.map_cons, List.cons_append, List.length_cons] at s₂
  have hα : u ++ Cell.lt :: pre.map Cell.plain ++ Cell.plain T.head :: post.map Cell.plain =
      u ++ [.lt] ++ (pre ++ T.head :: post).map .plain := by simp
  rw [hα] at s₂
  have s₃ : (rules M w).nextO^[1] (some (u ++ [.lt] ++ (pre ++ T.head :: post).map .plain,
      Ctrl.C, .rt :: v)) =
      some (u ++ [.lt] ++ (pre ++ T.head :: post).map .plain, .E, .rt :: v) :=
    next_drop M w _ v
  have s₄ := erase_sweep M w (u ++ [.lt]) (.rt :: v) (pre ++ T.head :: post)
  have s₅ : (rules M w).nextO^[1] (some (u ++ [.lt], Ctrl.E, .rt :: v)) =
      some (u ++ [.lt], .H default, input w ++ .rt :: v) :=
    next_reset M w u (.rt :: v)
  exact ⟨_, by omega, iter_comp M w (iter_comp M w (iter_comp M w (iter_comp M w s₁ s₂) s₃) s₄) s₅⟩

/-! ### Halting and periodicity of the initial word -/

/-- The machine halts on the input `w`. -/
def Halts (M : TM0.Machine Γ Λ) (w : List Γ) : Prop :=
  ∃ cfg, TM0.Reaches M (TM0.init w) cfg ∧ TM0.step M cfg = none

/-- The initial word `L H_{q₀} w R`. -/
def start (w : List Γ) : Vertex (Cell Γ) (Ctrl Λ) := ([.lt], .H default, input w ++ [.rt])

theorem reach_of_reaches {u v : List (Cell Γ)} {cfg : TM0.Cfg Γ Λ} {x : Vertex (Cell Γ) (Ctrl Λ)}
    (hx : Enc u v cfg x) {cfg' : TM0.Cfg Γ Λ} (h : TM0.Reaches M cfg cfg') :
    ∃ k y, SimReach M w x y k ∧ Enc u v cfg' y := by
  induction h with
  | refl => exact ⟨0, x, SimReach.refl x, hx⟩
  | tail _ hstep ih =>
    obtain ⟨k, y, hk, hy⟩ := ih
    obtain ⟨k', y', -, hk', hy'⟩ := step_sim M w hy hstep
    exact ⟨k + k', y', hk.trans hk', hy'⟩

/-- **Halting closes a cycle.** If the machine halts on `w`, the initial word returns to itself. -/
theorem periodic_of_halts (h : Halts M w) : (rules M w).Periodic (start w) := by
  obtain ⟨cfg, hreach, hhalt⟩ := h
  have hx : Enc [] [] (TM0.init w : TM0.Cfg Γ Λ) (start w) := by
    simpa [start] using enc_init (Λ := Λ) w [] []
  obtain ⟨k, y, hk, hy⟩ := reach_of_reaches M w hx hreach
  obtain ⟨k', hk', hcycle⟩ := cleanup_sim M w hy hhalt
  refine ⟨k' + k, by omega, ?_⟩
  rw [Function.iterate_add_apply, hk.1, hcycle]
  simp [start]

/-- **Only halting reaches the cleanup.** If the run from an encoding of `cfg` reaches a cleanup
letter, the machine halts from `cfg`. -/
theorem halts_of_cleanup :
    ∀ (n : ℕ) {u v : List (Cell Γ)} {cfg : TM0.Cfg Γ Λ} {x : Vertex (Cell Γ) (Ctrl Λ)},
      Enc u v cfg x →
      (∃ z, (rules M w).nextO^[n] (some x) = some z ∧ z.2.1.cleanup = true) →
      ∃ cfg', TM0.Reaches M cfg cfg' ∧ TM0.step M cfg' = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v cfg x hx hz
    cases hstep : TM0.step M cfg with
    | none => exact ⟨cfg, Relation.ReflTransGen.refl, hstep⟩
    | some cfg' =>
      obtain ⟨k, y, hk, hxy, hy⟩ := step_sim M w hx hstep
      obtain ⟨z, hz, hzc⟩ := hz
      by_cases hnk : n < k
      · obtain ⟨z', hz', hz'c⟩ := hxy.2 n hnk
        rw [hz] at hz'
        cases hz'
        rw [hzc] at hz'c
        exact absurd hz'c (by simp)
      · have hz' : (rules M w).nextO^[n - k] (some y) = some z := by
          rw [← hxy.1, ← Function.iterate_add_apply, Nat.sub_add_cancel (not_lt.mp hnk), hz]
        obtain ⟨cfg'', hreach, hhalt⟩ := ih (n - k) (by omega) hy ⟨z, hz', hzc⟩
        exact ⟨cfg'', Relation.ReflTransGen.head (by rw [hstep]; rfl) hreach, hhalt⟩

end Machine

end SubalgebraFreeness
