module

public import SubalgebraFreeness.Cycles
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.Halting

/-! # A universal machine with finitely many states

The manuscript encodes an arbitrary Turing machine. We fix one machine whose halting problem is
undecidable, so that only the input varies. Mathlib provides the chain

`Nat.Partrec.Code.eval` → `Turing.ToPartrec.Code` → `TM2` (`PartrecToTM2`) → `TM1` (`TM2to1`)
→ `TM0` (`TM1to0`),

with a finite set of reachable labels at each stage. We apply it to a code for
`m ↦ eval (ofNat Code m) 0`, and restrict the resulting `TM0` machine to its finite support.
`halts_iff` states that it halts on the encoding of `m` exactly when the program with code `m`
halts on `0`. -/

@[expose] public noncomputable section
namespace SubalgebraFreeness

open Turing

namespace Machine

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Halting is the domain of Mathlib's evaluation. -/
theorem halts_iff_eval_dom (M : TM0.Machine Γ Λ) (w : List Γ) :
    Halts M w ↔ (TM0.eval M w).Dom := by
  rw [TM0.eval, Part.dom_iff_mem]
  constructor
  · rintro ⟨cfg, hreach, hhalt⟩
    exact ⟨_, Part.mem_map _ (StateTransition.mem_eval.mpr ⟨hreach, hhalt⟩)⟩
  · rintro ⟨_, h⟩
    obtain ⟨cfg, hcfg, -⟩ := (Part.mem_map_iff _).mp h
    exact ⟨cfg, (StateTransition.mem_eval.mp hcfg).1, (StateTransition.mem_eval.mp hcfg).2⟩

/-- The states of a finite support containing the initial state, which stays the default. -/
def SuppState (S : Finset Λ) (_h : default ∈ S) : Type _ := {q // q ∈ S}

variable {S : Finset Λ} {h₀ : default ∈ S}

instance : Inhabited (SuppState S h₀) := ⟨⟨default, h₀⟩⟩

instance : Fintype (SuppState S h₀) := inferInstanceAs (Fintype {q // q ∈ S})

instance : DecidableEq (SuppState S h₀) := Classical.decEq _

/-- The identity on tape symbols, as a pointed map. -/
def idPointed : PointedMap Γ Γ := ⟨id, rfl⟩

variable (M : TM0.Machine Γ Λ) (hS : TM0.Supports M ↑S)

omit [Inhabited Γ] in
open Classical in
/-- Enter the support, sending outside states to the initial state. -/
def enterFun (h₀ : default ∈ S) (q : Λ) : SuppState S h₀ := if h : q ∈ S then ⟨q, h⟩ else ⟨default, h₀⟩

omit [Inhabited Γ] in
theorem enterFun_of_mem (h₀ : default ∈ S) {q : Λ} (hq : q ∈ S) : enterFun h₀ q = ⟨q, hq⟩ := by
  unfold enterFun
  exact dite_eq_left hq

/-- Enter the support, as a pointed map. -/
def enter : PointedMap Λ (SuppState S hS.1) := ⟨enterFun hS.1, enterFun_of_mem hS.1 hS.1⟩

/-- The machine restricted to a finite support. -/
def restrict : TM0.Machine Γ (SuppState S hS.1) :=
  TM0.Machine.map M idPointed idPointed (enter M hS) Subtype.val

theorem halts_restrict (w : List Γ) : Halts (restrict M hS) w ↔ Halts M w := by
  rw [halts_iff_eval_dom, halts_iff_eval_dom]
  have H := TM0.Machine.map_respects M idPointed idPointed (enter M hS) Subtype.val hS
    (fun _ => rfl) (fun q hq => by
      change (enterFun hS.1 q).1 = q
      rw [enterFun_of_mem hS.1 hq])
  have hinit : (TM0.init w : TM0.Cfg Γ Λ).q ∈ (S : Set Λ) ∧
      TM0.Cfg.map idPointed (enter M hS) (TM0.init w) = (TM0.init w : TM0.Cfg Γ (SuppState S hS.1)) := by
    refine ⟨hS.1, ?_⟩
    rw [TM0.map_init, show idPointed.f = (id : Γ → Γ) from rfl, List.map_id]
  exact StateTransition.tr_eval_dom H hinit

end Machine

namespace Universal

open PartrecToTM2 (Γ' K' Λ' Cont')

/-- The universal partial function: the program with code `m`, run on the input `0`. -/
def univ (m : ℕ) : Part ℕ := (Denumerable.ofNat Nat.Partrec.Code m).eval 0

theorem univ_partrec : Partrec univ :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)

theorem exists_ucode : ∃ c : ToPartrec.Code, ∀ m, c.eval [m] = pure <$> univ m := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr univ_partrec)
  exact ⟨c, fun m => hc ⟨[m], rfl⟩⟩

/-- A sequential program computing `univ`. -/
def ucode : ToPartrec.Code := exists_ucode.choose

theorem ucode_eval (m : ℕ) : ucode.eval [m] = pure <$> univ m := exists_ucode.choose_spec m

/-- The labels of Mathlib's `TM2` interpreter, starting at the program `ucode`. -/
def Lab : Type := Λ'

instance : Inhabited Lab := ⟨PartrecToTM2.trNormal ucode Cont'.halt⟩

instance : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, fun k => by cases k <;> simp⟩

/-- The `TM2` interpreter. -/
def M2 : Lab → TM2.Stmt (fun _ : K' => Γ') Lab (Option Γ') := PartrecToTM2.tr

/-- Its `TM1` emulation. -/
def M1 := TM2to1.tr M2

/-- Its `TM0` emulation. -/
def M0 : TM0.Machine (TM2to1.Γ' K' fun _ => Γ') (TM1to0.Λ' M1) := TM1to0.tr M1

/-- The tape alphabet of the universal machine. -/
abbrev Sym : Type := TM2to1.Γ' K' fun _ => Γ'

/-- The reachable labels at each stage. -/
def S2 : Finset Lab := PartrecToTM2.codeSupp ucode Cont'.halt

def S1 : Finset (TM2to1.Λ' K' (fun _ => Γ') Lab (Option Γ')) := TM2to1.trSupp M2 S2

def S0 : Finset (TM1to0.Λ' M1) := TM1to0.trStmts M1 S1

theorem supports2 : TM2.Supports M2 S2 := PartrecToTM2.tr_supports ucode Cont'.halt

theorem supports1 : TM1.Supports M1 S1 := TM2to1.tr_supports M2 supports2

theorem supports0 : TM0.Supports M0 ↑S0 := TM1to0.tr_supports M1 supports1

/-- The states of the universal machine. -/
abbrev State : Type := Machine.SuppState S0 supports0.1

/-- **The universal machine**, with finitely many states and tape symbols. -/
def machine : TM0.Machine Sym State := Machine.restrict M0 supports0

/-- The encoding of the input `m` on the tape. -/
def input (m : ℕ) : List Sym := TM2to1.trInit K'.main (PartrecToTM2.trList [m])

theorem init_eq (m : ℕ) :
    (TM2.init K'.main (PartrecToTM2.trList [m]) : TM2.Cfg (fun _ : K' => Γ') Lab (Option Γ')) =
      PartrecToTM2.init ucode [m] := by
  simp only [TM2.init, PartrecToTM2.init]
  congr 1
  funext k
  cases k <;> rfl

/-- **The universal machine halts on the encoding of `m` exactly when the program with code `m`
halts on the input `0`.** -/
theorem halts_iff (m : ℕ) :
    Machine.Halts machine (input m) ↔ ((Denumerable.ofNat Nat.Partrec.Code m).eval 0).Dom := by
  have h₁ : Machine.Halts machine (input m) ↔ (TM0.eval M0 (input m)).Dom := by
    rw [machine, Machine.halts_restrict, Machine.halts_iff_eval_dom]
  have h₂ : (TM0.eval M0 (input m)).Dom ↔ (TM1.eval M1 (input m)).Dom := by
    rw [M0, TM1to0.tr_eval]
  have h₃ : (TM1.eval M1 (input m)).Dom ↔
      (TM2.eval M2 K'.main (PartrecToTM2.trList [m])).Dom :=
    TM2to1.tr_eval_dom M2 K'.main (PartrecToTM2.trList [m])
  have h₄ : (TM2.eval M2 K'.main (PartrecToTM2.trList [m])).Dom ↔
      (StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init ucode [m])).Dom := by
    rw [TM2.eval, Part.map_Dom, init_eq]
    rfl
  have h₅ : (StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init ucode [m])).Dom ↔
      (univ m).Dom := by
    rw [PartrecToTM2.tr_eval, ucode_eval]
    simp
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end Universal

end SubalgebraFreeness
