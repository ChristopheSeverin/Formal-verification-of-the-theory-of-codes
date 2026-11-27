module

public import SubalgebraFreeness.Universal
public import SubalgebraFreeness.Encoding
public import Mathlib.Computability.Primrec.List

/-! # The reduction from the halting problem

For the universal machine and the input `m`, the rules of `Machine.rules` give a finite set of
words and differences of words in `K⟨a, b⟩`. The generated subalgebra is free exactly when the
machine does not halt on `m` (`free_iff_not_halts`).

Only the reset rule `L E → L H_{q₀} w` depends on `m`, through the binary digits of `m` written
on the tape. The list of generators is a fixed list followed by this rule, and the map from
`m` to the last specification is primitive recursive (`resetSpec_primrec`). -/

@[expose] public noncomputable section
namespace SubalgebraFreeness

universe u

open Turing Machine

/-! ### Binary digits -/

/-- The binary digits of a natural number, least significant first. -/
def bits (n : ℕ) : List Bool :=
  if n = 0 then [] else n.bodd :: bits n.div2
termination_by n
decreasing_by rw [Nat.div2_val]; omega

theorem bits_zero : bits 0 = [] := by rw [bits]; simp

theorem bits_of_ne_zero {n : ℕ} (hn : n ≠ 0) : bits n = n.bodd :: bits n.div2 := by
  rw [bits, ite_eq_right hn]

theorem bits_primrec : Primrec bits := by
  have hg : Primrec₂ fun (_ : Unit) (L : List (List Bool)) =>
      some (Nat.casesOn (motive := fun _ => List Bool) L.length []
        fun k => (k + 1).bodd :: L.getD (k + 1).div2 []) :=
    (Primrec.option_some.comp (Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
      (Primrec.const []) ((Primrec.list_cons.comp (Primrec.nat_bodd.comp
        (Primrec.succ.comp Primrec.snd)) ((Primrec.list_getD []).comp (Primrec.snd.comp
          Primrec.fst) (Primrec.nat_div2.comp (Primrec.succ.comp Primrec.snd)))).to₂))).to₂
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => bits n) hg fun _ n => by
    cases n with
    | zero => simp [bits_zero]
    | succ k =>
      have hlt : (k + 1).div2 < k + 1 := by rw [Nat.div2_val]; omega
      simp only [List.length_map, List.length_range]
      show some ((k + 1).bodd :: ((List.range (k + 1)).map fun n => bits n).getD (k + 1).div2 []) =
        some (bits (k + 1))
      rw [bits_of_ne_zero (Nat.succ_ne_zero k), List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hlt]
      rfl
  exact this.comp (Primrec.const ()) Primrec.id

open PartrecToTM2 in
theorem trNum_bit1 (x : Num) : trNum (Num.bit1 x) = Γ'.bit1 :: trNum x := by
  cases x <;> rfl

open PartrecToTM2 in
theorem trNum_bit0 {x : Num} (hx : x ≠ 0) : trNum (Num.bit0 x) = Γ'.bit0 :: trNum x := by
  cases x with
  | zero => exact absurd rfl hx
  | pos p => rfl

open PartrecToTM2 in
/-- Mathlib's tape encoding of a number lists its binary digits. -/
theorem trNat_eq_bits (n : ℕ) : trNat n = (bits n).map fun b => cond b Γ'.bit1 Γ'.bit0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [bits_zero]
    · rw [bits_of_ne_zero hn, List.map_cons, ← ih n.div2 (by rw [Nat.div2_val]; omega)]
      have hbit := Nat.bit_bodd_div2 n
      rw [trNat, ← Num.ofNat'_eq, ← hbit, Num.ofNat'_bit, trNat, ← Num.ofNat'_eq,
        Nat.bodd_bit, Nat.div2_bit]
      cases hb : n.bodd with
      | true => exact trNum_bit1 _
      | false =>
        apply trNum_bit0
        rw [Num.ofNat'_eq]
        intro h0
        have hd : n.div2 = 0 := by
          have := congrArg (fun x : Num => (x : ℕ)) h0
          simpa using this
        apply hn
        rw [← Nat.bit_bodd_div2 n, hb, hd]
        rfl

/-! ### The generators for the universal machine -/

namespace Reduction

open Universal

instance : DecidableEq Sym := Classical.decEq _

/-- The letters of `D ⊕ S`. -/
abbrev Letter : Type := Cell Sym ⊕ Ctrl State

instance : DecidableEq Letter := Classical.decEq _

/-- A numbering of the letters, used for the block code `cⱼ ↦ aʲ b`. -/
def idx (x : Letter) : ℕ := (Fintype.equivFin Letter x : ℕ)

theorem idx_injective : Function.Injective idx := fun _ _ h =>
  (Fintype.equivFin Letter).injective (Fin.ext h)

/-- The rules for the input `m`. -/
def rulesFor (m : ℕ) : Rules (Cell Sym) (Ctrl State) (Rule Sym State) :=
  Machine.rules machine (Universal.input m)

/-- The specification of a letter of `D`. -/
def letterSpec (d : Cell Sym) : WordSpec := .inl (code idx [.inl d])

/-- The specification `ℓᵢ - rᵢ` of a rule for the input `m`. -/
def ruleSpec (m : ℕ) (i : Rule Sym State) : WordSpec :=
  .inr (code idx (vword (lhs i)).toList, code idx (vword ((rulesFor m).rhs i)).toList)

/-- The specifications that do not depend on the input: the letters of `D` and every rule
except the reset. -/
def fixedSpecs : List WordSpec :=
  (Finset.univ : Finset (Cell Sym)).toList.map letterSpec ++
    ((Finset.univ : Finset (Rule Sym State)).toList.filter (· ≠ Rule.reset)).map (ruleSpec 0)

/-- The reset rule, the only specification depending on the input. -/
def resetSpec (m : ℕ) : WordSpec := ruleSpec m Rule.reset

/-- All the generators for the input `m`. -/
def specs (m : ℕ) : List WordSpec := fixedSpecs ++ [resetSpec m]

theorem rhs_eq_of_ne_reset {i : Rule Sym State} (hi : i ≠ Rule.reset) (m m' : ℕ) :
    (rulesFor m).rhs i = (rulesFor m').rhs i := by
  cases i <;> first | exact absurd rfl hi | rfl

variable (K : Type*) [Field K]

theorem eval_letterSpec (d : Cell Sym) :
    WordSpec.eval K (letterSpec d) = embed K idx ((rulesFor 0).gen K (.inl d)) := by
  rw [Rules.gen, show (letter (Sum.inl d) : Poly K Letter) = mono (FreeMonoid.of (Sum.inl d)) from rfl,
    embed_mono]
  rfl

theorem eval_ruleSpec (m : ℕ) (i : Rule Sym State) :
    WordSpec.eval K (ruleSpec m i) = embed K idx ((rulesFor m).gen K (.inr i)) := by
  rw [Rules.gen, map_sub, embed_mono, embed_mono]
  rfl

theorem gen_inl (m m' : ℕ) (d : Cell Sym) :
    (rulesFor m).gen K (.inl d) = (rulesFor m').gen K (.inl d) := rfl

theorem specs_eval (m : ℕ) :
    {p | ∃ y ∈ specs m, WordSpec.eval K y = p} = embed K idx '' Set.range ((rulesFor m).gen K) := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [specs, fixedSpecs, List.mem_append, List.mem_map, List.mem_filter,
      Finset.mem_toList, Finset.mem_univ, true_and, List.mem_singleton] at hy
    rcases hy with (⟨d, rfl⟩ | ⟨i, hi, rfl⟩) | rfl
    · exact ⟨.inl d, by rw [eval_letterSpec, gen_inl]⟩
    · refine ⟨.inr i, ?_⟩
      rw [eval_ruleSpec, Rules.gen, Rules.gen, rhs_eq_of_ne_reset (by simpa using hi) 0 m]
      rfl
    · exact ⟨.inr Rule.reset, (eval_ruleSpec K m _).symm⟩
  · rintro ⟨x, rfl⟩
    rcases x with d | i
    · refine ⟨letterSpec d, ?_, by rw [eval_letterSpec, gen_inl]⟩
      simp [specs, fixedSpecs]
    · by_cases hi : i = Rule.reset
      · subst hi
        exact ⟨resetSpec m, by simp [specs], eval_ruleSpec K m _⟩
      · refine ⟨ruleSpec 0 i, ?_, ?_⟩
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr
            ⟨i, List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ _), by simpa using hi⟩,
              rfl⟩))))
        · rw [eval_ruleSpec, Rules.gen, Rules.gen, rhs_eq_of_ne_reset hi 0 m]
          rfl

/-- The subalgebra generated by the specifications is the algebra `A` of the rules. -/
def specsEquiv (m : ℕ) : generated K (specs m) ≃ₐ[K] ((rulesFor m).pres K).range :=
  generatedEquiv idx_injective _ _ (specs_eval K m)

/-- **The subalgebra is free exactly when the universal machine does not halt on `m`.** -/
theorem free_iff_not_halts (m : ℕ) :
    (∃ B : Type u, Nonempty (generated K (specs m) ≃ₐ[K] FreeAlgebra K B)) ↔
      ¬ Halts machine (Universal.input m) := by
  have hf := Machine.functional machine (Universal.input m)
  constructor
  · rintro ⟨B, ⟨e⟩⟩ hhalt
    obtain ⟨x, hx⟩ := (periodic_iff_halts machine (Universal.input m)).mpr hhalt
    have hbare : ∀ i, ¬ (rulesFor m).Periodic ((rulesFor m).lhs i) :=
      lhs_not_periodic machine (Universal.input m)
    exact ((rulesFor m).not_free_of_periodic (K := K) hf hbare hx).false
      (((specsEquiv K m).symm.trans e).trans FreeAlgebra.equivMonoidAlgebraFreeMonoid)
  · intro hhalt
    have hno : ∀ x, ¬ (rulesFor m).Periodic x := fun x hx =>
      hhalt ((periodic_iff_halts machine (Universal.input m)).mp ⟨x, hx⟩)
    obtain ⟨e⟩ := (rulesFor m).free_of_no_periodic (K := K) hf hno
    exact ⟨ULift.{u} (Cell Sym ⊕ Rule Sym State), ⟨((specsEquiv K m).trans e).trans
      ((MonoidAlgebra.domCongr K K (FreeMonoid.freeMonoidCongr Equiv.ulift.symm)).trans
        FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)⟩⟩

/-! ### Computability of the reset rule -/

/-- The block of a tape symbol. -/
def blk (γ : Sym) : List Bool := block (idx (.inl (.plain γ)))

open PartrecToTM2 in
/-- The tape symbol holding the stack symbol `a` on the main stack. -/
def onMain (a : Γ') : Sym := (false, Function.update (fun _ => none) K'.main (some a))

open PartrecToTM2 in
/-- The bottom cell of the tape, holding the end marker of the input list. -/
def cellCons : Sym := (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

open PartrecToTM2 in
theorem input_eq (m : ℕ) : Universal.input m = cellCons :: ((trNat m).reverse.map onMain) := by
  simp only [Universal.input, TM2to1.trInit, trList, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append]
  rfl

/-- The left delimiter and the initial control letter, coded. -/
def resetPrefix : List Bool := code idx [.inl .lt, .inr (.H default)]

theorem code_append (u v : List Letter) : code idx (u ++ v) = code idx u ++ code idx v :=
  List.flatMap_append

theorem code_map {β : Type*} (f : β → Letter) (l : List β) :
    code idx (l.map f) = l.flatMap fun a => block (idx (f a)) :=
  List.flatMap_map _ _ _

open PartrecToTM2 in
/-- The reset rule, written with the binary digits of the input. -/
theorem resetSpec_eq (m : ℕ) :
    resetSpec m = .inr (code idx (vword (lhs (Rule.reset : Rule Sym State))).toList,
      resetPrefix ++ (blk cellCons ++
        (bits m).reverse.flatMap fun b => cond b (blk (onMain Γ'.bit1)) (blk (onMain Γ'.bit0)))) := by
  have hw : (vword ((rulesFor m).rhs Rule.reset)).toList =
      [.inl .lt, .inr (.H default)] ++ (Universal.input m).map fun γ => .inl (.plain γ) := by
    rw [input_eq]
    simp [vword, rulesFor, Machine.rules, rhs, Machine.input, input_eq]
  have hd : (Universal.input m).flatMap blk = blk cellCons ++
      (bits m).reverse.flatMap fun b => cond b (blk (onMain Γ'.bit1)) (blk (onMain Γ'.bit0)) := by
    rw [input_eq, List.flatMap_cons, trNat_eq_bits, ← List.map_reverse, List.map_map,
      List.flatMap_map]
    congr 2
    funext b
    cases b <;> rfl
  simp only [resetSpec, ruleSpec]
  rw [hw, code_append, ← resetPrefix, ← hd, code_map]
  rfl

theorem resetSpec_primrec : Primrec resetSpec := by
  refine (Primrec.sumInr.comp (Primrec.pair (Primrec.const _) (Primrec.list_append.comp
    (Primrec.const _) (Primrec.list_append.comp (Primrec.const _) (Primrec.list_flatMap
      (Primrec.list_reverse.comp bits_primrec)
      (Primrec.cond Primrec.snd (Primrec.const _) (Primrec.const _)).to₂))))).of_eq
    fun m => (resetSpec_eq m).symm

end Reduction

end SubalgebraFreeness
