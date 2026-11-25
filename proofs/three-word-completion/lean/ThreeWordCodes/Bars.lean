module

public import ThreeWordCodes.LetterSuffix

/-! # Recoding a binary text at each marker

The bar b a^n is one symbol of an infinite auxiliary alphabet. This alphabet
can be encoded back into binary words with any specified bar as a single letter.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {I : Type*}

private def reverseBar (n : ℕ) : Word Bool := run n ++ [b]
private def bar (n : ℕ) : Word Bool := b :: run n

private theorem reverse_bar_code : NamedCode reverseBar := by
  have detect (m n : ℕ) (p : reverseBar m <+: reverseBar n) : m=n :=
    (marked_prefix p).1
  refine (namedCode_iff_range _).mpr ⟨fun x y eqn => detect _ _ (by rw [eqn]),?_⟩
  have prefixFree : InformationTheory.IsPrefixFree (Set.range reverseBar) := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hp
    exact congrArg reverseBar (detect x y hp)
  exact prefixFree.isUniquelyDecodable (by rintro ⟨x,eqn⟩; simp [reverseBar] at eqn)

private theorem bar_code : NamedCode bar := by
  have e : (fun n => (reverseBar n).reverse) = bar := by
    funext n
    simp [reverseBar,bar,run]
  exact e ▸ reverse_bar_code.reverse

private theorem bar_reads (g : List ℕ) (j : ℕ) :
    spell bar (g ++ [j]) = mixed 0 g j := by
  induction g with
  | nil => simp [bar,mixed,gapTail,run]
  | cons c g ih =>
    change bar c ++ spell bar (g ++ [j]) = _
    simp [ih,bar,mixed,gapTail,run]

/-- If all entries begin with b and one is b a^q, every equation is preserved
by a binary realization in which this distinguished entry is one letter. -/
theorem bar_letter_realization (v : I → Word Bool) (k : I) (q : ℕ)
    (start : ∀ i, ∃ g j, v i = mixed 0 g j) (one : v k = b :: run q) :
    HasLetterRealization v := by
  classical
  choose gaps last repr using start
  let s (i : I) := gaps i ++ [last i]
  have er : (fun i => spell bar (s i)) = v := funext fun i => (bar_reads ..).trans (repr i).symm
  have ek : s k = [q] := bar_code (show spell bar (s k) = spell bar [q] by
    rw [congrFun er,one]; simp [bar])
  let idx (n : ℕ) := if n=q then 0 else n+1
  have inj : Function.Injective idx := by
    intro x y eqn
    by_cases hx : x=q <;> by_cases hy : y=q <;> simp_all [idx]
  let enc (n : ℕ) := reverseBar (idx n)
  have nc : NamedCode enc := by
    intro x y eqn
    have maps (w : Word ℕ) : spell enc w = spell reverseBar (w.map idx) := by
      induction w with
      | nil => rfl
      | cons n w ih => exact congrArg (enc n ++ ·) ih
    exact List.map_injective_iff.mpr inj (reverse_bar_code ((maps x).symm.trans (eqn.trans (maps y))))
  let d (i : I) := spell enc (s i)
  have first : SameEquations s v := er ▸ bar_code.preserves_equations s
  exact ⟨d,first.symm.trans (nc.preserves_equations s),k,b,by simp [d,ek,enc,reverseBar,idx,run]⟩

/-- The common-initial-margin case n=1 in the lengthening proof of Lemma 4. -/
theorem single_bar_lengthening (g : List ℕ) (j q : ℕ) :
    HasLetterRealization (addToken (pair (mixed 0 g j) (mixed 0 g (j+1))) (mixed 0 [] q)) := by
  apply bar_letter_realization _ none q _ rfl
  rintro (_ | (_ | _)) <;> exact ⟨_,_,rfl⟩

end ThreeWordCodes.BinaryGaps
