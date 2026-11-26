module

public import NonfreeBinaryFactor.Submonoid
public import ThreeWordCodes.BorderWords

/-! # The unique five-factor decomposition

The two cuts on the right are the initial-power cuts on the reversed word.
Appending a right-hand power preserves and reflects the left boundary test. -/

@[expose] public section
namespace NonfreeBinaryFactor

open ThreeWordCodes (wordPow wordPow_succ)

/-- Reinsert the two terminal powers. -/
def appendRight (v : BinaryWord) (k l : ℕ) : BinaryWord :=
  (v ++ wordPow [a] k) ++ wordPow [a,a,b,b] l

private theorem reverse_appendRight (v : BinaryWord) (k l : ℕ) :
    (appendRight v k l).reverse = prepend [b,b,a,a] a l k v.reverse := by
  simp only [appendRight, prepend, List.reverse_append, ThreeWordCodes.Border.reverse_pow]
  rfl

private theorem exists_right (w : BinaryWord) :
    ∃ k l v, RightNormal v ∧ appendRight v k l = w := by
  obtain ⟨l, k, t, ht, he⟩ := exists_prepend (h := b) (c := a) [b,a,a] w.reverse
  refine ⟨k, l, t.reverse, by simpa [RightNormal] using ht, List.reverse_inj.mp ?_⟩
  rw [reverse_appendRight, List.reverse_reverse, he]

private theorem right_unique {u v : BinaryWord} {k l k' l' : ℕ}
    (hu : RightNormal u) (hv : RightNormal v) (he : appendRight u k l = appendRight v k' l') :
    k = k' ∧ l = l' ∧ u = v := by
  have rev := congrArg List.reverse he
  rw [reverse_appendRight, reverse_appendRight] at rev
  obtain ⟨hl, hk, eq⟩ := prepend_unique (show b ≠ a by decide) hu hv rev
  exact ⟨hk, hl, List.reverse_inj.mp eq⟩

/-- A prefix test for a nonempty pattern extends from its tail: if the
candidate word is empty, the sole extra test is against the suffix itself. -/
private theorem cons_test {c : Bool} {p s : BinaryWord} (no : ¬ c :: p <+: s)
    (tail : ∀ w, p <+: w ++ s ↔ p <+: w) (w : BinaryWord) :
    c :: p <+: w ++ s ↔ c :: p <+: w := by
  cases w with
  | nil => simp [no]
  | cons d w => simp [tail]

private theorem left_append_safe {s : BinaryWord} (hb : ¬ [b] <+: s)
    (hab : ¬ [a,b] <+: s) (w : BinaryWord) : LeftNormal (w ++ s) ↔ LeftNormal w := by
  have keepB := cons_test hb (by simp)
  have keepAB := cons_test hab keepB
  have noBAB : ¬ [b,a,b] <+: s :=
    fun h => hb ((show [b] <+: [b,a,b] by decide).trans h)
  have keepBAB := cons_test noBAB keepAB
  simp only [LeftNormal, Reduced, keepB, keepAB, keepBAB]

private theorem left_append_power {p : BinaryWord}
    (step : ∀ w, LeftNormal (w ++ p) ↔ LeftNormal w) (w : BinaryWord) (n : ℕ) :
    LeftNormal (w ++ wordPow p n) ↔ LeftNormal w := by
  induction n with
  | zero => simp
  | succ n ih => rw [wordPow_succ, ← List.append_assoc, step, ih]

theorem left_appendRight (v : BinaryWord) (k l : ℕ) :
    LeftNormal (appendRight v k l) ↔ LeftNormal v := by
  have keepA := left_append_safe (s := [a]) (by decide) (by decide)
  have keepAABB := left_append_safe (s := [a,a,b,b]) (by decide) (by decide)
  exact (left_append_power keepAABB _ l).trans (left_append_power keepA v k)

/-- Multiply (ab)^i, b^j, the middle element, a^k and (aabb)^l, in that order. -/
def assemble (M : Submonoid (FreeMonoid Bool)) :
    ℕ × ℕ × M × ℕ × ℕ → FreeMonoid Bool
  | (i, j, m, k, l) =>
    (FreeMonoid.ofList [a,b])^i * (FreeMonoid.of b)^j * m.val *
      (FreeMonoid.of a)^k * (FreeMonoid.ofList [a,a,b,b])^l

private theorem assemble_toList {M : Submonoid (FreeMonoid Bool)} (i j : ℕ)
    (m : M) (k l : ℕ) :
    (assemble M (i,j,m,k,l)).toList = prepend [a,b] b i j (appendRight m.val.toList k l) := by
  simp only [assemble, prepend, appendRight, wordPow, FreeMonoid.toList_mul, List.append_assoc]
  rfl

theorem assemble_bijective : Function.Bijective (assemble middleSubmonoid) := by
  constructor
  · rintro ⟨i, j, m, k, l⟩ ⟨i', j', m', k', l'⟩ eq
    have same := congrArg FreeMonoid.toList eq
    rw [assemble_toList, assemble_toList] at same
    have hm : Middle m.val.toList := m.property
    have hm' : Middle m'.val.toList := m'.property
    obtain ⟨rfl, rfl, rest⟩ := prepend_unique (show a ≠ b by decide)
      ((left_appendRight _ _ _).mpr hm.1) ((left_appendRight _ _ _).mpr hm'.1) same
    obtain ⟨rfl, rfl, words⟩ := right_unique hm.2 hm'.2 rest
    have em : m = m' := Subtype.ext (FreeMonoid.ext words)
    rw [em]
  · intro w
    obtain ⟨i, j, u, hu, hleft⟩ := exists_prepend (h := a) (c := b) [b] w.toList
    obtain ⟨k, l, v, hv, hright⟩ := exists_right u
    have left : LeftNormal (appendRight v k l) := hright ▸ hu
    let m : middleSubmonoid := ⟨FreeMonoid.ofList v, (left_appendRight _ _ _).mp left, hv⟩
    refine ⟨(i,j,m,k,l), FreeMonoid.ext ?_⟩
    rw [assemble_toList]
    change prepend [a,b] b i j (appendRight v k l) = w.toList
    rw [hright, hleft]

end NonfreeBinaryFactor
