module

public import ThreeWordCodes.Certificate

/-! # Characteristic series, unambiguous cuts, and tree polynomials -/

@[expose] public section
namespace ThreeWordCodes.WordSeries
open scoped ThreeWordCodes.WordSeries
variable {A : Type*}

noncomputable def indicator (S : Finset (Word A)) : Series A :=
  fun w => by classical exact if w ∈ S then 1 else 0

@[simp] theorem indicator_pos (S : Finset (Word A)) (w : Word A) :
    0 < indicator S w ↔ w ∈ S := by classical by_cases h : w ∈ S <;> simp [indicator, h]

theorem indicator_le (S : Finset (Word A)) (w : Word A) : indicator S w ≤ 1 := by
  classical
  by_cases h : w ∈ S <;> simp [indicator, h]

theorem indicator_of_mem {S : Finset (Word A)} {w : Word A} (hw : w ∈ S) : indicator S w = 1 := by
  classical simp [indicator, hw]

noncomputable def joinSets (S T : Finset (Word A)) : Finset (Word A) := by
  classical exact (S ×ˢ T).image (fun z => z.1 ++ z.2)

@[simp] theorem mem_joinSets {S T : Finset (Word A)} {w : Word A} :
    w ∈ joinSets S T ↔ ∃ u ∈ S, ∃ v ∈ T, u ++ v = w := by
  classical
  simp only [joinSets, Finset.mem_image, Finset.mem_product, Prod.exists]
  grind

/-- A product of two characteristic series still has coefficients at most one
when every pair of positive cuts has the same left part. -/
theorem conv_le_one_of_unique {f g : Series A} {w : Word A}
    (hf : ∀ x, f x ≤ 1) (hg : ∀ x, g x ≤ 1)
    (unique : ∀ u v x y, u ++ v = w → x ++ y = w →
      0 < f u → 0 < g v → 0 < f x → 0 < g y → u = x) : (f ⋆ g) w ≤ 1 := by
  induction w generalizing f with
  | nil => simpa only [conv_nil] using Nat.mul_le_mul (hf []) (hg [])
  | cons a w ih =>
    have tail := ih (f := shift a f) (fun u => hf (a :: u)) (by
      intro u v x y e e' hu hv hx hy
      have := unique (a::u) v (a::x) y (congrArg (List.cons a) e) (congrArg (List.cons a) e')
        hu hv hx hy
      exact (List.cons.inj this).2)
    have head := Nat.mul_le_mul (hf []) (hg (a :: w))
    rw [conv_cons]
    by_cases hz : 0 < (shift a f ⋆ g) w
    · obtain ⟨x,y,e,hx,hy⟩ := conv_pos.mp hz
      by_cases h : 0 < f [] * g (a::w)
      · have bad := unique [] (a::w) (a::x) y rfl (congrArg (List.cons a) e)
          (Nat.pos_of_mul_pos_right h) (Nat.pos_of_mul_pos_left h) hx hy
        contradiction
      · omega
    · omega

theorem indicator_product {S T : Finset (Word A)}
    (uniq : Function.Injective (fun z : ↥S × ↥T => z.1.val ++ z.2.val)) :
    (indicator S ⋆ indicator T) = indicator (joinSets S T) := by
  funext w
  have small := conv_le_one_of_unique (w := w) (indicator_le S) (indicator_le T) (by
    intro u v x y e e' hu hv hx hy
    have ke := uniq (a₁ := (⟨u, (indicator_pos _ _).mp hu⟩, ⟨v, (indicator_pos _ _).mp hv⟩))
      (a₂ := (⟨x, (indicator_pos _ _).mp hx⟩, ⟨y, (indicator_pos _ _).mp hy⟩)) (e.trans e'.symm)
    exact congrArg (fun z : ↥S × ↥T => z.1.val) ke)
  have positive : 0 < (indicator S ⋆ indicator T) w ↔ w ∈ joinSets S T := by
    rw [conv_pos, mem_joinSets]
    simp only [indicator_pos]
    grind
  classical
  change _ = if w ∈ joinSets S T then 1 else 0
  split
  next h => exact le_antisymm small (positive.mpr h)
  next h => exact Nat.eq_zero_of_not_pos (fun k => h (positive.mp k))

noncomputable def alphabetWords (A : Type*) [Fintype A] : Finset (Word A) := by
  classical exact Finset.univ.image (fun a : A => [a])

@[simp] theorem mem_alphabetWords [Fintype A] (w : Word A) :
    w ∈ alphabetWords A ↔ ∃ a, w = [a] := by classical simp [alphabetWords, eq_comm]

theorem alphabet_indicator [Fintype A] : indicator (alphabetWords A) = (letters : Series A) := by
  funext w
  cases w with
  | nil => simp [indicator, letters]
  | cons a w => cases w <;> simp [indicator, letters, epsilon]

theorem tree_series [Fintype A] [DecidableEq A] {I : Finset (Word A)} (hI : RootedPrefixClosed I) :
    indicator (leaves I) + indicator I = epsilon + (indicator I ⋆ letters) := by
  have inj : Function.Injective (fun z : ↥I × ↥(alphabetWords A) => z.1.val ++ z.2.val) := by
    rintro ⟨u, ⟨v, hv⟩⟩ ⟨x, ⟨y, hy⟩⟩ eqn
    obtain ⟨a,rfl⟩ := (mem_alphabetWords _).mp hv
    obtain ⟨b,rfl⟩ := (mem_alphabetWords _).mp hy
    obtain ⟨p,q⟩ := List.append_inj' eqn (by rfl)
    exact Prod.ext (Subtype.ext p) (Subtype.ext q)
  rw [← alphabet_indicator, indicator_product inj]
  funext w
  have child : w ∈ joinSets I (alphabetWords A) ↔ IsChild I w := by simp [IsChild]
  by_cases z : w = []
  · subst w
    simp [indicator, hI.root, mem_leaves, child, epsilon, nil_not_child]
  · have ep : epsilon w = 0 := by cases w <;> simp_all [epsilon]
    by_cases hi : w ∈ I
    · simp [indicator, child, hi, ep, mem_leaves, child_of_internal hI hi z]
    · by_cases hc : IsChild I w <;> simp [indicator, hi, ep, mem_leaves, child, hc]

theorem finite_conv_support {f g : Series A} (hf : Set.Finite {w | 0 < f w})
    (hg : Set.Finite {w | 0 < g w}) : Set.Finite {w | 0 < (f ⋆ g) w} := by
  apply ((hf.prod hg).image (fun z : Word A × Word A => z.1 ++ z.2)).subset
  rintro w h
  obtain ⟨u,v,e,hu,hv⟩ := conv_pos.mp h
  exact ⟨(u,v), ⟨hu,hv⟩,e⟩

theorem finite_indicator_support (S : Finset (Word A)) : Set.Finite {w | 0 < indicator S w} := by
  simp

end ThreeWordCodes.WordSeries
