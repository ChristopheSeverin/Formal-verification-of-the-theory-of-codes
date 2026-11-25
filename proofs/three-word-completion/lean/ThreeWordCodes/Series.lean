module

public import ThreeWordCodes.Definitions
public import Mathlib.Algebra.Group.Pi.Basic

/-! # Word coefficients of the certificate in Lemma 1

Convolution splits a word at every letter boundary. The proof uses natural
coefficients and makes the two cancellations in the formal-series argument explicit.
-/

@[expose] public section

namespace ThreeWordCodes
namespace WordSeries

abbrev Series (A : Type*) := Word A → ℕ
variable {A : Type*}

def epsilon : Series A
  | [] => 1
  | _ :: _ => 0

def letters : Series A
  | [] => 0
  | _ :: t => epsilon t

def shift (a : A) (f : Series A) : Series A := fun w => f (a :: w)

def conv (f g : Series A) : Word A → ℕ
  | [] => f [] * g []
  | a :: w => f [] * g (a :: w) + conv (shift a f) g w

scoped infixr:72 " ⋆ " => ThreeWordCodes.WordSeries.conv
open scoped ThreeWordCodes.WordSeries

@[simp] theorem conv_nil (f g : Series A) : (f ⋆ g) [] = f [] * g [] := rfl
theorem conv_cons (f g : Series A) (a : A) (w : Word A) :
    (f ⋆ g) (a :: w) = f [] * g (a :: w) + (shift a f ⋆ g) w := rfl

theorem add_conv (f g h : Series A) : ((f + g) ⋆ h) = (f ⋆ h) + (g ⋆ h) := by
  funext w
  induction w generalizing f g with
  | nil => simp [Nat.add_mul]
  | cons a w ih =>
    change (f [] + g []) * h (a :: w) + ((shift a f + shift a g) ⋆ h) w = _
    rw [ih]
    simp only [Pi.add_apply, conv_cons, Nat.add_mul]
    omega

theorem conv_add (f g h : Series A) : (f ⋆ (g + h)) = (f ⋆ g) + (f ⋆ h) := by
  funext w
  induction w generalizing f with
  | nil => simp [Nat.mul_add]
  | cons a w ih =>
    simp only [Pi.add_apply, conv_cons, Nat.mul_add, ih]
    omega

private theorem scale_conv (k : ℕ) (f h : Series A) :
    ((fun x => k * f x) ⋆ h) = fun x => k * (f ⋆ h) x := by
  funext w
  induction w generalizing f with
  | nil => simp [Nat.mul_assoc]
  | cons a w ih =>
    change k * f [] * h (a :: w) + ((fun x => k * shift a f x) ⋆ h) w = _
    rw [ih]
    simp only [conv_cons, Nat.mul_add, Nat.mul_assoc]

theorem conv_assoc (f g h : Series A) : ((f ⋆ g) ⋆ h) = (f ⋆ (g ⋆ h)) := by
  funext w
  induction w generalizing f g with
  | nil => simp [Nat.mul_assoc]
  | cons a w ih =>
    have hd : shift a (f ⋆ g) = (fun x => f [] * shift a g x) + (shift a f ⋆ g) := rfl
    simp only [conv_cons, conv_nil, hd, add_conv, scale_conv, Pi.add_apply, ih,
      Nat.mul_add, Nat.mul_assoc]
    omega

@[simp] theorem zero_conv (f : Series A) : ((0 : Series A) ⋆ f) = 0 := by
  funext w
  induction w with
  | nil => simp
  | cons a w ih =>
    change 0 * f (a :: w) + ((0 : Series A) ⋆ f) w = 0
    simpa using ih

@[simp] theorem epsilon_conv (f : Series A) : (epsilon ⋆ f) = f := by
  funext w
  cases w with
  | nil => simp [epsilon]
  | cons a w =>
    change 1 * f (a :: w) + ((0 : Series A) ⋆ f) w = _
    simp

@[simp] theorem conv_epsilon (f : Series A) : (f ⋆ epsilon) = f := by
  funext w
  induction w generalizing f with
  | nil => simp [epsilon]
  | cons a w ih =>
    change f [] * 0 + (shift a f ⋆ epsilon) w = _
    simpa [shift] using ih (shift a f)

theorem agree_conv {g h : Series A} (n : ℕ)
    (agree : ∀ u : Word A, u.length ≤ n → g u = h u) (f : Series A)
    (w : Word A) (hw : w.length ≤ n) : (f ⋆ g) w = (f ⋆ h) w := by
  induction w generalizing f with
  | nil => simp [agree [] (by simp)]
  | cons a w ih =>
    rw [conv_cons, conv_cons, agree _ hw, ih (shift a f) (by simpa using Nat.le_of_succ_le hw)]

/-- A series with constant term one can be cancelled on the left. -/
theorem cancel_left {p y z : Series A} (hp : p [] = 1) (h : (p ⋆ y) = (p ⋆ z)) : y = z := by
  funext w
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    cases w with
    | nil =>
      have e := congrFun h []
      simpa [hp] using e
    | cons a w =>
      have small : ∀ u : Word A, u.length ≤ w.length → y u = z u := by
        intro u hu
        exact ih u.length (by simp at len; omega) u rfl
      have e := congrFun h (a :: w)
      simpa only [conv_cons, hp, Nat.one_mul, agree_conv w.length small (shift a p) w le_rfl,
        Nat.add_right_cancel_iff] using e

theorem universal_of_fixed {t : Series A} (ht : t = epsilon + (letters ⋆ t)) :
    t = fun _ => 1 := by
  funext w
  induction w with
  | nil => simpa [epsilon, letters] using congrFun ht []
  | cons a w ih =>
    have e := congrFun ht (a :: w)
    change t (a :: w) = 0 + (0 * t (a :: w) + (epsilon ⋆ t) w) at e
    simpa [ih] using e

/-- Coefficient identity Q F* P = A*, with the Kleene series supplied by its unfolding.
The finite-support and parsing consequences are separate from this algebraic identity. -/
theorem certificate_identity {p q f star : Series A} (hp : p [] = 1)
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q))
    (unfoldStar : star = epsilon + (f ⋆ star)) :
    (q ⋆ (star ⋆ p)) = fun _ => 1 := by
  have he := congrArg (fun s : Series A => (s ⋆ star) ⋆ p) cert
  simp only [add_conv, epsilon_conv, conv_assoc] at he
  have hs := congrArg (fun s : Series A => s ⋆ p) unfoldStar
  simp only [add_conv, epsilon_conv, conv_assoc] at hs
  apply universal_of_fixed
  apply cancel_left hp
  rw [conv_add, conv_epsilon]
  funext w
  have e := congrFun he w
  have s := congrFun hs w
  simp only [Pi.add_apply] at e s ⊢
  omega

/-- The first n terms of the geometric series. -/
def approximant (f : Series A) : ℕ → Series A
  | 0 => 0
  | n + 1 => epsilon + (f ⋆ approximant f n)

private theorem successive {f : Series A} (hf : f [] = 0) (n : ℕ) (w : Word A)
    (hw : w.length < n) : approximant f (n+1) w = approximant f n w := by
  induction n generalizing w with
  | zero => omega
  | succ n ih =>
    cases w with
    | nil => simp [approximant, hf]
    | cons a w =>
      simp only [approximant, Pi.add_apply, conv_cons, hf, Nat.zero_mul, Nat.zero_add]
      exact congrArg (_ + ·) (agree_conv w.length
        (fun u hu => ih u (by simp at hw; omega)) (shift a f) w le_rfl)

private theorem stable {f : Series A} (hf : f [] = 0) {w : Word A} {n m : ℕ}
    (hw : w.length < n) (hnm : n ≤ m) : approximant f m w = approximant f n w := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => exact (successive hf m w (by omega)).trans ih

/-- Each coefficient only needs concatenations with at most as many tokens as letters. -/
def kleene (f : Series A) : Series A := fun w => approximant f (w.length + 1) w

theorem kleene_unfold {f : Series A} (hf : f [] = 0) :
    kleene f = epsilon + (f ⋆ kleene f) := by
  funext w
  have hn := successive hf (w.length+1) w (by omega)
  change approximant f (w.length+1) w = _
  rw [← hn]
  change epsilon w + (f ⋆ approximant f (w.length+1)) w = epsilon w + (f ⋆ kleene f) w
  exact congrArg (_ + ·) (agree_conv w.length
    (fun u hu => stable hf (by omega) (Nat.succ_le_succ hu)) f w le_rfl)

theorem proper_of_certificate {p q f : Series A} (hp : p [] = 1) (hq : q [] = 1)
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q)) : f [] = 0 := by
  simpa [hp, hq, epsilon, letters] using congrFun cert []

theorem certificate_series {p q f : Series A} (hp : p [] = 1) (hq : q [] = 1)
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q)) :
    (q ⋆ (kleene f ⋆ p)) = fun _ => 1 :=
  certificate_identity hp cert (kleene_unfold (proper_of_certificate hp hq cert))

@[simp] theorem kleene_nil (f : Series A) : kleene f [] = 1 := by
  simp [kleene, approximant, epsilon]

theorem cut_le (f g : Series A) (u v : Word A) : f u * g v ≤ (f ⋆ g) (u ++ v) := by
  induction u generalizing f with
  | nil =>
    cases v with
    | nil => exact le_rfl
    | cons a v => exact Nat.le_add_right _ _
  | cons a u ih =>
    exact (ih (shift a f)).trans (Nat.le_add_left _ _)

theorem conv_pos {f g : Series A} {w : Word A} :
    0 < (f ⋆ g) w ↔ ∃ u v, u ++ v = w ∧ 0 < f u ∧ 0 < g v := by
  constructor
  · induction w generalizing f with
    | nil =>
      intro h
      exact ⟨[], [], rfl, Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
    | cons a w ih =>
      intro h
      rw [conv_cons] at h
      by_cases hp : 0 < f [] * g (a :: w)
      · exact ⟨[], _, rfl, Nat.pos_of_mul_pos_right hp, Nat.pos_of_mul_pos_left hp⟩
      · obtain ⟨u, v, huv, hf, hg⟩ := ih (f := shift a f) (by omega)
        exact ⟨a :: u, v, congrArg (List.cons a) huv, hf, hg⟩
  · rintro ⟨u, v, rfl, hf, hg⟩
    exact (Nat.mul_pos hf hg).trans_le (cut_le f g u v)

/-- A convolution coefficient at most one determines both sides of a positive cut. -/
theorem cut_unique {f g : Series A} {u v x y : Word A}
    (h : u ++ v = x ++ y) (bound : (f ⋆ g) (u ++ v) ≤ 1)
    (hu : 0 < f u) (hv : 0 < g v) (hx : 0 < f x) (hy : 0 < g y) :
    u = x ∧ v = y := by
  induction u generalizing x f with
  | nil =>
    cases x with
    | nil => exact ⟨rfl, h⟩
    | cons a x =>
      change v = a :: (x ++ y) at h
      subst v
      have ht := (Nat.mul_pos hx hy).trans_le (cut_le (shift a f) g x y)
      have hh := Nat.mul_pos hu hv
      change f [] * g (a :: (x ++ y)) + (shift a f ⋆ g) (x ++ y) ≤ 1 at bound
      omega
  | cons a u ih =>
    cases x with
    | nil =>
      change a :: (u ++ v) = y at h
      subst y
      have ht := (Nat.mul_pos hu hv).trans_le (cut_le (shift a f) g u v)
      have hh := Nat.mul_pos hx hy
      change f [] * g (a :: (u ++ v)) + (shift a f ⋆ g) (u ++ v) ≤ 1 at bound
      omega
    | cons b x =>
      obtain ⟨rfl, he⟩ := List.cons.inj h
      change f [] * g (a :: (u ++ v)) + (shift a f ⋆ g) (u ++ v) ≤ 1 at bound
      obtain ⟨rfl, rfl⟩ := ih (f := shift a f) he (by omega) hu hx
      exact ⟨rfl, rfl⟩

end WordSeries
end ThreeWordCodes
