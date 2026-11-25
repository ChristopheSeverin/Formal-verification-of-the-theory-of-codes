module

public import ThreeWordCodes.PalindromicBoundary
public import ThreeWordCodes.LetterSuffix

/-! # Equations on the signed basis in Proposition 7

On the abstract alphabet the letter a denotes x and the letter b denotes
the inverse of f. The positive pairs ba and ab denote the literal words ba
and ab. The change of generators is injective on the whole free group.
-/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

local notation "ga" => GroupCoordinates.a
local notation "gb" => GroupCoordinates.b

def literal (s : ℕ) (p : Word Bool) := c ++ spell (pair (x s) c) p ++ c.reverse
def abstractWord (p : Word Bool) := [b,a] ++ spell (pair [a] [b,a]) p ++ [a,b]

@[simp] theorem group_word_pow {A : Type*} (w : Word A) (n : ℕ) :
    groupWord (wordPow w n) = groupWord w ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ,groupWord_append,ih,pow_succ]

theorem f_then_c (s : ℕ) : pal s ++ c=x s := by simpa [x,pal] using enlarge s 1
theorem c_then_f (s : ℕ) : c.reverse ++ pal s=x s := by
  change [a,b] ++ (wordPow [a,b] s ++ [a]) = wordPow [a,b] (s+1) ++ [a]
  rw [wordPow_succ',List.append_assoc]

def basis (s : ℕ) : FreeGroup Bool →* FreeGroup Bool :=
  FreeGroup.lift (pairG (groupWord (x s)) (groupWord (pal s))⁻¹)
where pairG (u v : FreeGroup Bool) : Bool → FreeGroup Bool
        | false => u
        | true => v

@[simp] theorem basis_a (s : ℕ) : basis s ga=groupWord (x s) := by simp [basis,GroupCoordinates.a,basis.pairG]
@[simp] theorem basis_b (s : ℕ) : basis s gb=(groupWord (pal s))⁻¹ := by simp [basis,GroupCoordinates.b,basis.pairG]

private theorem group_c : groupWord c=gb*ga := by
  exact groupWord_append [b] [a]
private theorem group_cr : groupWord c.reverse=ga*gb := by
  exact groupWord_append [a] [b]

@[simp] theorem basis_ba (s : ℕ) : basis s (gb*ga)=groupWord c := by
  rw [map_mul,basis_b,basis_a,←f_then_c,groupWord_append,inv_mul_cancel_left]
@[simp] theorem basis_ab (s : ℕ) : basis s (ga*gb)=groupWord c.reverse := by
  rw [map_mul,basis_b,basis_a,←c_then_f,groupWord_append,mul_inv_cancel_right]

/-- Recover both abstract generators from their images. -/
theorem basis_injective (s : ℕ) : Function.Injective (basis s) := by
  let C := gb*ga
  let A := ga * (C^(s+1))⁻¹
  let G : FreeGroup Bool →* FreeGroup Bool := FreeGroup.lift (basis.pairG A (C*A⁻¹))
  have gA : G ga=A := by simp [G,GroupCoordinates.a,basis.pairG]
  have gB : G gb=C*A⁻¹ := by simp [G,GroupCoordinates.b,basis.pairG]
  have gc : G (groupWord c)=C := by rw [group_c,map_mul,gA,gB,inv_mul_cancel_right]
  have xc : x s=[a]++wordPow c (s+1) := by simpa [pal,x] using (enlarge 0 (s+1)).symm
  have gx : G (groupWord (x s))=ga := by
    rw [xc,groupWord_append,map_mul,group_word_pow,map_pow,gc,show groupWord [a]=ga from rfl,gA]
    simp [A]
  have gf : G (groupWord (pal s))*C=ga := by rw [←gc,←map_mul,←groupWord_append,f_then_c,gx]
  have inv : (G (groupWord (pal s)))⁻¹=gb := by
    have e := eq_mul_inv_of_mul_eq gf
    rw [e,mul_inv_rev,inv_inv]
    simp [C]
  have both : G.comp (basis s)=MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    cases i with
    | false => exact (congrArg G (basis_a s)).trans gx
    | true => change G (basis s gb)=gb; rw [basis_b,map_inv,inv]
  exact Function.LeftInverse.injective (fun u => congrArg (fun F : FreeGroup Bool →* FreeGroup Bool => F u) both)

theorem basis_middle (s : ℕ) (p : Word Bool) :
    basis s (groupWord (spell (pair [a] [b,a]) p))=groupWord (spell (pair (x s) c) p) := by
  induction p with
  | nil => simp
  | cons i p ih =>
    simp only [spell_cons,groupWord_append,map_mul,ih]
    congr 1
    cases i with
    | false => exact basis_a s
    | true => exact (congrArg (basis s) group_c).trans (basis_ba s)

theorem basis_third (s : ℕ) (p : Word Bool) :
    basis s (groupWord (abstractWord p))=groupWord (literal s p) := by
  simp only [abstractWord,literal,groupWord_append,map_mul,basis_middle]
  rw [show groupWord [a,b]=ga*gb from group_cr,show groupWord [b,a]=gb*ga from group_c,basis_ab,basis_ba]

/-- The literal triple and its one-marker model have precisely the same
equations on all lists of names, with no assumption on the interior p. -/
theorem equations_from_image (s k l : ℕ) {W z : Word Bool} (image : basis s (groupWord W)=groupWord z) :
    SameEquations (oneMarker (k+1) (l+1) W) (triple s k l z) := by
  apply sameEquations_of_group_change (basis s) (basis_injective s)
  rintro (_ | (_ | _))
  · exact image
  · exact basis_a s
  · change basis s (groupWord (run (k+1) ++ ([b] ++ run (l+1))))=groupWord (y s k l)
    simp only [groupWord_append,groupWord_run,map_mul,map_pow,basis_a,y,group_word_pow]
    rw [show groupWord [b]=gb from rfl,basis_b,pow_succ' (groupWord (x s)) l]
    have bc := basis_ba s
    rw [map_mul,basis_a,basis_b] at bc
    simp only [mul_assoc]
    rw [←mul_assoc (groupWord (pal s))⁻¹ (groupWord (x s)),bc]

theorem signed_equations (s k l : ℕ) (p : Word Bool) :
    SameEquations (oneMarker (k+1) (l+1) (abstractWord p)) (triple s k l (literal s p)) :=
  equations_from_image s k l (basis_third s p)

/-- A code in the literal alphabet is injective on the abstract names as well. -/
theorem abstract_code {s k l : ℕ} {p : Word Bool} (code : NamedCode (triple s k l (literal s p))) :
    NamedCode (oneMarker (k+1) (l+1) (abstractWord p)) := (signed_equations s k l p).namedCode_iff.mpr code

end ThreeWordCodes.Palindromic
