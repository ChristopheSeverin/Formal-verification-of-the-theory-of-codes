module

public import ThreeWordCodes.UniformCoordinates

/-! # Positive coordinates when the uniform gap is one

For distinct initial margins the new free letters are A and B. The period K
is AB, and the distinguished token S is A. The two choices of S cover the two
orders of the initial margins.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
open GroupCoordinates (change)
private abbrev G := FreeGroup Bool
private abbrev x : G := GroupCoordinates.a
private abbrev y : G := GroupCoordinates.b
private abbrev K : G := x*y

private def assign (u v : G) : G →* G := FreeGroup.lift fun c => if c then v else u
@[simp] private theorem assign_x (u v : G) : assign u v x = u := by simp [x,GroupCoordinates.a,assign]
@[simp] private theorem assign_y (u v : G) : assign u v y = v := by simp [y,GroupCoordinates.b,assign]

private theorem recovers (F H : G →* G) (hx : H (F x) = x) (hy : H (F y) = y) :
    Function.Injective F := by
  have equal : H.comp F = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro c
    cases c
    · exact hx
    · exact hy
  exact Function.LeftInverse.injective (fun t => congrArg (fun k : G →* G => k t) equal)

private def leftMap (M : ℕ) := assign (x⁻¹ * K^M) (K * (x⁻¹ * K^M)⁻¹)
private def rightMap (M : ℕ) := assign ((K^M)⁻¹ * x) (((K^M)⁻¹ * x)⁻¹ * K)

private theorem left_inj (M : ℕ) : Function.Injective (leftMap M) := by
  let oldK := y*x
  let oldS := oldK^M * x⁻¹
  let H := assign oldS (oldS⁻¹*oldK)
  have hk : H K = oldK := by simp [H,K]
  have hs : H x = oldS := assign_x ..
  apply recovers _ H
  · simp only [leftMap,assign_x,map_mul,map_inv,map_pow,hk,hs]
    change oldS⁻¹ * oldK^M = x
    simp [oldS]
  · simp only [leftMap,assign_y,map_mul,map_inv,map_pow,hk,hs]
    change oldK * (oldS⁻¹ * oldK^M)⁻¹ = y
    simp [oldS,oldK,mul_assoc]

private theorem right_inj (M : ℕ) : Function.Injective (rightMap M) := by
  let oldK := x*y
  let oldS := oldK^M * x
  let H := assign oldS (oldS⁻¹*oldK)
  have hk : H K = oldK := by simp [H,K]
  have hs : H x = oldS := assign_x ..
  apply recovers _ H
  · simp only [rightMap,assign_x,map_mul,map_inv,map_pow,hk,hs]
    change (oldK^M)⁻¹ * oldS = x
    simp [oldS]
  · simp only [rightMap,assign_y,map_mul,map_inv,map_pow,hk,hs]
    change ((oldK^M)⁻¹ * oldS)⁻¹ * oldK = y
    simp [oldS,oldK]

private def W (i n q : ℕ) := mixed i (List.replicate n 1) q
private theorem old_words (n : ℕ) :
    groupWord (W 0 n 0) = (y*x)^(n+1)*x⁻¹ ∧
    groupWord (W 0 n 1) = (y*x)^(n+1) ∧
    groupWord (W 1 n 0) = (x*y)^(n+1) ∧
    groupWord (W 1 n 1) = (x*y)^(n+1)*x := by
  have cons (i n q : ℕ) : W i (n+1) q = (run i ++ [b]) ++ W 1 n q := by
    simp [W,mixed,gapTail,List.replicate_succ,List.append_assoc]
  induction n with
  | zero =>
    have consG (c : Bool) (w : Word Bool) : groupWord (c::w) = FreeGroup.of c * groupWord w := by
      change groupWord ([c] ++ w) = _
      rw [groupWord_append,groupWord_singleton]
    simp [W,mixed,gapTail,run,consG,x,y,GroupCoordinates.a,GroupCoordinates.b,a,b,mul_assoc]
  | succ n ih =>
    obtain ⟨_,_,left,right⟩ := ih
    have pre (i : ℕ) : groupWord (run i ++ [b]) = x^i*y := by
      rw [groupWord_append,groupWord_run,groupWord_singleton]; rfl
    simp only [cons,groupWord_append,pre,left,right,pow_zero,pow_one,one_mul]
    have slide := mul_pow_mul y x (n+1)
    constructor
    · rw [←slide,pow_succ (y*x) (n+1)]
      group
    refine ⟨?_,?_,?_⟩
    · rw [←mul_assoc,←slide,pow_succ (y*x) (n+1)]
      group
    · rw [pow_succ' (x*y) (n+1)]
    · rw [pow_succ' (x*y) (n+1)]
      simp [mul_assoc]

private def period (M : ℕ) := wordPow [a,b] M
private def dropA (N : ℕ) := b :: period N

private theorem positive_period (M : ℕ) : groupWord (period M) = K^M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    change groupWord (wordPow [a,b] (M+1)) = _
    rw [wordPow_succ,groupWord_append,pow_succ]
    change groupWord (period M) * groupWord ([a] ++ [b]) = _
    rw [ih,groupWord_append,groupWord_singleton,groupWord_singleton]
    rfl

private theorem dropA_image (N : ℕ) : groupWord (dropA N) = x⁻¹*K^(N+1) := by
  change groupWord ([b] ++ period N) = _
  rw [groupWord_append,groupWord_singleton,positive_period,pow_succ']
  change y * K^N = x⁻¹ * ((x*y)*K^N)
  simp [mul_assoc]

private theorem leftK (M : ℕ) : leftMap M (y*x) = K := by simp [leftMap,mul_assoc]
private theorem rightK (M : ℕ) : rightMap M (x*y) = K := by simp [rightMap,mul_assoc]

/-- In the unit-gap case, distinct normalized initial margins give a positive
letter model for any numbers of markers, even before imposing ambiguity. -/
theorem alternating_lengthening {i h q : ℕ} (n m : ℕ) (ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0))
    (qmax : q≤1) : HasLetterRealization (extended i (List.replicate n 1) 0 h (List.replicate m 1) q) := by
  have sumForm : x⁻¹*K^((n+1)+(m+1)) = groupWord (dropA ((n+1)+m)) := by
    rw [dropA_image,show (n+1)+(m+1) = ((n+1)+m)+1 by omega]
  have conjForm : x⁻¹*K^(m+1)*x = groupWord (dropA m ++ [a]) := by
    rw [groupWord_append,groupWord_singleton,dropA_image]; rfl
  obtain ⟨P0,P1,U0,U1⟩ := old_words n
  obtain ⟨Q0,Q1,V0,V1⟩ := old_words m
  rcases ends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · let F := leftMap (n+1)
    let model := addToken (pair [a] (period (n+1))) (if q=0 then dropA m++[a] else dropA ((n+1)+m))
    refine ⟨model,sameEquations_of_group_change F (left_inj _) ?_,some false,a,rfl⟩
    have old (t : ℕ) : F ((y*x)^t) = K^t := by rw [map_pow,leftK]
    have base : F x = x⁻¹*K^(n+1) := assign_x ..
    have eq0 : groupWord (W 1 m 0) = x*(y*x)^(m+1)*x⁻¹ := by
      rw [V0,←mul_pow_mul x y (m+1)]
      simp [mul_assoc]
    have eq1 : groupWord (W 1 m 1) = x*(y*x)^(m+1) := by rw [V1,mul_pow_mul]
    rintro (_ | (_ | _))
    · rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
      · change F (groupWord (W 1 m 0)) = groupWord (dropA m++[a])
        rw [eq0,map_mul,map_mul,map_inv,old,base,←conjForm]
        group
      · change F (groupWord (W 1 m 1)) = _
        rw [eq1,map_mul,old,base]
        change _ = groupWord (dropA ((n+1)+m))
        rw [←sumForm,pow_add K (n+1) (m+1),mul_assoc]
    · change F (groupWord (W 0 n 0)) = groupWord [a]
      rw [P0,map_mul,map_inv,old,base,groupWord_singleton]
      change _ = x
      group
    · change F (groupWord (W 0 n 1)) = groupWord (period _)
      rw [P1,old,positive_period]
  · let F := rightMap (n+1)
    let model := addToken (pair (period (n+1)) [a]) (if q=0 then dropA ((n+1)+m) else dropA m++[a])
    refine ⟨model,sameEquations_of_group_change F (right_inj _) ?_,some true,a,rfl⟩
    have old (t : ℕ) : F ((x*y)^t) = K^t := by rw [map_pow,rightK]
    have base : F x = (K^(n+1))⁻¹*x := assign_x ..
    have eq0 : groupWord (W 0 m 0) = x⁻¹*(x*y)^(m+1) := by
      rw [Q0]
      calc (y*x)^(m+1)*x⁻¹ = (x⁻¹*(x*(y*x)^(m+1)))*x⁻¹ := by simp
           _ = _ := by rw [←mul_pow_mul x y (m+1)]; simp [mul_assoc]
    have eq1 : groupWord (W 0 m 1) = x⁻¹*(x*y)^(m+1)*x := by
      rw [Q1,mul_assoc,mul_pow_mul]
      group
    rintro (_ | (_ | _))
    · rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
      · change F (groupWord (W 0 m 0)) = groupWord (dropA ((n+1)+m))
        rw [eq0,map_mul,map_inv,old,base,←sumForm,pow_add]
        group
      · change F (groupWord (W 0 m 1)) = groupWord (dropA m++[a])
        rw [eq1,map_mul,map_mul,map_inv,old,base,←conjForm]
        group
    · change F (groupWord (W 1 n 0)) = groupWord (period _)
      rw [U0,old,positive_period]
    · change F (groupWord (W 1 n 1)) = groupWord [a]
      rw [U1,map_mul,old,base,groupWord_singleton]
      change _ = x
      group

end ThreeWordCodes.BinaryGaps
