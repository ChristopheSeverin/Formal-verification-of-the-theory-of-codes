module

public import ThreeWordCodes.Palindromic
public import ThreeWordCodes.PureCorollaries
public import Mathlib.Data.List.Chain

/-! # Proposition 7 for every alternating third word -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps
variable {A B : Type*}

private theorem read_on_pair (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    {v : Bool → Word Bool} (base : Completable v) (X C Z : Word Bool)
    (readX : spell v X=x s) (readC : spell v C=c) (readZ : spell v Z=z)
    (pure : (∃ a n, X=List.replicate n a) ∨ ∃ a n, Z=List.replicate n a) :
    Completable (triple s k l z) := by
  let outer := addToken (pair X (wordPow X (k+1)++C++wordPow X l)) Z
  have eqn : (fun i => spell v (outer i)) = triple s k l z := by
    funext i
    rcases i with _ | (_ | _) <;> simp [outer,triple,pair,addToken,y,spell_wordPow,readX,readC,readZ]
  apply pure_reading_completion threeOrder base outer eqn code
  rcases pure with ⟨w,n,e⟩ | ⟨w,n,e⟩
  · exact ⟨some false,w,n,e⟩
  · exact ⟨none,w,n,e⟩

def pal (n : ℕ) := wordPow [a,b] n ++ [a]
private def cap (n : ℕ) := wordPow c n ++ [b]

theorem enlarge (i n : ℕ) : pal i ++ wordPow c n = pal (i+n) := by
  simp only [pal,wordPow_add,List.append_assoc]
  exact congrArg (wordPow [a,b] i ++ ·) (rotate_power [a] [b] n).symm

private theorem pair_complete (n : ℕ) : Completable (pair (pal n) c) := by
  have head : ∃ rest, pal n=a::rest := by
    cases n with
    | zero => exact ⟨[],rfl⟩
    | succ n => rw [pal,wordPow_succ']; exact ⟨_,rfl⟩
  apply noncommuting_pair_completion
  obtain ⟨rest,form⟩ := head
  intro eqn
  rw [form] at eqn
  exact Bool.noConfusion (List.cons.inj eqn).1

/-- Any complete reading on the shorter basis x, ba suffices, in addition
to the forward reading on x, (ba)x^l. -/
theorem complete_on_x_c (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (read : ∃ p, spell (pair (x s) c) p=z) : Completable (triple s k l z) := by
  obtain ⟨p,rp⟩ := read
  apply read_on_pair s k l z code (pair_complete (s+1)) [a] [b] p
  · simp [pair,x,pal,a]
  · simp [pair,b]
  · exact rp
  · exact Or.inl ⟨a,1,rfl⟩

theorem letter_ends (s k l t : ℕ) (code : NamedCode (triple s k l (pal t))) :
    Completable (triple s k l (pal t)) := by
  let p := min (s+1) t
  let v := pair (pal p) c
  let names (i : ℕ) := a::List.replicate (i-p) b
  have expansion (i : ℕ) (hi : p ≤ i) : spell v (names i)=pal i := by
    change pal p ++ spell v (List.replicate (i-p) b) = _
    rw [spell_replicate,show v b=c from rfl,enlarge,Nat.add_sub_of_le hi]
  apply read_on_pair s k l (pal t) code (pair_complete p) (names (s+1)) [b] (names t)
  · exact expansion (s+1) (Nat.min_le_left ..)
  · simp [pair,b]
  · exact expansion t (Nat.min_le_right ..)
  · rcases le_total (s+1) t with first | second
    · exact Or.inl ⟨a,1,by simp [names,p,Nat.min_eq_left first]⟩
    · exact Or.inr ⟨a,1,by simp [names,p,Nat.min_eq_right second]⟩

theorem back_pow (w : Word Bool) (n : ℕ) : (wordPow w n).reverse = wordPow w.reverse n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ,List.reverse_append,ih,wordPow_succ']

private theorem reverse_cap (n : ℕ) : (cap n).reverse = cap n := by
  simp only [cap,List.reverse_append,List.reverse_singleton,back_pow]
  exact (rotate_power [b] [a] n).symm

theorem flip_back {s k l : ℕ} {z : Word Bool} (done : Completable (triple s l k z.reverse)) :
    Completable (triple s k l z) := by
  have flip := done.reverse
  rw [triple_reverse,List.reverse_reverse] at flip
  exact flip

private theorem even_backward (s k l t : ℕ) (code : NamedCode (triple s k l (wordPow c t))) :
    Completable (triple s k l (wordPow c t)) :=
  complete_on_x_c s k l _ code ⟨List.replicate t b,spell_replicate (pair (x s) c) b t⟩

private theorem starts_bab (t : ℕ) : ∃ tail, cap (t+1) = b::a::b::tail := by
  rw [cap,wordPow_succ']
  cases t with
  | zero => exact ⟨[],rfl⟩
  | succ t => rw [wordPow_succ']; exact ⟨_,rfl⟩

private theorem excludes_bab (s k l : ℕ) (rest : Word Bool) :
    Completable (triple s k (l+1) (b::a::b::rest)) := by
  apply incomparable_reading
  rintro ⟨p,suffix,eqn⟩
  cases p with
  | nil => simp at eqn
  | cons i p =>
    have startX : ∃ t, x s=a::t := by rw [x,wordPow_succ']; exact ⟨_,rfl⟩
    obtain ⟨t,xt⟩ := startX
    cases i <;> simp [readers,pair,c,wordPow_succ',xt,b,a] at eqn

private theorem alternating_product (i t j : ℕ) :
    pal i ++ cap t ++ pal j = pal (i+(t+1)+j) := by
  have core : [a] ++ wordPow c t ++ [b] = wordPow [a,b] (t+1) := by
    rw [show [a] ++ wordPow c t=wordPow [a,b] t ++ [a] from (rotate_power [a] [b] t).symm,wordPow_succ]
    simp [List.append_assoc]
  simp only [pal,cap,wordPow_add,List.append_assoc] at core ⊢
  simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
    congrArg (fun w => wordPow [a,b] i ++ w ++ wordPow [a,b] j ++ [a]) core

private theorem marker_ends (s k l t : ℕ) (code : NamedCode (triple s k l (cap t))) :
    Completable (triple s k l (cap t)) := by
  cases t with
  | zero => exact named_pure_power_completion threeOrder code ⟨none,b,1,rfl⟩
  | succ t =>
    obtain ⟨rest,form⟩ := starts_bab t
    cases l with
    | succ l => rw [form]; exact excludes_bab s k l rest
    | zero =>
      cases k with
      | succ k => exact flip_back (by rw [reverse_cap,form]; exact excludes_bab s 0 k rest)
      | zero =>
        have yy : y s 0 0 = pal (s+2) := by
          simpa [y,x,pal] using enlarge (s+1) 1
        have e : x s ++ cap (t+1) ++ y s 0 0 = y s 0 0 ++ cap (t+1) ++ x s := by
          rw [yy,show x s=pal (s+1) from rfl,alternating_product,alternating_product]
          congr 1; omega
        have test : spell (triple s 0 0 (cap (t+1))) [some false,none,some true] =
            spell (triple s 0 0 (cap (t+1))) [some true,none,some false] := by
          simpa [triple,pair,addToken,List.append_assoc] using e
        exact ((by decide : [some false,none,some true] ≠ [some true,none,some false]) (code test)).elim

private def alternating (c : Bool) : ℕ → Word Bool
  | 0 => []
  | n+1 => c::alternating (!c) n

private theorem expand (w : Word Bool) (c : Bool) (starts : w=[] ∨ w.head?=some c)
    (chain : w.IsChain (·≠·)) : w=alternating c w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons x xs ih =>
    have same : x=c := by simpa using starts
    subst x
    apply congrArg (c :: ·)
    cases xs with
    | nil => rfl
    | cons y ys =>
      obtain ⟨different,later⟩ := List.isChain_cons_cons.mp chain
      have bit : y=(!c) := by cases c <;> cases y <;> simp_all
      exact ih _ (Or.inr (by simp [bit])) later

private theorem alternating_pairs (c : Bool) (n : ℕ) :
    alternating c (2*n) = wordPow [c,!c] n ∧
    alternating c (2*n+1) = wordPow [c,!c] n ++ [c] := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have e : 2*(n+1)=2*n+2 := by omega
    rw [e,wordPow_succ']
    simp only [alternating,Bool.not_not,List.cons_append,List.nil_append]
    constructor
    · exact congrArg (fun z => c::(!c)::z) ih.1
    · exact congrArg (fun z => c::(!c)::z) ih.2

/-- Every code in Proposition 7 whose third word alternates strictly is
positively completable, for all four choices of initial and final letters. -/
theorem alternating_third_completion (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (chain : z.IsChain (·≠·)) : Completable (triple s k l z) := by
  let bit := z.headD a
  have init : z=[] ∨ z.head?=some bit := by cases z <;> simp [bit]
  have form := expand z bit init chain
  let n := z.length/2
  have parity : z.length=2*n ∨ z.length=2*n+1 := by dsimp [n]; omega
  rcases parity with len | len
  · rw [len,(alternating_pairs bit n).1] at form
    cases h : bit with
    | true =>
      have eqn : z=wordPow c n := by simpa [h,c,a,b] using form
      exact eqn.symm ▸ even_backward s k l n (eqn ▸ code)
    | false =>
      have eqn : z.reverse=wordPow c n := by simpa [h,back_pow,c,a,b] using congrArg List.reverse form
      have rc := triple_reverse s k l z ▸ code.reverse
      exact flip_back (eqn.symm ▸ even_backward s l k n (eqn ▸ rc))
  · rw [len,(alternating_pairs bit n).2] at form
    cases h : bit with
    | false =>
      have eqn : z=pal n := by simpa [h,pal,a,b] using form
      exact eqn.symm ▸ letter_ends s k l n (eqn ▸ code)
    | true =>
      have eqn : z=cap n := by simpa [h,cap,c,a,b] using form
      exact eqn.symm ▸ marker_ends s k l n (eqn ▸ code)

end ThreeWordCodes.Palindromic
