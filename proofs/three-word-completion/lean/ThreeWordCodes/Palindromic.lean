module

public import ThreeWordCodes.SelectedGraft
public import ThreeWordCodes.OneMarker

/-! # The alternating-palindrome family of Proposition 7

The parameters s, k and l in this file are one less than the three positive
parameters in the manuscript. Thus zero is allowed in all three arguments.
-/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

def x (s : ℕ) : Word Bool := wordPow [a,b] (s+1) ++ [a]
def c : Word Bool := [b,a]
def y (s k l : ℕ) := wordPow (x s) (k+1) ++ c ++ wordPow (x s) l
def triple (s k l : ℕ) (z : Word Bool) := addToken (pair (x s) (y s k l)) z

/-- Proposition 7 of the manuscript. -/
def PropositionSeven : Prop :=
  ∀ s k l z, NamedCode (triple s k l z) → Completable (triple s k l z)

theorem x_head (s : ℕ) : ∃ u, x s = a::u := by
  rw [x,wordPow_succ']
  exact ⟨_,rfl⟩

private theorem reverse_pow {A : Type*} (w : Word A) (k : ℕ) :
    (wordPow w k).reverse = wordPow w.reverse k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordPow_succ,List.reverse_append,ih,wordPow_succ']

@[simp] theorem x_palindrome (s : ℕ) : (x s).reverse = x s := by
  simp only [x,List.reverse_append,reverse_pow,List.reverse_singleton]
  exact (rotate_power [a] [b] (s+1)).symm

theorem shift (s : ℕ) : x s ++ c = c.reverse ++ x s := by
  change (wordPow [a,b] (s+1) ++ [a]) ++ [b,a] = [a,b] ++ (wordPow [a,b] (s+1) ++ [a])
  calc _ = wordPow [a,b] (s+2) ++ [a] := by rw [wordPow_succ [a,b] (s+1)]; simp [List.append_assoc]
       _ = _ := by rw [wordPow_succ' [a,b] (s+1)]; simp

@[simp] theorem y_reverse (s k l : ℕ) : (y s k l).reverse = y s l k := by
  simp only [y,List.reverse_append,reverse_pow,x_palindrome]
  rw [wordPow_succ' (x s) k,wordPow_succ (x s) l]
  simpa only [List.append_assoc] using congrArg (fun w => wordPow (x s) l ++ w ++ wordPow (x s) k) (shift s).symm

theorem triple_reverse (s k l : ℕ) (z : Word Bool) :
    (fun i => (triple s k l z i).reverse) = triple s l k z.reverse := by
  funext i
  rcases i with _ | (_ | _) <;> simp [triple,addToken,pair]

def readers (s l : ℕ) := pair (x s) (c ++ wordPow (x s) l)

theorem reader_prefix (s l : ℕ) :
    Function.Injective (readers s l) ∧ (∀ i, readers s l i ≠ []) ∧
      InformationTheory.IsPrefixFree (Set.range (readers s l)) := by
  obtain ⟨u,form⟩ := x_head s
  refine ⟨?_,?_,?_⟩
  · rintro (_ | _) (_ | _) eqn <;> simp_all [readers,pair,c,a,b]
  · rintro (_ | _) <;> simp [readers,pair,form,c]
  · rintro _ ⟨(_ | _),rfl⟩ _ ⟨(_ | _),rfl⟩ ⟨w,eqn⟩ <;> first | rfl | simp [readers,pair,form,c,a,b] at eqn

/-- If greedy reading fails by an incomparable remainder, the shorter list
completes and lengthening restores y. -/
theorem incomparable_reading (s k l : ℕ) (z : Word Bool)
    (stop : ¬∃ p, z <+: spell (readers s l) p) : Completable (triple s k l z) := by
  obtain ⟨inj,nz,pf⟩ := reader_prefix s l
  have done := greedy_completion inj nz pf z stop
  let w := addToken (readers s l) z
  let pad (j : Option Bool) := if j=some true then List.replicate (k+1) (some false) else []
  have eqn : (fun j => spell w (pad j) ++ w j) = triple s k l z := by
    funext j
    rcases j with _ | (_ | _) <;>
      simp [w,pad,readers,triple,addToken,pair,spell_replicate,y,List.append_assoc]
  exact eqn ▸ done.padLeft pad

/-- A complete reading on x and c x^l gives the one-sided marker a^(k+1)b
on the names. Its positive completion is unconditional. -/
theorem complete_reading (s k l : ℕ) (z : Word Bool) (code : NamedCode (triple s k l z))
    (read : ∃ p, spell (readers s l) p = z) : Completable (triple s k l z) := by
  obtain ⟨p,rfl⟩ := read
  obtain ⟨inj,nz,pf⟩ := reader_prefix s l
  have inner := completable_prefix inj nz pf
  let outer := addToken (pair [a] (run (k+1) ++ [b])) p
  have eqn : (fun j => spell (readers s l) (outer j)) = triple s k l (spell (readers s l) p) := by
    funext j
    rcases j with _ | (_ | _) <;>
      simp [outer,readers,triple,addToken,pair,run,spell_replicate,y,List.append_assoc,a,b]
  have named := (inner.1.preserves_equations outer).namedCode_iff.mpr (eqn.symm ▸ code)
  exact eqn ▸ inner.substitute (left_marker_completion (k+1) p named)

/-- Any obstruction has to stop strictly inside the last token in both
orientations and cannot have a complete reading in either orientation. -/
theorem two_proper_readings {s k l : ℕ} {z : Word Bool} (code : NamedCode (triple s k l z))
    (bad : ¬ Completable (triple s k l z)) :
    (∃ p, z <+: spell (readers s l) p) ∧ (¬∃ p, spell (readers s l) p = z) ∧
    (∃ p, z.reverse <+: spell (readers s k) p) ∧ (¬∃ p, spell (readers s k) p = z.reverse) := by
  have eqn := triple_reverse s k l z
  have rc : NamedCode (triple s l k z.reverse) := eqn ▸ code.reverse
  have rb : ¬Completable (triple s l k z.reverse) := by
    intro done
    have reverted := done.reverse
    rw [triple_reverse,List.reverse_reverse] at reverted
    exact bad reverted
  exact ⟨by by_contra h; exact bad (incomparable_reading s k l z h),
    fun h => bad (complete_reading s k l z code h),
    by by_contra h; exact rb (incomparable_reading s l k z.reverse h),
    fun h => rb (complete_reading s l k z.reverse rc h)⟩

private def graftLeaves : List (Word Bool) := [[a],[a,b],[b,b]]

/-- The first short-gap graft for the signed-letter application. The same
suffix leaves work for every s and every literal tail incomparable with ba. -/
theorem graft_certificate (s : ℕ) (t : Word Bool) (apart : ¬ Comparable t c) :
    HasFiniteCertificate ({x s,x s++c,c++c++t} : Set (Word Bool)) := by
  let v := readers s 0
  have vc : v b = c := by simp [v,readers,pair,b]
  have va : v a = x s := rfl
  have nt : t≠[] := by rintro rfl; exact apart (Or.inl List.nil_prefix)
  have ok : SelectedGraft.Valid v graftLeaves [b,b] t := by
    refine ⟨by decide,by decide,nt,by decide,?_⟩
    intro q hq
    have all : ∀ q∈SelectedGraft.nodes graftLeaves, q=[] ∨ q=[b] := by decide
    rcases all q hq with rfl | rfl
    · exact ⟨Ne.symm nt,fun _ => by decide⟩
    · have text : spell v [b]=c := by simp [vc]
      rw [text]
      exact ⟨fun h => apart (Or.inl (h ▸ List.prefix_refl _)),fun cp => (apart cp).elim⟩
  obtain ⟨inj,nz,pf⟩ := reader_prefix s 0
  have result := SelectedGraft.certificate v inj nz pf graftLeaves [b,b] t ok
  apply result.mono
  rintro w (rfl | rfl | rfl)
  · right
    exact ⟨[a],⟨by decide,by decide⟩,by simp [va]⟩
  · right
    exact ⟨[a,b],⟨by decide,by decide⟩,by simp [va,vc]⟩
  · left
    simp [vc]

/-- All positive exponents in Proposition 7 lift from the same graft.
The third word consists of two copies of ba followed by the chosen tail. -/
theorem graft_completion (s k l : ℕ) (t : Word Bool) (apart : ¬ Comparable t c) :
    Completable (triple s k l (c++c++t)) := by
  let z := c++c++t
  let v := triple s 0 0 z
  obtain ⟨u,xu⟩ := x_head s
  have subset : Set.range v ⊆ ({x s,x s++c,c++c++t} : Set (Word Bool)) := by
    rintro _ ⟨(_ | (_ | _)),rfl⟩ <;> simp [v,z,triple,addToken,pair,y]
  have complete := ((graft_certificate s t apart).mono subset).toPositive
  have injective : Function.Injective v := by
    rintro (_ | (_ | _)) (_ | (_ | _)) eqn <;> try rfl
    all_goals simp [v,z,triple,addToken,pair,y,xu,c,a,b] at eqn
  have base : Completable v := by
    refine ⟨(namedCode_iff_range _).mpr ⟨injective,?_⟩,complete⟩
    obtain ⟨M,_,_,contain,hM,_⟩ := complete
    intro p q hp hq
    exact hM.1 p q (fun w hw => contain (hp w hw)) (fun w hw => contain (hq w hw))
  let pad (n : ℕ) (j : Option Bool) := if j=some true then List.replicate n (some false) else []
  let left := fun j => spell v (pad k j) ++ v j
  have done : Completable left := base.padLeft (pad k)
  have eqn : (fun j => left j ++ spell left (pad l j)) = triple s k l z := by
    funext j
    rcases j with _ | (_ | _) <;>
      simp [left,pad,v,triple,addToken,pair,y,spell_replicate,wordPow_succ,List.append_assoc]
  exact eqn ▸ done.padRight (pad l)

end ThreeWordCodes.Palindromic
