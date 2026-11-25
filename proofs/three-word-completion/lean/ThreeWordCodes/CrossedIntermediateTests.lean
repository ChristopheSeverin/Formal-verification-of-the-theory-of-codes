module

public import ThreeWordCodes.CrossedUnitGaps
public import ThreeWordCodes.CrossedSymmetry

/-! # The two injective tests for row II with a lateral letter -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem strip_pairs {g : Option Bool → Word Bool} (nz : ∀ k,g k≠[]) (ab : g P=[a,b])
    (only : ∀ k,(g k).head?=some a → k=P) (n : ℕ) (l : Word (Option Bool)) (w : Word Bool)
    (eqn : spell g l=wordPow [a,b] n++w) : ∃ s,spell g s=w := by
  induction n generalizing l with
  | zero => exact ⟨l,eqn⟩
  | succ n ih =>
    rw [wordPow_succ',List.append_assoc] at eqn
    obtain ⟨s,rfl⟩ := forced_head (w:=[a,b]++(wordPow [a,b] n++w)) nz P (by rw [ab]; exact only)
      l (by simp) (by rw [ab]; rfl) eqn
    rw [spell_cons,ab] at eqn
    exact ih s (List.append_cancel_left eqn)

/-- For Q=(ba)^(n+1), no two products of ab,Q,Qaba differ by an initial a.
Every forced reading either encounters aa or removes one token on the right. -/
theorem alternating_intermediate_test (n : ℕ) :
    let q := [b]++(wordPow [a,b] n++[a])
    NamedCode (pieces [a,b] q (q++[a,b,a])) := by
  intro q
  let g := pieces [a,b] q (q++[a,b,a])
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,q,pieces,addToken,pair]
  have only (k : Option Bool) (h : (g k).head?=some a) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,q,pieces,addToken,pair,P,a,b]
  have force (l : Word (Option Bool)) (w : Word Bool) (eqn : spell g l=[a]++w) :
      ∃ s,[b]++spell g s=w := by
    obtain ⟨s,rfl⟩ := forced_head (w:=[a]++w) nz P only l (by simp) rfl eqn
    exact ⟨s,(List.cons.inj eqn).2⟩
  have fail (r : Word (Option Bool)) : ∀ l,spell g l≠[a]++spell g r := by
    induction r with
    | nil =>
      intro l eqn
      obtain ⟨s,impossible⟩ := force l [] eqn
      contradiction
    | cons k r ih =>
      intro l eqn
      obtain ⟨s,step⟩ := force l _ eqn
      rcases k with _|(_|_)
      · have tail : spell g s=wordPow [a,b] n++([a,a,b,a]++spell g r) := by
          change b::spell g s=(([b]++(wordPow [a,b] n++[a]))++[a,b,a])++spell g r at step
          simp only [List.append_assoc,List.cons_append,List.nil_append,List.cons.injEq,true_and] at step
          exact step
        obtain ⟨l',read⟩ := strip_pairs nz rfl only n s _ tail
        obtain ⟨s',bad⟩ := force l' ([a,b,a]++spell g r) read
        exact Bool.noConfusion ((List.cons.inj bad).1 : true=false)
      · exact Bool.noConfusion ((List.cons.inj step).1 : true=false)
      · have tail : spell g s=wordPow [a,b] n++([a]++spell g r) := by
          change b::spell g s=([b]++(wordPow [a,b] n++[a]))++spell g r at step
          simp only [List.append_assoc,List.cons_append,List.nil_append,List.cons.injEq,true_and] at step
          exact step
        obtain ⟨s',read⟩ := strip_pairs nz rfl only n s _ tail
        exact ih s' read
  by_contra amb
  obtain ⟨l,r,eqn⟩ := shifted_products [a,b] q (by decide) (by simp [q]) (by change some a≠some b; decide) amb
  exact fail r l eqn

theorem joined_test_two (m n : ℕ) :
    let p := mixed 1 (List.replicate m 2) 0
    let q := mixed 0 (List.replicate n 2) 1
    NamedCode (pieces p q (q++p++[a])) := by
  intro p q
  let g := pieces (Border.marks m++[a]) ([a]++Border.marks n) ([a]++(Border.marks n++Border.marks m))
  have imageP : GroupCoordinates.change 1 1 (groupWord p)=groupWord (Border.marks m++[a]) := by
    simpa [p,run] using gap_two_image 1 m 0 (by decide) (by decide)
  have imageQ : GroupCoordinates.change 1 1 (groupWord q)=groupWord ([a]++Border.marks n) := by
    simpa [q,run] using gap_two_image 0 n 1 (by decide) (by decide)
  have imagePa : GroupCoordinates.change 1 1 (groupWord (p++[a]))=groupWord (Border.marks m) := by
    rw [show p++[a]=mixed 1 (List.replicate m 2) 1 from append_pure _ 1 0 1]
    simpa [run] using gap_two_image 1 m 1 (by decide) (by decide)
  have same : SameEquations (pieces p q (q++p++[a])) g := by
    apply sameEquations_of_group_change (GroupCoordinates.change 1 1) (GroupCoordinates.change_involutive 1 1).injective
    rintro (_|(_|_))
    · change GroupCoordinates.change 1 1 (groupWord (q++p++[a]))=groupWord ([a]++(Border.marks n++Border.marks m))
      rw [List.append_assoc,groupWord_append,map_mul,imageQ,imagePa,←groupWord_append,List.append_assoc]
    · exact imageP
    · exact imageQ
  apply same.namedCode_iff.mpr
  let f (k : Option Bool) := ((g k).reverse).map (letterFlip true)
  let lens : Option Bool → ℕ
    | none => m+1+(n+1)
    | some false => 0
    | some true => n+1
  have hi : Function.Injective lens := by
    rintro (_|(_|_)) (_|(_|_)) eqn <;> simp_all [lens]
  have marks (d : ℕ) : ((Border.marks d).reverse).map (letterFlip true)=run (d+1) := by
    simp [Border.marks,run,letterFlip,a,b]
  have shape (k : Option Bool) : ∃ w,f k=run (lens k)++b::w := by
    rcases k with _|(_|_)
    · refine ⟨[],?_⟩
      change ((([a]++(Border.marks n++Border.marks m)).reverse).map (letterFlip true))=run ((m+1)+(n+1))++[b]
      simp only [List.reverse_append,List.map_append,marks,run_add,List.append_assoc]
      rfl
    · refine ⟨run (m+1),?_⟩
      simp [f,g,pieces,addToken,pair,Border.marks,lens,run,letterFlip,a,b]
    · refine ⟨[],?_⟩
      simp [f,g,pieces,addToken,pair,Border.marks,lens,run,letterFlip,a,b]
  have good := (named_flip_iff (fun k => (g k).reverse) true).mp (BinaryGaps.distinct_starts f lens shape hi).1
  simpa using good.reverse

end ThreeWordCodes.CrossedCase
