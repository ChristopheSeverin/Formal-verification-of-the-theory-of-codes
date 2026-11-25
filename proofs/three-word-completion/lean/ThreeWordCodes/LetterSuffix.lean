module

public import ThreeWordCodes.Realizations
public import ThreeWordCodes.Coordinates
public import ThreeWordCodes.GapComparison

/-! # The one-marker branch of binary lengthening in Lemma 4

If P = a^i b, the words P and Pa have different final letters. An ambiguous
third word is a suffix of one token followed by complete tokens. This avoids
having to classify its individual gaps.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A I : Type*}

private theorem suffix_reading [Fintype A] [Fintype I] {f : I → Word A}
    (hi : Function.Injective (fun i => (f i).reverse)) (hn : ∀ i, (f i).reverse ≠ [])
    (prefixFree : InformationTheory.IsPrefixFree (Set.range (fun i => (f i).reverse)))
    (w : Word A) (amb : ¬ NamedCode (addToken f w)) : ∃ s, w <:+ spell f s := by
  let r := addToken (fun i => (f i).reverse) w.reverse
  have re : (fun k => (r k).reverse) = addToken f w := by
    funext k
    cases k <;> simp [r,addToken]
  obtain ⟨s,he⟩ := prefix_of_products_of_ambiguity hi hn prefixFree w.reverse
    (fun h => amb (re ▸ h.reverse))
  exact ⟨s.reverse,List.reverse_prefix.mp (by simpa only [spell_reverse] using he)⟩

private theorem cut_suffix {f : I → Word A} (s : Word I) {w : Word A}
    (tail : w <:+ spell f s) :
    w=[] ∨ ∃ x r u, r <:+ f x ∧ w = r ++ spell f u := by
  induction s with
  | nil => exact Or.inl (by simpa using tail)
  | cons x s ih =>
    obtain ⟨left,eqn⟩ := tail
    rcases List.append_eq_append_iff.mp eqn with ⟨r,token,word⟩ | ⟨r,_,word⟩
    · exact Or.inr ⟨x,r,s,⟨left,token.symm⟩,word⟩
    · exact ih ⟨r,word.symm⟩

namespace BinaryGaps

def firstPair (i : ℕ) := pair (mixed i [] 0) (mixed i [] 1)

private theorem one_token_suffix (i t : ℕ) (r : Word Bool) (h : r <:+ mixed i [] t) :
    (∃ n, r = run n) ∨ ∃ z, z ≤ i ∧ r = mixed z [] t := by
  induction i with
  | zero =>
    change r <:+ b :: run t at h
    rcases List.suffix_cons_iff.mp h with word | tail
    · exact Or.inr ⟨0,le_rfl,word⟩
    · exact Or.inl ⟨r.length,List.eq_replicate_iff.mpr ⟨rfl,fun _ hm => (List.mem_replicate.mp
        (tail.sublist.subset hm)).2⟩⟩
  | succ i ih =>
    change r <:+ a :: mixed i [] t at h
    rcases List.suffix_cons_iff.mp h with word | tail
    · exact Or.inr ⟨_,le_rfl,word⟩
    · rcases ih tail with pure | ⟨z,le,form⟩
      · exact Or.inl pure
      · exact Or.inr ⟨z,by omega,form⟩

theorem groupWord_run (i : ℕ) : groupWord (run i) = GroupCoordinates.a ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change groupWord ([a] ++ run i) = _
    rw [groupWord_append,ih,groupWord_singleton,pow_succ']
    rfl

private theorem mixed_image (h t : ℕ) : groupWord (mixed h [] t) =
    GroupCoordinates.a ^ h * GroupCoordinates.b * GroupCoordinates.a ^ t := by
  change groupWord (run h ++ ([b] ++ run t)) = _
  rw [groupWord_append,groupWord_append,groupWord_singleton,groupWord_run,groupWord_run,mul_assoc]
  rfl

/-- Signed coordinates for a suffix cut inside the first token. Its unused
initial margin and unused terminal margin become positive powers of D. -/
private theorem partial_image (i h t : ℕ) (hi : h ≤ i) (ht : t ≤ 1) :
    GroupCoordinates.change i 1 (groupWord (mixed h [] t)) = groupWord (mixed (i-h) [] (1-t)) := by
  let d := GroupCoordinates.a
  let j := GroupCoordinates.b
  have e₁ : d⁻¹ ^ h * d^(i : ℤ) = d^(i-h) := by
    rw [zpow_natCast,show i = h+(i-h) by omega]
    simp [pow_add]
  have e₂ : d^(1 : ℤ) * d⁻¹ ^ t = d^(1-t) := by
    rcases (show t=0 ∨ t=1 by omega) with rfl | rfl <;> simp
  rw [mixed_image,mixed_image,map_mul,map_mul,map_pow,map_pow,GroupCoordinates.change_a,
    GroupCoordinates.change_b]
  change (d⁻¹^h * (d^(i : ℤ) * j * d^(1 : ℤ))) * d⁻¹^t = _
  calc _ = (d⁻¹^h * d^(i : ℤ)) * j * (d^(1 : ℤ) * d⁻¹^t) := by simp [mul_assoc]
       _ = _ := by rw [e₁,e₂]

private theorem map_group_spell (F : FreeGroup Bool →* FreeGroup Bool)
    {f z : I → Word Bool} (images : ∀ k, F (groupWord (f k)) = groupWord (z k)) (s : Word I) :
    F (groupWord (spell f s)) = groupWord (spell z s) := by
  induction s with
  | nil => simp
  | cons x s ih => simp [images,ih]

/-- Whenever (P, Pa, Q) is ambiguous and P = a^i b, it has a binary
realization with one letter preserving every equation on its three names. -/
theorem single_marker_lengthening (i : ℕ) (w : Word Bool)
    (amb : ¬ NamedCode (addToken (firstPair i) w)) :
    HasLetterRealization (addToken (firstPair i) w) := by
  let f := firstPair i
  have ends (c : Bool) : (f c).reverse = (!c) :: (if c then b :: run i else run i) := by
    cases c <;> simp [f,firstPair,pair,mixed,run,gapTail,b,a]
  obtain ⟨s,tail⟩ := suffix_reading (f:=f)
    (by intro x y he; simpa only [ends,List.head?_cons,Option.some.injEq,Bool.not_inj_iff] using (congrArg List.head? he))
    (by intro x; rw [ends]; simp)
    (by
      rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ ⟨z,he⟩
      change (f x).reverse ++ z = (f y).reverse at he
      rw [ends,ends] at he
      have xy := (List.cons.inj he).1
      rw [Bool.not_inj xy]) w amb
  have cut : ∃ r u, w = r ++ spell f u ∧
      ((∃ n, r = run n) ∨ ∃ h t, h ≤ i ∧ t ≤ 1 ∧ r = mixed h [] t) := by
    rcases cut_suffix s tail with empty | ⟨x,r,u,part,read⟩
    · exact ⟨[],[],empty,Or.inl ⟨0,rfl⟩⟩
    · refine ⟨r,u,read,?_⟩
      let t := if x then 1 else 0
      have term : f x = mixed i [] t := by cases x <;> rfl
      rcases one_token_suffix i t r (term ▸ part) with yes | ⟨h,le,wrd⟩
      · exact Or.inl yes
      · exact Or.inr ⟨h,t,le,by cases x <;> simp [t],wrd⟩
  obtain ⟨r,u,read,shape⟩ := cut
  rcases shape with ⟨n,rfl⟩ | ⟨h,t,hi,ht,rfl⟩
  · let inner := pair [a] (mixed i [] 0)
    let z := pair [b] [b,a]
    have nz : [a] ++ mixed i [] 0 ≠ mixed i [] 0 ++ [a] := by
      intro eqn
      have joined : ([a] ++ run i) ++ [b] = mixed i [] 0 ++ [a] := by
        simpa [mixed,gapTail,run,List.append_assoc] using eqn
      have last := congrArg List.getLast? joined
      simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at last
      contradiction
    have std := (noncommuting_pair_completion _ _ nz).1
    have pairRead : (fun k => spell inner (z k)) = f := by
      funext x
      cases x <;> simp [inner,z,f,firstPair,pair,mixed,gapTail,run,b,a]
    have pureRead (n : ℕ) : spell inner (run n) = run n := by
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg (a :: ·) ih
    let model := addToken z (run n ++ spell z u)
    have actual : (fun k => spell inner (model k)) = addToken f w := by
      funext k
      cases k with
      | none =>
        change spell inner (run n ++ spell z u) = w
        rw [spell_append,pureRead,←spell_substitution,pairRead,read]
      | some x => exact congrFun pairRead x
    exact ⟨model,actual ▸ (std.preserves_equations model).symm,some false,b,rfl⟩
  · let z := pair [b,a] [b]
    let F := GroupCoordinates.change i 1
    have images (x : Bool) : F (groupWord (f x)) = groupWord (z x) := by
      cases x
      · simpa [f,firstPair,pair,z,mixed,gapTail,run] using partial_image i i 0 le_rfl (by omega)
      · simpa [f,firstPair,pair,z,mixed,gapTail,run] using partial_image i i 1 le_rfl le_rfl
    let model := addToken z (mixed (i-h) [] (1-t) ++ spell z u)
    refine ⟨model,sameEquations_of_group_change F (GroupCoordinates.change_involutive i 1).injective ?_,
      some true,b,rfl⟩
    rintro (_ | x)
    · change F (groupWord w) = groupWord (mixed (i-h) [] (1-t) ++ spell z u)
      rw [read,groupWord_append,groupWord_append,map_mul,show F (groupWord (mixed h [] t)) = _
        from partial_image i h t hi ht,map_group_spell F images]
    · exact images x

end BinaryGaps
end ThreeWordCodes
