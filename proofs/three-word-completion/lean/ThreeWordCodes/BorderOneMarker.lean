module

public import ThreeWordCodes.BorderUniform
public import ThreeWordCodes.MarkerPositions
public import ThreeWordCodes.ShortGaps

/-! # The one-marker third piece in the second-letter border case -/

@[expose] public section
namespace ThreeWordCodes.Border
open BinaryGaps

/-- The first long-gap block determines every other block. Bounding that
prefix suffices to express the whole list as runs of twos separated by ones. -/
theorem blocks_from_prefix_bound (gs : List ℕ) (amb : ¬NamedCode (layout 1 [] 1 0 gs 0))
    (cap : ∀ H,H <+: gs → (∀ x∈H,2≤x) → ∀ x∈H,x≤2) :
    ∃ d k,gs=List.replicate d 2++wordPow (1::List.replicate d 2) k := by
  have lo : ∀ u∈gs,1≤u := one_marker_gaps (k:=1) (l:=1) (fun code => amb code.1)
  by_cases has : ∃ u∈gs,u<1+1
  · obtain ⟨H,c,k,small,high,shape⟩ := short_gap_blocks amb has
    have mem : c∈gs := by rw [shape,wordPow_succ']; simp
    have one : c=1 := by have := lo c mem; omega
    have block : H=List.replicate H.length 2 := by
      apply List.eq_replicate_iff.mpr ⟨rfl,?_⟩
      intro u hu
      have upper := cap H ⟨_,shape.symm⟩ high u hu
      have lower := high u hu
      omega
    refine ⟨H.length,k+1,?_⟩
    simpa only [←block,←one] using shape
  · have block : gs=List.replicate gs.length 2 := by
      apply List.eq_replicate_iff.mpr ⟨rfl,?_⟩
      intro u hu
      have below := cap gs (List.prefix_refl _) (fun x hx => by by_contra! small; exact has ⟨x,hx,small⟩) u hu
      have above : ¬u<1+1 := fun lt => has ⟨u,hu,lt⟩
      omega
    exact ⟨gs.length,0,by simpa only [wordPow_zero,List.append_nil] using block⟩

theorem one_marker_blocks (gs : List ℕ) (old : ¬NamedCode (layout 0 gs 0 1 [] 1))
    (longer : ¬NamedCode (extended 0 gs 0 1 [] 1)) :
    ∃ d k,gs=List.replicate d 2++wordPow (1::List.replicate d 2) k := by
  apply blocks_from_prefix_bound gs (swapped_ambiguity old)
  intro H pref _ u hu
  by_contra! large
  exact longer (large_gap_locates_bodies 0 gs 1 1 2 (by decide) ⟨u,pref.sublist.subset hu,large⟩)

theorem body_blocks (d k : ℕ) :
    mixed 0 (List.replicate d 2++wordPow (1::List.replicate d 2) k) 0 =
      body d 2++wordPow ([a]++body d 2) k := by
  let H := List.replicate d 2
  change mixed 0 (H++wordPow (1::H) k) 0=body d 2++wordPow ([a]++body d 2) k
  induction k with
  | zero => simp [body,H]
  | succ k ih =>
    rw [wordPow_succ (1::H) k,wordPow_succ ([a]++body d 2) k,←List.append_assoc (body d 2),←ih]
    let B := H++wordPow (1::H) k
    have e : mixed 0 B 0++[a]=mixed 0 B 1 := append_pure B 0 0 1
    rw [←List.append_assoc (mixed 0 _ 0),e]
    simpa only [body,H,B,List.append_assoc,Nat.add_zero] using (join_mixed B H 0 1 0 0).symm

/-- The (d+1)-st power of aba is obtained by bracketing H_(d+1)(2) by a. -/
theorem aba_body (d : ℕ) : wordPow [a,b,a] (d+1)=[a]++body d 2++[a] := by
  have pure (n : ℕ) : wordPow [a,b,a] (n+1)=mixed 1 (List.replicate n 2) 1 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [wordPow_succ' [a,b,a] (n+1),ih]
      exact join_mixed [] (List.replicate n 2) 1 1 1 1
  exact (pure d).trans (body_bracket d 2 1 1).symm

theorem one_marker_forbidden {gs : List ℕ} {n i j : ℕ}
    (model : Model (mixed 0 gs 0) [a] [a,b,a] n i j)
    (old : ¬NamedCode (layout 0 gs 0 1 [] 1)) (longer : ¬NamedCode (extended 0 gs 0 1 [] 1)) : False := by
  obtain ⟨d,k,shape⟩ := one_marker_blocks gs old longer
  have e : mixed 0 gs 0=body d 2++wordPow ([a]++body d 2) k := by rw [shape,body_blocks]
  let h := [a]++body d 2
  have one : [a]++mixed 0 gs 0=wordPow h (k+1) := by rw [e,wordPow_succ']; simp [h]
  have two : wordPow [a,b,a] (d+1)++mixed 0 gs 0=wordPow h (k+2) := by
    rw [aba_body,e,wordPow_succ' h (k+1),wordPow_succ' h k]; simp [h,List.append_assoc]
  apply model.forbidden d
  rw [one,two]; exact wordPow_comm ..

end ThreeWordCodes.Border
