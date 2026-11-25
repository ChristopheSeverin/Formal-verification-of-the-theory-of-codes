module

public import ThreeWordCodes.CrossedOverlapUniform
public import ThreeWordCodes.CrossedOverlapBlocks

/-! # The one-marker overlapping row and the last obstruction -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem overlap_ba (E : List ℕ) (s : ℕ) (bound : s≤1)
    (m : Model .overlap [b,a] [a] (mixed s E 0)) : False := by
  let v := mixed s E 0
  let K := mixed 0 E.reverse 0
  let W := [b,a]++v
  let R := E.reverse++[1+s]
  have form : W=mixed 0 ((1+s)::E) 0 := join_mixed [] E 0 1 s 0
  have back : W.reverse=mixed 0 R 0 := by rw [form,reverse_mixed,List.reverse_cons]
  have vback : v.reverse=K++run s := by
    change (mixed s E 0).reverse=_
    rw [reverse_mixed]
    simpa only [Nat.zero_add,K] using (append_pure E.reverse 0 0 s).symm
  have shorter := m.cuts false
  change ¬NamedCode (pieces [a,b,a] ([b,a]++v) v) at shorter
  have rev := swap_last_ambiguity (reverse_ambiguity shorter)
  have test : ¬NamedCode (pieces [a,b,a] (K++run s) ((K++run s)++[a,b])) := by
    simpa only [List.reverse_append,vback,show [b,a].reverse=[a,b] from rfl,
      show [a,b,a].reverse=[a,b,a] from rfl] using rev
  have large := m.cuts true
  change ¬NamedCode (pieces [a,b,a] W [a]) at large
  have reversed := reverse_ambiguity (Border.cycle_ambiguity large)
  rw [back] at reversed
  have sep : ¬NamedCode (layout 1 [] 1 0 R 0) := reversed
  obtain ⟨d,k,shape⟩ := Border.blocks_from_prefix_bound R sep (bounded_long_block E.reverse s bound test)
  let B := Border.body d 2
  let h := [a]++B
  have BW : W.reverse=B++wordPow h k := by rw [back,shape,Border.body_blocks]
  have pal : (B++wordPow h k).reverse=B++wordPow h k := by
    rw [List.reverse_append,Border.reverse_pow]
    change wordPow (([a]++Border.body d 2).reverse) k++(Border.body d 2).reverse=_
    simp only [List.reverse_append,Border.body_reverse,show [a].reverse=[a] from rfl]
    exact rotate_power B [a] k
  have word : W=B++wordPow h k := (by simpa only [List.reverse_reverse,pal] using congrArg List.reverse BW)
  have one : [a]++W=wordPow h (k+1) := by rw [word,wordPow_succ']; simp [h]
  have two : wordPow [a,b,a] (d+1)++W=wordPow h (k+2) := by
    rw [Border.aba_body,word,wordPow_succ' h (k+1),wordPow_succ' h k]
    simp [h,B,List.append_assoc]
  let f := pieces [a,b,a] W ([a]++W)
  have good : NamedCode f := m.code
  have equation : spell f ((List.replicate (d+1) P++[Q])++[Z])=
      spell f (Z::(List.replicate (d+1) P++[Q])) := by
    simp only [spell_append,spell_cons,spell_nil,List.append_nil,spell_replicate]
    change (wordPow [a,b,a] (d+1)++W)++([a]++W)=([a]++W)++(wordPow [a,b,a] (d+1)++W)
    rw [one,two]; exact wordPow_comm ..
  have names := good equation
  rw [List.replicate_succ] at names
  exact (by decide : P≠Z) (List.cons.inj names).1

theorem overlap_left (t v : Word Bool) (m : Model .overlap t [a] v) : False := by
  obtain ⟨G,E,r,s,q,tf,vf,ends,bound,cop⟩ := lateral_overlap_forms m
  by_cases empty : G=[]
  · subst G
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have tb : t=[b] := tf
      subst t
      exact overlap_central _ _ (m.flip b ⟨P,rfl⟩)
    · have tba : t=[b,a] := tf
      exact overlap_ba E s bound (tba ▸ vf ▸ m)
  · exact overlap_many G E r s q (List.length_pos_iff.mpr empty) cop ends bound (tf ▸ vf ▸ m)

theorem overlap_impossible (t u v : Word Bool) : ¬Model .overlap t u v := by
  intro m
  obtain ⟨k,unit⟩ := m.letter
  rcases k with _|(_|_)
  · change v=[a] at unit
    subst v
    exact overlap_left t.reverse u.reverse (m.reverse (by decide))
  · change t=[a] at unit
    exact overlap_central u v (unit ▸ m)
  · change u=[a] at unit
    exact overlap_left t v (unit ▸ m)

end ThreeWordCodes.CrossedCase
