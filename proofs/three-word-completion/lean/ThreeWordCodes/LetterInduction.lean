module

public import ThreeWordCodes.Normalization

/-! # Isolating the remaining letter-realization case of Lemma 4

Left shortening preserves ambiguity in the reverse direction. Undoing it in a
binary model only requires an additional argument if the changed entry carried
the only single letter. Section 2 analyses the resulting triple P, Pa, Q.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A B : Type*}

def lengthen (i j : Fin 3) (v : Fin 3 → Word A) (k : Fin 3) : Word A :=
  if k=j then v i ++ v k else v k

private def template (i j k : Fin 3) : Word (Fin 3) :=
  (if k=j then [i] else []) ++ [k]

private theorem encode_template (i j : Fin 3) (v : Fin 3 → Word A) :
    (fun k => spell v (template i j k)) = lengthen i j v := by
  funext k
  by_cases h : k=j <;> simp [template,lengthen,h]

theorem SameEquations.lengthen {v : Fin 3 → Word A} {w : Fin 3 → Word B}
    (h : SameEquations v w) (i j : Fin 3) : SameEquations (lengthen i j v) (lengthen i j w) := by
  simpa only [encode_template] using h.substitution (template i j)

private theorem pairwise_transport {v : Fin 3 → Word A} {w : Fin 3 → Word B}
    (h : SameEquations v w) (nc : ∀ i j, i≠j → v i ++ v j ≠ v j ++ v i) :
    ∀ i j, i≠j → w i ++ w j ≠ w j ++ w i := by
  intro i j ne comm
  apply nc i j ne
  simpa using (h [i,j] [j,i]).mpr (by simpa using comm)

/-- The binary subproblem for the existence of a letter realization. Its three
input names encode P, a, Q before lengthening. After lengthening their images are
P, Pa, Q, up to permutation and exchange of the two alphabet letters. -/
def LetterLengtheningCase : Prop :=
  ∀ (d : Fin 3 → Word Bool) (i j : Fin 3), i ≠ j →
    (∀ k, d k ≠ []) → ¬ NamedCode d →
    (∃ b, d j = [b]) → (∀ k, k ≠ j → ∀ b, d k ≠ [b]) →
    (∀ p q, p ≠ q →
      lengthen i j d p ++ lengthen i j d q ≠ lengthen i j d q ++ lengthen i j d p) →
    ¬ NamedCode (lengthen i j d) → HasLetterRealization (lengthen i j d)

/-- A proof of the explicit binary lengthening subproblem supplies the
existence part of Lemma 4 over every finite alphabet. -/
theorem letter_realization_of_lengthening [Fintype A] (step : LetterLengtheningCase)
    (v : Fin 3 → Word A) (nz : ∀ k, v k ≠ []) (amb : ¬ NamedCode v) (np : Nonperiodic v) :
    HasLetterRealization v := by
  classical
  induction len : (∑ i, (v i).length) using Nat.strong_induction_on generalizing v with
  | ind n ih =>
    by_cases pair : ∃ i j, i≠j ∧ v i ++ v j = v j ++ v i
    · obtain ⟨i,j,ne,comm⟩ := pair
      exact letter_model_of_commuting_pair v np ne comm
    · have nc (i j : Fin 3) (ne : i≠j) : v i ++ v j ≠ v j ++ v i :=
        fun comm => pair ⟨i,j,ne,comm⟩
      have inj : Function.Injective v := by
        intro i j e
        by_contra ne
        exact nc i j ne (by rw [e])
      have hp : ¬ InformationTheory.IsPrefixFree (Set.range v) := fun hp => amb (completable_prefix inj nz hp).1
      change ¬ (∀ x ∈ Set.range v, ∀ y ∈ Set.range v, x <+: y → x=y) at hp
      push Not at hp
      obtain ⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,⟨r,e⟩,ne⟩ := hp
      have ij : i≠j := fun h => ne (congrArg v h)
      have nonzero : r≠[] := by rintro rfl; exact ne (by simpa using e)
      let w (k : Fin 3) := if k=j then r else v k
      have restored : lengthen i j w = v := by
        funext k
        by_cases h : k=j
        · subst k
          simpa [lengthen,w,ij] using e
        · simp [lengthen,w,h]
      have wne (k : Fin 3) : w k ≠ [] := by by_cases h : k=j <;> simp [w,h,nonzero,nz]
      have wamb : ¬ NamedCode w := by
        intro code
        apply amb
        rw [←restored,←encode_template]
        exact code.substitution (last_marked_code _)
      have wnp : Nonperiodic w := by
        rintro ⟨u,hu⟩
        apply np
        refine ⟨u,fun k => ?_⟩
        rw [←congrFun restored k]
        by_cases hk : k=j
        · obtain ⟨a,ha⟩ := hu i
          obtain ⟨b,hb⟩ := hu k
          refine ⟨a+b,?_⟩
          rw [lengthen,ite_eq_left hk,ha,hb,wordPow_add]
        · simpa [lengthen,hk] using hu k
      have smaller : r.length < (v j).length := by
        have lens : (v i).length + r.length = (v j).length := by
          simpa only [List.length_append] using congrArg List.length e
        have ipos := List.length_pos_iff.mpr (nz i)
        omega
      have total : (∑ k, (w k).length) < n := by
        rw [←len]
        exact Finset.sum_lt_sum (fun k _ => by by_cases h : k=j <;> simp [w,h,smaller.le])
          ⟨j,Finset.mem_univ _,by simpa [w] using smaller⟩
      obtain ⟨d,eqn,letter⟩ := ih _ total w wne wamb wnp rfl
      have lift := eqn.lengthen i j
      rw [restored] at lift
      by_cases survives : ∃ k, k≠j ∧ ∃ b, d k=[b]
      · obtain ⟨k,h,b,eb⟩ := survives
        exact ⟨_,lift,k,b,by simp [lengthen,h,eb]⟩
      · obtain ⟨k,b,mark⟩ := letter
        have kj : k=j := by by_contra h; exact survives ⟨k,h,b,mark⟩
        subst k
        have dn (k : Fin 3) : d k ≠ [] := fun empty => wne k (by
          simpa using (eqn [k] []).mpr (by simp [empty]))
        have da : ¬ NamedCode d := fun code => wamb (eqn.namedCode_iff.mpr code)
        obtain ⟨p,ep,one⟩ := step d i j ij dn da ⟨b,mark⟩
          (fun k ne b e => survives ⟨k,ne,b,e⟩) (pairwise_transport lift nc)
          (fun code => amb (lift.namedCode_iff.mpr code))
        exact ⟨p,lift.trans ep,one⟩

end ThreeWordCodes
