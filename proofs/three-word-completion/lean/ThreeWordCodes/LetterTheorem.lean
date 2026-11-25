module

public import ThreeWordCodes.NormalizedStep
public import ThreeWordCodes.LetterInduction
public import Mathlib.Data.List.Count

/-! # Existence of equation-preserving binary letter models (Lemma 4)

A shortest letter model of the shortened list is put in binary normal form.
If the letter is exactly the name being lengthened, the P, Pa, Q analysis
supplies a new letter model.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A B I J : Type*}

private theorem HasLetterRealization.reindex {v : I → Word A} (h : HasLetterRealization v)
    (e : J ≃ I) : HasLetterRealization (fun j => v (e j)) := by
  obtain ⟨d,rels,k,c,one⟩ := h
  refine ⟨fun j => d (e j),fun s t => ?_,e.symm k,c,by simpa using one⟩
  simpa only [spell_rename] using rels (s.map e) (t.map e)

theorem flip_equations (v : I → Word Bool) (c : Bool) :
    SameEquations v (fun k => (v k).map (letterFlip c)) := by
  have hi : Function.Injective (letterFlip c) := Function.LeftInverse.injective (letterFlip_twice c)
  intro s t
  simp only [map_spell]
  exact ⟨congrArg (List.map _),fun e => List.map_injective_iff.mpr hi e⟩

private theorem transport_nc {v : I → Word A} {w : I → Word B} (rel : SameEquations v w)
    (nc : ∀ i j, i≠j → v i ++ v j ≠ v j ++ v i) :
    ∀ i j, i≠j → w i ++ w j ≠ w j ++ w i := by
  intro i j ne he
  apply nc i j ne
  simpa using (rel [i,j] [j,i]).mpr (by simpa using he)

namespace BinaryGaps

private theorem only_a (w : Word Bool) (no : b ∉ w) : w = run w.length :=
  List.eq_replicate_iff.mpr ⟨rfl,fun x hx => by cases x <;> first | rfl | exact (no hx).elim⟩

theorem head_zero {i g j} (x : (mixed i g j).head? = some b) : i=0 := by
  cases i with
  | zero => rfl
  | succ i => simp [mixed,run,List.replicate_succ,a,b] at x

theorem last_zero {i g j} (x : (mixed i g j).getLast? = some b) : j=0 := by
  apply head_zero (g:=g.reverse) (j:=i)
  simpa only [←reverse_mixed,List.head?_reverse] using x

private theorem lift_pure_third (P : Word Bool) (n : ℕ) (hb : b∈P) :
    HasLetterRealization (addToken (pair P (P++[a])) (run n)) := by
  let base := pair [a] P
  have independent : NamedCode base := (named_pair_iff_noncommuting _ _).mpr
    (fun commute => false_commutes_excludes_true commute hb)
  let d := addToken (pair [b] [b,a]) (run n)
  have pure (m : ℕ) : spell base (run m) = run m := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (a :: ·) ih
  have e : (fun k => spell base (d k)) = addToken (pair P (P++[a])) (run n) := by
    funext k
    rcases k with _ | (_ | _)
    · exact pure n
    · exact List.append_nil _
    · simp [d,base,addToken,pair,a,b]
  exact ⟨d,e ▸ (independent.preserves_equations d).symm,some false,b,rfl⟩

private theorem canonical_lengthening (P Q : Word Bool)
    (old : ¬ NamedCode (addToken (pair [a] P) Q)) (new : ¬ NamedCode (addToken (pair P (P++[a])) Q))
    (left : P.head?=some b ∨ Q.head?=some b) (right : P.getLast?=some b ∨ Q.getLast?=some b)
    (div : ∀ m, m∣P.count b → m∣Q.count b → m∣1)
    (pp : P ++ (P++[a]) ≠ (P++[a]) ++ P) (pq : P ++ Q ≠ Q ++ P)
    (paq : (P++[a]) ++ Q ≠ Q ++ (P++[a])) :
    HasLetterRealization (addToken (pair P (P++[a])) Q) := by
  have has : b∈P := by
    by_contra missing
    have pure := only_a P missing
    have comm : P++[a] = [a]++P := by
      rw [pure]
      change run P.length ++ run 1 = run 1 ++ run P.length
      rw [←run_add,←run_add,Nat.add_comm]
    exact pp (by rw [List.append_assoc,←comm])
  by_cases marker : b∈Q
  · obtain ⟨i,g,j,rfl⟩ := mixed_of_contains_marker has
    obtain ⟨h,e,q,rfl⟩ := mixed_of_contains_marker marker
    have mul : mixed i g j ++ [a] = mixed i g (j+1) := append_pure g i j 1
    rw [mul] at new pp paq ⊢
    apply normalized_binary_lengthening old new (left.imp head_zero head_zero)
      (right.imp last_zero last_zero) _ pq paq
    simp only [mixed_count] at div
    exact Nat.dvd_one.mp (div _ (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_left ..))
  · rw [only_a Q marker]
    exact lift_pure_third _ _ has

end BinaryGaps

private theorem a_third (i j : Fin 3) (ne : i≠j) :
    ∃ k, Function.Bijective (threeNames j i k) ∧ Function.Bijective (threeNames i j k) ∧ k≠j ∧ k≠i := by
  revert i j
  decide

/-- Undoing any left shortening of the sole letter in an ambiguous binary
letter model preserves the existence of a letter model. -/
theorem letter_lengthening_case : LetterLengtheningCase := by
  classical
  intro d i j ij nz amb unary _ outputNC outputAmb
  obtain ⟨k,oldOrder,newOrder,kj,ki⟩ := a_third i j ij
  have different : HasNoncommutingPair d := ⟨i,k,by simpa [lengthen,ij,kj] using outputNC i k (Ne.symm ki)⟩
  obtain ⟨v,rels,⟨one,c,hc⟩,heads,lasts,div⟩ :=
    normalize_letter_realization nz amb different ⟨d,fun _ _ => Iff.rfl,j,unary⟩
  by_cases remains : one ≠ j
  · exact ⟨_,rels.lengthen i j,one,c,by simp [lengthen,remains,hc]⟩
  have one_eq : one=j := not_ne_iff.mp remains
  subst one
  let f (u : Fin 3) := (v u).map (letterFlip c)
  have letter : f j = [BinaryGaps.a] := by cases c <;> simp [f,hc,letterFlip,BinaryGaps.a]
  have same : SameEquations d f := rels.trans (flip_equations v c)
  have after := same.lengthen i j
  let P := f i
  let Q := f k
  let ov := addToken (pair [BinaryGaps.a] P) Q
  let nv := addToken (pair P (P++[BinaryGaps.a])) Q
  let ei := Equiv.ofBijective _ oldOrder
  let eo := Equiv.ofBijective _ newOrder
  have namesOld : (fun x => f (ei x)) = ov := by
    funext x
    rcases x with _ | (_ | _)
    · rfl
    · exact letter
    · rfl
  have namesNew : (fun x => lengthen i j f (eo x)) = nv := by
    funext x
    rcases x with _ | (_ | _)
    · change lengthen i j f k = Q
      simp [lengthen,kj,Q]
    · change lengthen i j f i = P
      simp [lengthen,ij,P]
    · change lengthen i j f j = P++[BinaryGaps.a]
      simp [lengthen,letter,P]
  have oldFail : ¬ NamedCode ov := by
    intro hc
    rw [←namesOld] at hc
    exact amb (same.namedCode_iff.mpr (by simpa using hc.reindex ei.symm.injective))
  have newFail : ¬ NamedCode nv := by
    intro hc
    rw [←namesNew] at hc
    exact outputAmb (after.namedCode_iff.mpr (by simpa using hc.reindex eo.symm.injective))
  have oneEnd (ψ : Word Bool → Option Bool) (endmap : ∀ w, ψ (w.map (letterFlip c)) = (ψ w).map (letterFlip c))
      (lit : ψ [BinaryGaps.a] = some BinaryGaps.a) (all : ∀ b, ∃ i, ψ (v i)=some b) :
      ψ P=some BinaryGaps.b ∨ ψ Q=some BinaryGaps.b := by
    obtain ⟨t,ht⟩ := all (letterFlip c BinaryGaps.b)
    have end' : ψ (f t) = some BinaryGaps.b := by simp [f,endmap,ht]
    obtain ⟨z,rfl⟩ := ei.surjective t
    change ψ ((fun x => f (ei x)) z) = some BinaryGaps.b at end'
    rcases z with _ | (_ | _)
    · exact Or.inr end'
    · change ψ (f j) = some BinaryGaps.b at end'
      rw [letter,lit] at end'
      contradiction
    · exact Or.inl end'
  have count (u : Fin 3) : (f u).count BinaryGaps.b = (v u).count (letterFlip c BinaryGaps.b) := by
    simpa [f] using (List.count_map_of_injective (v u) (letterFlip c)
      (Function.LeftInverse.injective (letterFlip_twice c)) (letterFlip c BinaryGaps.b))
  have gcd (m : ℕ) (pi : m∣P.count BinaryGaps.b) (qi : m∣Q.count BinaryGaps.b) : m∣1 := by
    apply div (letterFlip c BinaryGaps.b) m
    intro t
    rw [←count]
    obtain ⟨z,rfl⟩ := ei.surjective t
    rcases z with _ | (_ | _)
    · exact qi
    · change m ∣ (f j).count BinaryGaps.b
      simp [letter,BinaryGaps.b,BinaryGaps.a]
    · exact pi
  have nc := transport_nc after outputNC
  have p := nc i j ij
  have r := nc i k (Ne.symm ki)
  have s := nc j k (Ne.symm kj)
  simp only [lengthen,ite_eq_right ij,ite_true,ite_eq_right kj,letter] at p r s
  obtain ⟨model,eqs,letter'⟩ := BinaryGaps.canonical_lengthening P Q oldFail newFail
    (oneEnd List.head? (by simp) rfl heads) (oneEnd List.getLast? (by simp) rfl lasts) gcd p r s
  have back : HasLetterRealization (lengthen i j f) := by
    have h : HasLetterRealization nv := ⟨model,eqs,letter'⟩
    rw [←namesNew] at h
    simpa using h.reindex eo.symm
  obtain ⟨z,en,hw⟩ := back
  exact ⟨z,after.trans en,hw⟩

/-- Every ambiguous nonperiodic triple of nonempty words over a finite
alphabet has an equation-preserving binary model with a letter entry. -/
theorem letter_realization [Fintype A] (v : Fin 3 → Word A) (nz : ∀ i, v i ≠ [])
    (amb : ¬ NamedCode v) (np : Nonperiodic v) : HasLetterRealization v :=
  letter_realization_of_lengthening letter_lengthening_case v nz amb np

namespace BinaryGaps

/-- Lemma 4 of the manuscript. The returned equivalence gives the permutation
of the original token names. A mixed word with m markers has m-1 internal
gaps, so both off-letter counts are positive by construction. -/
theorem binary_letter_normal_form [Fintype A] (v : Fin 3 → Word A) (nz : ∀ k, v k ≠ [])
    (amb : ¬ NamedCode v) (nc : ∀ i j, i≠j → v i ++ v j ≠ v j ++ v i) :
    ∃ order : Option Bool ≃ Fin 3, ∃ i g j h e q,
      SameEquations (fun k => v (order k)) (layout i g j h e q) ∧
      (i=0 ∨ h=0) ∧ (j=0 ∨ q=0) ∧ (e.length+1).Coprime (g.length+1) ∧
      ((g=[] ∧ ∀ z ∈ e, max i j ≤ z) ∨ (e=[] ∧ ∀ z ∈ g, max h q ≤ z) ∨
       (0<g.length ∧ 0<e.length ∧ ∃ c>0, (∀ z ∈ g, z=c) ∧ (∀ z ∈ e, z=c) ∧
         i≤c ∧ j≤c ∧ h≤c ∧ q≤c)) := by
  have diff : HasNoncommutingPair v := ⟨0,1,nc 0 1 (by decide)⟩
  obtain ⟨v',eqn,⟨p,c,one⟩,heads,lasts,div⟩ := normalize_letter_realization nz amb diff
    (letter_realization v nz amb diff.nonperiodic)
  let f (k : Fin 3) := (v' k).map (letterFlip c)
  have pword : f p=[a] := by cases c <;> simp [f,one,letterFlip,a]
  have rel : SameEquations v f := eqn.trans (flip_equations v' c)
  have noncomm := transport_nc rel nc
  obtain ⟨u,z,bij⟩ := order_three p
  let order := Equiv.ofBijective _ bij
  have pu : p≠u := fun h => (by decide : (some false : Option Bool) ≠ some true) (bij.1 h)
  have pz : p≠z := fun h => (by decide : (some false : Option Bool) ≠ none) (bij.1 h)
  have uz : u≠z := fun h => (by decide : (some true : Option Bool) ≠ none) (bij.1 h)
  have has (k : Fin 3) (ne : p≠k) : b∈f k := by
    by_contra missing
    have pure := only_a (f k) missing
    apply noncomm p k ne
    rw [pword,pure]
    change run 1 ++ run _ = run _ ++ run 1
    rw [←run_add,←run_add,Nat.add_comm]
  obtain ⟨i,g,j,U⟩ := mixed_of_contains_marker (has u pu)
  obtain ⟨h,e,q,V⟩ := mixed_of_contains_marker (has z pz)
  have names : (fun k => f (order k)) = layout i g j h e q := by
    funext k
    rcases k with _ | (_ | _) <;> assumption
  have kernel : SameEquations (fun k => v (order k)) (layout i g j h e q) := by
    rw [←names]
    intro s t
    simpa only [spell_rename] using rel (s.map order) (t.map order)
  have bad : ¬ NamedCode (layout i g j h e q) := by
    intro h
    have hc := kernel.namedCode_iff.mpr h
    exact amb (by simpa using hc.reindex order.symm.injective)
  have endPair (ψ : Word Bool → Option Bool)
      (mapEnd : ∀ w, ψ (w.map (letterFlip c)) = (ψ w).map (letterFlip c))
      (lit : ψ [a] = some a) (all : ∀ b, ∃ k, ψ (v' k)=some b) :
      ψ (mixed i g j)=some b ∨ ψ (mixed h e q)=some b := by
    obtain ⟨k,hk⟩ := all (letterFlip c b)
    have mapped : ψ (f k) = some b := by simp [f,mapEnd,hk]
    obtain ⟨o,rfl⟩ := order.surjective k
    change ψ ((fun k => f (order k)) o) = some b at mapped
    rw [names] at mapped
    rcases o with _ | (_ | _)
    · exact Or.inr mapped
    · change ψ [a] = some b at mapped
      rw [lit] at mapped
      contradiction
    · exact Or.inl mapped
  let m := (e.length+1).gcd (g.length+1)
  have each (o : Option Bool) : m ∣ ((fun k => f (order k)) o).count b := by
    rw [names]
    rcases o with _ | (_ | _)
    · simpa only [layout,addToken,mixed_count] using (Nat.gcd_dvd_left (e.length+1) (g.length+1))
    · simp [layout,addToken,pair,a,b]
    · simpa only [layout,addToken,pair,mixed_count] using (Nat.gcd_dvd_right (e.length+1) (g.length+1))
  have cop : (e.length+1).Coprime (g.length+1) := by
    apply Nat.dvd_one.mp (div (letterFlip c b) m ?_)
    intro k
    have count : (f k).count b = (v' k).count (letterFlip c b) := by
      simpa [f] using (List.count_map_of_injective (v' k) (letterFlip c)
        (Function.LeftInverse.injective (letterFlip_twice c)) (letterFlip c b))
    rw [←count]
    simpa using each (order.symm k)
  refine ⟨order,i,g,j,h,e,q,kernel,
    (endPair List.head? (by simp) rfl heads).imp head_zero head_zero,
    (endPair List.getLast? (by simp) rfl lasts).imp last_zero last_zero,cop,?_⟩
  by_cases first : g=[]
  · subst g
    exact Or.inl ⟨rfl,one_marker_gaps (fun hc => bad hc.1)⟩
  by_cases second : e=[]
  · subst e
    exact Or.inr (Or.inl ⟨rfl,one_marker_gaps (fun hc => swapped_ambiguity bad hc.1)⟩)
  have pg := List.length_pos_iff.mpr first
  have pe := List.length_pos_iff.mpr second
  have unequal : g.length ≠ e.length := by
    intro eqn
    rw [eqn,Nat.coprime_self] at cop
    omega
  obtain ⟨c,gu,eu,bi,bj,bh,bq⟩ := uniform_gaps_of_distinct_counts bad pg pe unequal cop
  have positive : 0<c := by
    by_contra! hc
    have zero : c=0 := by omega
    have gz : g=List.replicate g.length 0 := List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (gu x hx).trans zero⟩
    have ez : e=List.replicate e.length 0 := List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (eu x hx).trans zero⟩
    apply noncomm u z uz
    rw [U,V,gz,ez,show i=0 by omega,show j=0 by omega,show h=0 by omega,show q=0 by omega,
      marker_power,marker_power]
    exact wordPow_comm ..
  exact Or.inr (Or.inr ⟨pg,pe,c,positive,gu,eu,bi,bj,bh,bq⟩)

end BinaryGaps
end ThreeWordCodes
