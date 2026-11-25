module

public import ThreeWordCodes.BorderIdentity
public import ThreeWordCodes.CrossedForms

/-! # The four ambiguous shortenings of a minimal bordered triple -/

@[expose] public section
namespace ThreeWordCodes.Border

variable {A : Type*}

inductive Cut
  | middle | leftJoin | rightJoin | pieces
  deriving DecidableEq

/-- In order, these are (x,qp,z), (p,qp,z), (p,pq,z) and (p,q,z). -/
def cutWords (side : Cut) (p q z : Word A) (n : ℕ) : Option Bool → Word A :=
  match side with
  | .middle => addToken (pair (short p q n) (q++p)) z
  | .leftJoin => addToken (pair p (q++p)) z
  | .rightJoin => addToken (pair p (p++q)) z
  | .pieces => addToken (pair p q) z

private def extra (target donor : Option Bool) (n : ℕ) (i : Option Bool) : Word (Option Bool) :=
  if i=target then List.replicate n donor else []

theorem surround [Fintype A] (x u z : Word A) (i j : ℕ)
    (done : Completable (addToken (pair x u) z)) :
    Completable (addToken (pair x (wordPow x i++u++wordPow x j)) z) := by
  let f := addToken (pair x u) z
  let l := extra (some true) (some false) i
  let r := extra (some true) (some false) j
  let g (s) := spell f (l s)++f s
  have eqn : (fun s => g s++spell g (r s))=addToken (pair x (wordPow x i++u++wordPow x j)) z := by
    funext s
    rcases s with _ | (_|_) <;> simp [l,r,f,g,extra,addToken,pair,spell_replicate]
  exact eqn ▸ (done.padLeft l).padRight r

/-- Padding on the pieces recovers the prescribed triple in all four cases. -/
theorem lift_cut [Fintype A] (side : Cut) (p q z : Word A) (n i j : ℕ)
    (code : NamedCode (family p q z n i j)) (done : Completable (cutWords side p q z n)) :
    Completable (family p q z n i j) := by
  let x := short p q n
  cases side with
  | middle => exact surround x (q++p) z (i+1) j done
  | leftJoin =>
    let g := addToken (pair p (q++p)) z
    let r := extra (some false) (some true) n
    have form : (fun k => g k++spell g (r k))=addToken (pair x (q++p)) z := by
      funext k; rcases k with _ | (_|_) <;> simp [g,r,extra,addToken,pair,spell_replicate,x,short]
    have small : Completable (addToken (pair x (q++p)) z) := form ▸ done.padRight r
    exact surround x (q++p) z (i+1) j small
  | rightJoin =>
    let g := addToken (pair p (p++q)) z
    let l := extra (some false) (some true) n
    have form : (fun k => spell g (l k)++g k)=addToken (pair x (p++q)) z := by
      funext k; rcases k with _ | (_|_) <;> simp [g,l,extra,addToken,pair,spell_replicate,x,short,rotate_power]
    have small : Completable (addToken (pair x (p++q)) z) := form ▸ done.padLeft l
    have word : wordPow x i++(p++q)++wordPow x (j+1)=wordPow x (i+1)++(q++p)++wordPow x j := by
      rw [wordPow_succ' x j,wordPow_succ x i]
      simpa only [List.append_assoc] using congrArg (fun w => wordPow x i++w++wordPow x j)
        (short_shift p q n).symm
    have complete := surround x (p++q) z i (j+1) small
    rw [word] at complete
    exact complete
  | pieces => exact of_completable_pieces p q z n i j code done

/-- A shortest binary obstruction can invoke the induction hypothesis on
a triple in any fixed ordering of its three entries. -/
theorem shorter_named {f : Fin 3 → Word Bool} (input : ClassificationInput f)
    (order : Option Bool ≃ Fin 3) (w : Option Bool → Word Bool)
    (le : ∀ i,(w i).length≤(f (order i)).length)
    (strict : ∃ i,(w i).length<(f (order i)).length) (code : NamedCode w) : Completable w := by
  have small : totalWordLength (fun i => w (order.symm i)) < totalWordLength f := by
    apply Finset.sum_lt_sum
    · intro i _
      simpa only [Equiv.apply_symm_apply] using le (order.symm i)
    · obtain ⟨i,h⟩ := strict
      exact ⟨order i,Finset.mem_univ _,by simpa only [Equiv.symm_apply_apply] using h⟩
  have done := input.shorter _ small (code.reindex order.symm.injective)
  simpa only [Equiv.symm_apply_apply] using done.reindex order.injective

theorem all_cuts_ambiguous {f : Fin 3 → Word Bool} (input : ClassificationInput f) (bad : ¬Completable f)
    (p q z : Word Bool) (n i j : ℕ) (np : p≠[]) (order : Option Bool ≃ Fin 3)
    (form : (fun k => f (order k))=family p q z n i j) (side : Cut) :
    ¬NamedCode (cutWords side p q z n) := by
  have hp := List.length_pos_iff.mpr np
  have leX : p.length≤(short p q n).length := by simp [short]
  have xPos : 0<(short p q n).length := by omega
  have strict : q.length+p.length <
      (wordPow (short p q n) (i+1)++(q++p)++wordPow (short p q n) j).length := by
    rw [wordPow_succ']; simp only [List.length_append]; omega
  have shortSecond : (cutWords side p q z n (some true)).length < (f (order (some true))).length := by
    rw [congrFun form (some true)]
    cases side <;> simp only [cutWords,family,addToken,pair,List.length_append] at * <;> omega
  have le (s : Option Bool) : (cutWords side p q z n s).length≤(f (order s)).length := by
    rcases s with _ | (_|_)
    · rw [congrFun form none]; cases side <;> rfl
    · rw [congrFun form (some false)]
      cases side <;> first | exact Nat.le_refl _ | exact leX
    · exact shortSecond.le
  intro code
  have small := shorter_named input order _ le ⟨some true,shortSecond⟩ code
  have result := lift_cut side p q z n i j (form ▸ input.code.reindex order.injective) small
  exact bad ((completable_reindex_iff f order).mp (form.symm ▸ result))

private theorem opposite {x y z : Word Bool} (nx : x≠[]) (same : x.head?=y.head?)
    (both : ∀ c,∃ t : Option Bool,(addToken (pair x y) z t).head?=some c) : x.head?≠z.head? := by
  obtain ⟨a,w,hx⟩ := List.exists_cons_of_ne_nil nx
  intro equalEnd
  obtain ⟨t,ht⟩ := both (!a)
  have hxval : x.head?=some a := by simp [hx]
  have all (k : Option Bool) : (addToken (pair x y) z k).head?=some a := by
    rcases k with _ | (_|_)
    · exact equalEnd.symm.trans hxval
    · exact hxval
    · exact same.symm.trans hxval
  have contradiction := (all t).symm.trans ht
  cases a <;> simp at contradiction

/-- Equation (2) with an ordering of the input and the distinct ends of x
and z. Both end conditions follow from the classification input. -/
theorem border_has_form {f : Fin 3 → Word Bool} (input : ClassificationInput f) (border : HasBorder f) :
    ∃ x y z : Word Bool, ∃ data : Form x y, ∃ order : Option Bool ≃ Fin 3,
      (fun k => f (order k))=family data.p data.q z data.n data.i data.j ∧
      x.head?≠z.head? ∧ x.reverse.head?≠z.reverse.head? := by
  obtain ⟨i,j,pr,sf⟩ := border
  have ij : i≠j := by rintro rfl; exact Nat.lt_irrefl _ pr.2
  have third : ∀ a b : Fin 3,a≠b → ∃ k,a≠k ∧ b≠k := by decide
  obtain ⟨k,ik,jk⟩ := third i j ij
  obtain ⟨d⟩ := normal_form (input.code.entry_ne_nil i) pr.1 sf.1 (input.code.noncommuting_entries ij)
  obtain ⟨order,arr⟩ := order_three_entries ij ik jk (addToken (pair (f i) (f j)) (f k)) rfl rfl rfl
  have seen (c : Bool) : ∃ t,(addToken (pair (f i) (f j)) (f k) t).head?=some c := by
    obtain ⟨v,hv⟩ := input.firstLetters c
    exact ⟨order.symm v,by rw [←congrFun arr (order.symm v),Equiv.apply_symm_apply]; exact hv⟩
  have endSeen (c : Bool) : ∃ t,(addToken (pair (f i).reverse (f j).reverse) (f k).reverse t).head?=some c := by
    obtain ⟨v,hv⟩ := input.lastLetters c
    refine ⟨order.symm v,?_⟩
    have iden (t : Option Bool) :
        addToken (pair (f i).reverse (f j).reverse) (f k).reverse t=(f (order t)).reverse := by
      have eqn := congrArg List.reverse (congrFun arr t).symm
      rcases t with _ | (_|_) <;> exact eqn
    simpa [iden] using hv
  have nx := input.code.entry_ne_nil i
  exact ⟨_,_,_,d,order,arr.trans (d.words _).symm,opposite nx (head_of_prefix nx pr.1) seen,
    opposite (by simpa using nx) (head_of_prefix (by simpa using nx) sf.1.reverse) endSeen⟩

end ThreeWordCodes.Border
