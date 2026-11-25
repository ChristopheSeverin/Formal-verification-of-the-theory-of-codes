module

public import ThreeWordCodes.BinaryReduction

/-! # Letter realizations and the pairs that share an end letter -/

@[expose] public section
namespace ThreeWordCodes
variable {A B I : Type*}

/-- A binary model on the same names in which one name spells a single letter. -/
def HasLetterRealization (v : I → Word A) : Prop :=
  ∃ d : I → Word Bool, SameEquations v d ∧ ∃ i b, d i = [b]

private theorem third_name : ∀ i j : Fin 3, i ≠ j →
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ x, x=i ∨ x=j ∨ x=k := by decide

/-- The commuting-pair base case in the induction of Lemma 4. -/
theorem letter_model_of_commuting_pair [Fintype A] (v : Fin 3 → Word A)
    (aperiodic : Nonperiodic v) {i j : Fin 3} (ne : i ≠ j) (comm : v i ++ v j = v j ++ v i) :
    HasLetterRealization v := by
  classical
  obtain ⟨k,ki,kj,cover⟩ := third_name i j ne
  obtain ⟨r,m,n,ri,rj⟩ := (commuting_iff_common_power _ _).mp comm
  have nc : r ++ v k ≠ v k ++ r := by
    intro h
    obtain ⟨s,p,q,hr,hk⟩ := (commuting_iff_common_power _ _).mp h
    apply aperiodic
    refine ⟨s,fun x => ?_⟩
    rcases cover x with rfl | rfl | rfl
    · exact ⟨p*m,by rw [ri,hr,wordPow_mul]⟩
    · exact ⟨p*n,by rw [rj,hr,wordPow_mul]⟩
    · exact ⟨q,hk⟩
  let inner := pair r (v k)
  let d (x : Fin 3) := if x = i then List.replicate m false else if x=j then List.replicate n false else [true]
  have actual : (fun x => spell inner (d x)) = v := by
    funext x
    rcases cover x with rfl | rfl | rfl
    · simpa [d,inner,spell_replicate,pair] using ri.symm
    · simpa [d,Ne.symm ne,inner,spell_replicate,pair] using rj.symm
    · simp [d,ki,kj,inner,pair]
  have kernel := (noncommuting_pair_completion _ _ nc).1.preserves_equations d
  rw [actual] at kernel
  exact ⟨d, fun s t => (kernel s t).symm, k,true,by simp [d,ki,kj]⟩

theorem SameEquations.reverse {v : I → Word A} {w : I → Word B} (h : SameEquations v w) :
    SameEquations (fun i => (v i).reverse) (fun i => (w i).reverse) := by
  intro s t
  simpa only [spell_reverse,List.reverse_inj] using h s.reverse t.reverse

theorem first_mismatched_names {v : I → Word A} (nz : ∀ i, v i ≠ []) (s t : Word I)
    (diff : s ≠ t) (eqn : spell v s = spell v t) :
    ∃ i j u z, i ≠ j ∧ spell v (i::u) = spell v (j::z) := by
  classical
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => exact (diff rfl).elim
    | cons j t => exact (nz j (List.append_eq_nil_iff.mp eqn.symm).1).elim
  | cons i u ih =>
    cases t with
    | nil => exact (nz i (List.append_eq_nil_iff.mp eqn).1).elim
    | cons j z =>
      by_cases pair : i = j
      · subst j
        exact ih z (fun e => diff (e ▸ rfl)) (List.append_cancel_left eqn)
      · exact ⟨i,j,u,z,pair,eqn⟩

private theorem equal_initials {v : I → Word A} (nz : ∀ i, v i ≠ [])
    {i j : I} {s t : Word I} (e : spell v (i::s) = spell v (j::t)) :
    (v i).head? = (v j).head? := by
  have first (u : I) (tail : Word A) : (v u ++ tail).head? = (v u).head? := by
    cases hu : v u with
    | nil => exact (nz u hu).elim
    | cons a z => rfl
  simpa only [spell_cons,first] using congrArg List.head? e

private theorem outsider {T : Type*} {v : Fin 3 → T} {i j k : Fin 3}
    (all : ∀ x, x=i ∨ x=j ∨ x=k) (sep : ∃ p q, v p ≠ v q) (same : v i = v j) :
    v k ≠ v i := by
  intro h
  obtain ⟨p,q,diff⟩ := sep
  apply diff
  rcases all p with rfl | rfl | rfl <;> rcases all q with rfl | rfl | rfl <;> grind

private theorem partition {f : Fin 3 → A} {g : Fin 3 → B} {i j : Fin 3} (ne : i≠j)
    (common : f i=f j) (other : g i=g j)
    (two : ∃ p q, f p ≠ f q) (two' : ∃ p q, g p ≠ g q) :
    ∀ p q, f p = f q ↔ g p = g q := by
  obtain ⟨k,_,_,all⟩ := third_name i j ne
  have a := outsider all two common
  have b := outsider all two' other
  intro p q
  rcases all p with rfl | rfl | rfl <;> rcases all q with rfl | rfl | rfl <;> grind

/-- A nontrivial equation fixes the equal-initial pair when each realization has
more than one initial letter (Section 2, after Lemma 4). -/
theorem same_initial_pairs {v : Fin 3 → Word A} {w : Fin 3 → Word B}
    (eqns : SameEquations v w) (amb : ¬ NamedCode v)
    (nv : ∀ i, v i ≠ []) (nw : ∀ i, w i ≠ [])
    (hv : ∃ i j, (v i).head? ≠ (v j).head?) (hw : ∃ i j, (w i).head? ≠ (w j).head?) :
    ∀ i j, (v i).head? = (v j).head? ↔ (w i).head? = (w j).head? := by
  classical
  change ¬ (∀ ⦃s t⦄, spell v s = spell v t → s = t) at amb
  push Not at amb
  obtain ⟨s,t,he,ne⟩ := amb
  obtain ⟨i,j,p,q,ij,eqn⟩ := first_mismatched_names nv s t ne he
  exact partition ij (equal_initials nv eqn) (equal_initials nw ((eqns _ _).mp eqn)) hv hw

theorem same_final_pairs {v : Fin 3 → Word A} {w : Fin 3 → Word B}
    (eqns : SameEquations v w) (amb : ¬ NamedCode v)
    (nv : ∀ i, v i ≠ []) (nw : ∀ i, w i ≠ [])
    (hv : ∃ i j, (v i).getLast? ≠ (v j).getLast?) (hw : ∃ i j, (w i).getLast? ≠ (w j).getLast?) :
    ∀ i j, (v i).getLast? = (v j).getLast? ↔ (w i).getLast? = (w j).getLast? := by
  have rev : ¬ NamedCode (fun i => (v i).reverse) := fun h => amb (by simpa using h.reverse)
  simpa using same_initial_pairs eqns.reverse rev (by simpa using nv) (by simpa using nw)
    (by simpa using hv) (by simpa using hw)

end ThreeWordCodes
