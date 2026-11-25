module

public import ThreeWordCodes.BorderConstraints
public import ThreeWordCodes.LetterTheorem

/-! # Reducing a shortest border obstruction to a binary model with one letter -/

@[expose] public section
namespace ThreeWordCodes.Border

theorem two_ends (d : Fin 3 → Word Bool) (view : Word Bool → Option Bool)
    (all : ∀ b,∃ i,view (d i)=some b) : ∃ i j,view (d i)≠view (d j) := by
  obtain ⟨i,hi⟩ := all false
  obtain ⟨j,hj⟩ := all true
  exact ⟨i,j,by rw [hi,hj]; decide⟩

private theorem noncommuting_of_head {x z : Word Bool} (nx : x≠[]) (nz : z≠[]) (diff : x.head?≠z.head?) :
    x++z≠z++x := fun eqn => diff
      ((append_head_of_nonempty nx z).symm.trans ((congrArg List.head? eqn).trans (append_head_of_nonempty nz x)))

theorem normalized_with_a (orig : Fin 3 → Word Bool) (nz : ∀ k,orig k≠[])
    (amb : ¬NamedCode orig) (indep : HasNoncommutingPair orig) :
    ∃ d : Fin 3 → Word Bool, SameEquations orig d ∧ (∃ k,d k=[false]) ∧
      (∀ c,∃ k,(d k).head?=some c) ∧ (∀ c,∃ k,(d k).getLast?=some c) ∧
      ∀ c m,(∀ k,m∣(d k).count c) → m∣1 := by
  obtain ⟨v,eqn,⟨k,b,single⟩,first,last,div⟩ :=
    normalize_letter_realization nz amb indep (letter_realization orig nz amb indep.nonperiodic)
  let d (j : Fin 3) := (v j).map (letterFlip b)
  refine ⟨d,eqn.trans (flip_equations v b),⟨k,?_⟩,?_,?_,?_⟩
  · cases b <;> simp [d,single,letterFlip]
  · intro c
    obtain ⟨j,h⟩ := first (letterFlip b c)
    exact ⟨j,by simp [d,h]⟩
  · intro c
    obtain ⟨j,h⟩ := last (letterFlip b c)
    exact ⟨j,by simp [d,h]⟩
  · intro c m all
    apply div (letterFlip b c) m
    intro j
    have keys := List.count_map_of_injective (v j) (letterFlip b)
      (Function.LeftInverse.injective (letterFlip_twice b)) (letterFlip b c)
    simpa [d,←keys] using all j

/-- For a given ordering of a shortest obstruction, carry the constraints
to an equation-equivalent model on the same names. -/
theorem Form.to_model {f : Fin 3 → Word Bool} (input : ClassificationInput f) (bad : ¬Completable f)
    {x y z : Word Bool} (data : Form x y) (order : Option Bool ≃ Fin 3)
    (form : (fun k => f (order k))=family data.p data.q z data.n data.i data.j)
    (initial : x.head?≠z.head?) (final : x.reverse.head?≠z.reverse.head?) :
    ∃ u v w,SameEquations (pieces data.p data.q z) (pieces u v w) ∧ Model u v w data.n data.i data.j := by
  let p := data.p
  let q := data.q
  let n := data.n
  let i := data.i
  let j := data.j
  have code : NamedCode (family p q z n i j) := form ▸ input.code.reindex order.injective
  have no : ¬Completable (family p q z n i j) :=
    fun h => bad ((completable_reindex_iff f order).mp (form.symm ▸ h))
  have baseCode := data.words z ▸ code
  have baseNo := data.words z ▸ no
  obtain ⟨px,pxr,qz,qzr⟩ := data.marked_ends baseCode baseNo initial final
  have pz : p.head?≠z.head? := fun h => initial (px.symm.trans h)
  have pzr : p.getLast?≠z.getLast? := by
    simpa only [List.head?_reverse] using (fun h => final (pxr.symm.trans h) : p.reverse.head?≠z.reverse.head?)
  have qzl : q.getLast?=z.getLast? := by simpa only [List.head?_reverse] using qzr
  let g := pieces p q z
  let o := threeOrder
  let orig (k : Fin 3) := g (o.symm k)
  have names (k : Option Bool) : orig (o k)=g k := by simp [orig]
  have nz (k : Fin 3) : orig k≠[] := by
    obtain ⟨t,rfl⟩ := o.surjective k
    rw [names]
    rcases t with _ | (_|_)
    · exact code.entry_ne_nil none
    · exact data.p_nonempty
    · exact data.q_nonempty
  have actualCuts := all_cuts_ambiguous input bad p q z n i j data.p_nonempty order form
  have amb : ¬NamedCode orig := by
    intro coded
    have hg : NamedCode g := by simpa only [names] using coded.reindex o.injective
    exact actualCuts .pieces hg
  have independent : HasNoncommutingPair orig :=
    ⟨o P,o Z,by rw [names,names]; exact noncommuting_of_head data.p_nonempty (code.entry_ne_nil none) pz⟩
  obtain ⟨d,eqn,⟨k,single⟩,first,last,div⟩ := normalized_with_a orig nz amb independent
  let u := d (o P)
  let v := d (o Q)
  let w := d (o Z)
  have dn (t : Option Bool) : d (o t)=pieces u v w t := by rcases t with _ | (_|_) <;> rfl
  have nzD (k : Fin 3) : d k≠[] := by
    intro ew
    apply nz k
    have e := (eqn [k] []).mpr (by simp [ew])
    simpa using e
  have rel : SameEquations g (pieces u v w) := by
    have reindexed : SameEquations (fun t => orig (o t)) (fun t => d (o t)) := by
      intro s t
      simpa only [spell_rename] using eqn (s.map o) (t.map o)
    simpa only [names,dn] using reindexed
  have actualFirst : ∃ a b,(orig a).head?≠(orig b).head? := ⟨o P,o Z,by rw [names,names]; exact pz⟩
  have actualLast : ∃ a b,(orig a).getLast?≠(orig b).getLast? := ⟨o P,o Z,by rw [names,names]; exact pzr⟩
  have heads := same_initial_pairs eqn amb nz nzD actualFirst (two_ends d List.head? first)
  have tails := same_final_pairs eqn amb nz nzD actualLast (two_ends d List.getLast? last)
  have nhead (a b : Option Bool) : (g a).head?=(g b).head? ↔ (pieces u v w a).head?=(pieces u v w b).head? := by
    simpa only [names,dn] using heads (o a) (o b)
  have ntail (a b : Option Bool) : (g a).getLast?=(g b).getLast? ↔ (pieces u v w a).getLast?=(pieces u v w b).getLast? := by
    simpa only [names,dn] using tails (o a) (o b)
  refine ⟨u,v,w,rel,?_⟩
  refine ⟨fun t => dn t ▸ nzD (o t),⟨o.symm k,?_⟩,
    ⟨fun e => pz ((nhead P Z).mpr e),(nhead Q Z).mp qz⟩,
    ⟨fun e => pzr ((ntail P Z).mpr e),(ntail Q Z).mp qzl⟩,?_,
    (transfer_family rel n i j).namedCode_iff.mp code,?_,?_,?_,?_,?_,?_⟩
  · rw [←dn,Equiv.apply_symm_apply]; exact single
  · intro b m h
    apply div b m
    intro t
    obtain ⟨t,rfl⟩ := o.surjective t
    rw [dn]; exact h t
  · intro s hc
    exact actualCuts s ((transfer_cut rel s n).namedCode_iff.mpr hc)
  · intro side hc
    exact end_cuts_ambiguous input bad p q z n i j order form side ((transfer_endCut rel side n i j).namedCode_iff.mpr hc)
  · rintro ⟨s,read⟩
    exact no (third_on_pieces p q z n i j code ⟨s,(transfer_reading rel P Q Z s).mpr read⟩)
  · rintro ⟨s,read⟩
    exact no (second_on_others p q z n i j code ⟨s,(transfer_reading rel P Z Q s).mpr read⟩)
  · intro comm
    have badEq := (rel [Q,Z] [Z,Q]).mpr (by simpa [pieces,addToken,pair,Q,Z] using comm)
    exact no (commuting_second_third p q z n i j code (by simpa [g,pieces,addToken,pair,Q,Z] using badEq))
  · intro e h
    have sh : short p q n=x := data.short_word.symm
    exact no (forbidden_identity p q z n i j e (sh.symm ▸ initial)
      ((congrArg List.reverse sh).symm ▸ final) ((transfer_commuting rel (e+1)).mpr h) code)

/-- Eliminating the three possible locations of the unique letter in the
model suffices for every border of a shortest binary obstruction. -/
theorem border_of_no_model
    (exclude : ∀ p q z n i j,¬Model p q z n i j)
    (f : Fin 3 → Word Bool) (input : ClassificationInput f) (border : HasBorder f) : Completable f := by
  by_contra bad
  obtain ⟨x,y,z,data,order,form,initial,final⟩ := border_has_form input border
  obtain ⟨u,v,w,_,model⟩ := data.to_model input bad order form initial final
  exact exclude u v w _ _ _ model

end ThreeWordCodes.Border
