module

public import ThreeWordCodes.BorderSecondLetter
public import ThreeWordCodes.CrossedCommuting

/-! # The normalized binary model for the four crossed rows -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open Border (pieces P Q Z)
variable {A I : Type*}

/-- The indices name t,u,v in this order across all four rows. -/
def firstPair (row : CrossedShape) : Option Bool × Option Bool :=
  match row with
  | .sharedShort | .intermediate => (P,Z)
  | .disjoint => (Q,Z)
  | .overlap => (Q,P)

def lastPair (row : CrossedShape) : Option Bool × Option Bool :=
  match row with
  | .sharedShort | .intermediate => (P,Q)
  | .disjoint => (Q,Z)
  | .overlap => (P,Z)

private def pieceOrder : CrossedShape → Option Bool → Option Bool
  | .sharedShort,t => t
  | .intermediate,none => Q
  | .intermediate,some false => P
  | .intermediate,some true => Z
  | .disjoint,none => P
  | .disjoint,some false => Q
  | .disjoint,some true => Z
  | .overlap,none => Z
  | .overlap,some false => Q
  | .overlap,some true => P

private theorem piece_names (r : CrossedShape) (t u v : Word A) :
    (fun k => pieces t u v (pieceOrder r k))=crossedPieces r t u v := by
  funext k; cases r <;> rcases k with _|(_|_) <;> rfl

theorem spell_shortening (g : I → Word A) (r : CrossedShape) (b : Bool) (t u v : Word I) :
    (fun k => spell g (crossedShortening r b t u v k)) =
      crossedShortening r b (spell g t) (spell g u) (spell g v) := by
  funext k
  cases r <;> cases b <;> rcases k with _|(_|_) <;> simp [crossedShortening,pair,addToken]

structure Model (r : CrossedShape) (t u v : Word Bool) : Prop where
  nonempty : ∀ k,pieces t u v k≠[]
  letter : ∃ k,pieces t u v k=[false]
  divisors : ∀ c m,(∀ k,m∣(pieces t u v k).count c) → m∣1
  first : (pieces t u v (firstPair r).1).head?≠(pieces t u v (firstPair r).2).head?
  last : (pieces t u v (lastPair r).1).getLast?≠(pieces t u v (lastPair r).2).getLast?
  noncommuting : ∀ k l,k≠l → pieces t u v k++pieces t u v l≠pieces t u v l++pieces t u v k
  ambiguous : ¬NamedCode (pieces t u v)
  code : NamedCode (crossedWords r t u v)
  cuts : ∀ b,¬NamedCode (crossedShortening r b t u v)

theorem append_last {v : Word A} (h : v≠[]) (u : Word A) : (u++v).getLast?=v.getLast? := by
  simpa using Border.append_head_of_nonempty (u:=v.reverse) (by simpa using h) u.reverse

private theorem unequal_ends {f : Fin 3 → Word Bool} (input : ClassificationInput f)
    (r : CrossedShape) (t u v : Word Bool) (nt : t≠[]) (nu : u≠[]) (nv : v≠[])
    (order : Option Bool ≃ Fin 3) (form : (fun k => f (order k))=crossedWords r t u v) :
    (pieces t u v (firstPair r).1).head?≠(pieces t u v (firstPair r).2).head? ∧
    (pieces t u v (lastPair r).1).getLast?≠(pieces t u v (lastPair r).2).getLast? := by
  have avoid (get : Word Bool → Option Bool) (both : ∀ b,∃ j,get (f j)=some b)
      (x : Option Bool) : ¬∀ k,get (crossedWords r t u v k)=x := by
    intro common
    obtain ⟨i,hi⟩ := both false
    obtain ⟨j,hj⟩ := both true
    have one (s : Fin 3) : get (f s)=x := by
      simpa only [←congrFun form (order.symm s),Equiv.apply_symm_apply] using common (order.symm s)
    exact (by decide : (some false : Option Bool)≠some true) (hi.symm.trans ((one i).trans ((one j).symm.trans hj)))
  constructor
  · intro eqn
    apply avoid List.head? input.firstLetters ((pieces t u v (firstPair r).2).head?)
    intro k
    have nvt : v++t≠[] := by simp [nv]
    have nut : u++t≠[] := by simp [nu]
    cases r <;> rcases k with _|(_|_) <;>
      simp only [crossedWords,firstPair,pieces,addToken,pair,P,Q,Z] at eqn ⊢ <;>
      simp only [Border.append_head_of_nonempty nt,Border.append_head_of_nonempty nu,Border.append_head_of_nonempty nv,
        Border.append_head_of_nonempty nvt,Border.append_head_of_nonempty nut,eqn]
  · intro eqn
    apply avoid List.getLast? input.lastLetters ((pieces t u v (lastPair r).2).getLast?)
    intro k
    cases r <;> rcases k with _|(_|_) <;>
      simp only [crossedWords,lastPair,pieces,addToken,pair,P,Q,Z] at eqn ⊢ <;>
      simp only [append_last nt,append_last nu,append_last nv,eqn]

/-- On normalized names the hypothesized shortest counterexample has a letter
entry, a coded prescribed row and two ambiguous cuts with the indicated ends. -/
theorem to_model {f : Fin 3 → Word Bool} (input : ClassificationInput f) (bad : ¬Completable f)
    (r : CrossedShape) (t u v : Word Bool) (nt : t≠[]) (nu : u≠[]) (nv : v≠[])
    (order : Option Bool ≃ Fin 3) (form : (fun k => f (order k))=crossedWords r t u v) :
    ∃ T U V,SameEquations (pieces t u v) (pieces T U V) ∧ Model r T U V := by
  obtain ⟨anc,tu,tv,uv,cuts⟩ := crossed_obstruction_conditions input bad r t u v nt nu nv order form
  have ag : ¬NamedCode (pieces t u v) := by
    intro code
    have inj : Function.Injective (pieceOrder r) := by cases r <;> decide
    exact anc (piece_names r t u v ▸ code.reindex inj)
  have actual := unequal_ends input r t u v nt nu nv order form
  let g := pieces t u v
  let o := threeOrder
  let orig (k : Fin 3) := g (o.symm k)
  have names (k : Option Bool) : orig (o k)=g k := by simp [orig]
  have nz (k : Fin 3) : orig k≠[] := by
    obtain ⟨k,rfl⟩ := o.surjective k
    rw [names]; rcases k with _|(_|_) <;> assumption
  have amb : ¬NamedCode orig := fun h => ag (by simpa only [names] using h.reindex o.injective)
  have indep : HasNoncommutingPair orig := ⟨o P,o Q,by rw [names,names]; exact tu⟩
  obtain ⟨d,eqn,⟨k,single⟩,first,last,div⟩ := Border.normalized_with_a orig nz amb indep
  let T := d (o P)
  let U := d (o Q)
  let V := d (o Z)
  have dn (k : Option Bool) : d (o k)=pieces T U V k := by rcases k with _|(_|_) <;> rfl
  have rel : SameEquations g (pieces T U V) := by
    have reindexed : SameEquations (fun j => orig (o j)) (fun j => d (o j)) := by
      intro s t
      simpa only [spell_rename] using eqn (s.map o) (t.map o)
    simpa only [names,dn] using reindexed
  have nzd (k : Fin 3) : d k≠[] := by
    intro e
    have h := (eqn [k] []).mpr (by simp [e])
    exact nz k (by simpa using h)
  let L := firstPair r
  let R := lastPair r
  have actualFirst : ∃ i j,(orig i).head?≠(orig j).head? := ⟨o L.1,o L.2,by rw [names,names]; exact actual.1⟩
  have actualLast : ∃ i j,(orig i).getLast?≠(orig j).getLast? := ⟨o R.1,o R.2,by rw [names,names]; exact actual.2⟩
  have head := same_initial_pairs eqn amb nz nzd actualFirst (Border.two_ends d List.head? first) (o L.1) (o L.2)
  have tail := same_final_pairs eqn amb nz nzd actualLast (Border.two_ends d List.getLast? last) (o R.1) (o R.2)
  simp only [names,dn] at head tail
  have actualNC (k l : Option Bool) (ne : k≠l) : g k++g l≠g l++g k := by
    rcases k with _|(_|_) <;> rcases l with _|(_|_)
    all_goals first | exact (ne rfl).elim | exact tu | exact tu.symm | exact tv | exact tv.symm | exact uv | exact uv.symm
  refine ⟨T,U,V,rel,fun j => dn j ▸ nzd (o j),⟨o.symm k,?_⟩,?_,fun e => actual.1 (head.mpr e),
    fun e => actual.2 (tail.mpr e),?_,fun h => ag (rel.namedCode_iff.mpr h),?_,?_⟩
  · rw [←dn,Equiv.apply_symm_apply]; exact single
  · intro c m h
    apply div c m
    intro k
    obtain ⟨k,rfl⟩ := o.surjective k
    rw [dn]; exact h k
  · intro k l ne comm
    exact actualNC k l ne (by simpa using (rel [k,l] [l,k]).mpr (by simpa using comm))
  · have K := rel.substitution (crossedWords r [P] [Q] [Z])
    simp only [spell_crossed,g,pieces,spell_cons,spell_nil,List.append_nil,P,Q,Z,pair,addToken] at K
    exact K.namedCode_iff.mp (form ▸ input.code.reindex order.injective)
  · intro b h
    have K := rel.substitution (crossedShortening r b [P] [Q] [Z])
    simp only [spell_shortening,g,pieces,spell_cons,spell_nil,List.append_nil,P,Q,Z,pair,addToken] at K
    exact cuts b (K.namedCode_iff.mpr h)

theorem crossed_models_suffice.{u} (exclude : ∀ r t u v,¬Model r t u v) : ThreeWordTheorem.{u} := by
  apply four_crossed_rows_suffice
  intro f input table
  by_contra bad
  obtain ⟨r,t,u,v,nt,nu,nv,order,form⟩ := table
  obtain ⟨T,U,V,_,model⟩ := to_model input bad r t u v nt nu nv order form
  exact exclude r T U V model

end ThreeWordCodes.CrossedCase
