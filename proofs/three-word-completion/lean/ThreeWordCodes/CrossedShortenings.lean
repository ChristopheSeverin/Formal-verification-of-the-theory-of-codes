module

public import ThreeWordCodes.CrossedForms

/-! # Both shortenings in each of the four crossed rows are ambiguous -/

@[expose] public section
namespace ThreeWordCodes
variable {A : Type*}

/-- False selects the first shortening, true the second shortening in the four-row table in Section 5. -/
def crossedShortening (row : CrossedShape) (second : Bool) (t u v : Word A) : Option Bool → Word A :=
  match row,second with
  | .sharedShort,false => addToken (pair t u) (v++t)
  | .sharedShort,true => addToken (pair t (t++u)) v
  | .intermediate,false => addToken (pair t (v++t)) u
  | .intermediate,true => addToken (pair t v) (v++t++u)
  | .disjoint,false => addToken (pair u v) (t++v)
  | .disjoint,true => addToken (pair u v) (u++t)
  | .overlap,false => addToken (pair (u++t) (t++v)) v
  | .overlap,true => addToken (pair (u++t) (t++v)) u

private def changed : CrossedShape → Bool → Option Bool
  | .sharedShort,false | .intermediate,true => some true
  | _,_ => none

private def donor : CrossedShape → Bool → Option Bool
  | .intermediate,false | .disjoint,true | .overlap,true => some true
  | _,_ => some false

theorem lift_crossed_shortening [Fintype A] {row : CrossedShape} {side : Bool} {t u v : Word A}
    (done : Completable (crossedShortening row side t u v)) : Completable (crossedWords row t u v) := by
  let w := crossedShortening row side t u v
  let pad (i : Option Bool) := if i=changed row side then [donor row side] else []
  cases side with
  | false =>
    have eqn : (fun k => spell w (pad k) ++ w k) = crossedWords row t u v := by
      funext k
      cases row <;> rcases k with _ | (_ | _) <;>
        simp [w,pad,changed,donor,crossedWords,crossedShortening,addToken,pair,List.append_assoc]
    exact eqn ▸ done.padLeft pad
  | true =>
    have eqn : (fun k => w k ++ spell w (pad k)) = crossedWords row t u v := by
      funext k
      cases row <;> rcases k with _ | (_ | _) <;>
        simp [w,pad,changed,donor,crossedWords,crossedShortening,addToken,pair,List.append_assoc]
    exact eqn ▸ done.padRight pad

/-- A shortest counterexample in a specified table row forces ambiguity of
both named shortenings. The words need not themselves be distinct after a cut. -/
theorem both_crossed_shortenings_ambiguous {f : Fin 3 → Word Bool} (input : ClassificationInput f)
    (obstruction : ¬ Completable f) (row : CrossedShape) (t u v : Word Bool)
    (nt : t≠[]) (nu : u≠[]) (nv : v≠[]) (order : Option Bool ≃ Fin 3)
    (form : (fun k => f (order k))=crossedWords row t u v) (side : Bool) :
    ¬ NamedCode (crossedShortening row side t u v) := by
  let w := crossedShortening row side t u v
  let old := crossedWords row t u v
  have pt := List.length_pos_iff.mpr nt
  have pu := List.length_pos_iff.mpr nu
  have pv := List.length_pos_iff.mpr nv
  have limit (s : Option Bool) : (w s).length ≤ (old s).length := by
    cases row <;> cases side <;> rcases s with _ | (_ | _) <;>
      simp [w,old,crossedWords,crossedShortening,addToken,pair] <;> omega
  have cut : (w (changed row side)).length < (old (changed row side)).length := by
    cases row <;> cases side <;> simp [w,old,crossedWords,crossedShortening,changed,addToken,pair] <;> omega
  have en (s : Option Bool) : f (order s) = old s := congrFun form s
  have shorter : totalWordLength (fun i => w (order.symm i)) < totalWordLength f := by
    apply Finset.sum_lt_sum
    · intro k _
      simpa only [←en,Equiv.apply_symm_apply] using limit (order.symm k)
    · exact ⟨order (changed row side),Finset.mem_univ _,by simpa only [Equiv.symm_apply_apply,←en] using cut⟩
  intro code
  have result := input.shorter _ shorter (code.reindex order.symm.injective)
  have done : Completable w := by simpa only [Equiv.symm_apply_apply] using result.reindex order.injective
  exact obstruction ((completable_reindex_iff f order).mp (form.symm ▸ lift_crossed_shortening done))

end ThreeWordCodes
