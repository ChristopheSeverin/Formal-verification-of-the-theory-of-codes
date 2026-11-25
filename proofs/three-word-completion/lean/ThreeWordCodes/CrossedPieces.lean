module

public import ThreeWordCodes.CrossedShortenings

/-! # Completing every crossed row from its three pieces

Each row is obtained by two rounds of left or right padding on named words.
This also deals directly with the outer codes in the first three rows.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A : Type*}

/-- The three pieces, ordered to match the names retained during padding. -/
def crossedPieces (row : CrossedShape) (t u v : Word A) : Option Bool → Word A :=
  match row with
  | .sharedShort => addToken (pair t u) v
  | .intermediate => addToken (pair t v) u
  | .disjoint => addToken (pair u v) t
  | .overlap => addToken (pair u t) v

private def padOne (target withName : Option Bool) (i : Option Bool) : Word (Option Bool) :=
  if i=target then [withName] else []

/-- The outer construction in all four rows needs only the two padding rules. -/
theorem crossed_of_completable_pieces [Fintype A] {row : CrossedShape} {t u v : Word A}
    (done : Completable (crossedPieces row t u v)) : Completable (crossedWords row t u v) := by
  let U : Option Bool := some false
  let V : Option Bool := some true
  cases row with
  | sharedShort =>
    have out := (done.padLeft (padOne V U)).padRight (padOne none U)
    convert out using 1
    funext i
    rcases i with _ | (_ | _) <;> simp [padOne,crossedPieces,crossedWords,addToken,pair,U,V]
  | intermediate =>
    have out := (done.padRight (padOne V U)).padLeft (padOne none V)
    convert out using 1
    funext i
    rcases i with _ | (_ | _) <;> simp [padOne,crossedPieces,crossedWords,addToken,pair,U,V]
  | disjoint =>
    have out := (done.padLeft (padOne none U)).padRight (padOne none V)
    convert out using 1
    funext i
    rcases i with _ | (_ | _) <;> simp [padOne,crossedPieces,crossedWords,addToken,pair,U,V]
  | overlap =>
    let extend (i : Option Bool) : Word (Option Bool) :=
      match i with
      | some false => [V]
      | some true => [none]
      | none => []
    have out := (done.padRight extend).padLeft (padOne none U)
    convert out using 1
    funext i
    rcases i with _ | (_ | _) <;> simp [padOne,crossedPieces,crossedWords,extend,addToken,pair,U,V]

/-- Thus a shortest obstruction forces ambiguity already on t, u, v themselves,
independently of Proposition 6. -/
theorem crossed_pieces_ambiguous {f : Fin 3 → Word Bool} (input : ClassificationInput f)
    (obstruction : ¬ Completable f) (row : CrossedShape) (t u v : Word Bool)
    (nt : t≠[]) (nu : u≠[]) (nv : v≠[]) (order : Option Bool ≃ Fin 3)
    (form : (fun k => f (order k))=crossedWords row t u v) :
    ¬ NamedCode (crossedPieces row t u v) := by
  let w := crossedPieces row t u v
  let old := crossedWords row t u v
  have pt := List.length_pos_iff.mpr nt
  have pu := List.length_pos_iff.mpr nu
  have pv := List.length_pos_iff.mpr nv
  have le (i : Option Bool) : (w i).length ≤ (old i).length := by
    cases row <;> rcases i with _ | (_ | _) <;>
      simp [w,old,crossedPieces,crossedWords,pair,addToken] <;> omega
  have cut : ∃ i : Option Bool, (w i).length < (old i).length := by
    cases row with
    | sharedShort | intermediate =>
      exact ⟨some true,by simp [old,w,crossedWords,crossedPieces,pair,addToken]; omega⟩
    | disjoint | overlap =>
      exact ⟨none,by simp [old,w,crossedWords,crossedPieces,addToken]; omega⟩
  have en (i : Option Bool) : f (order i)=old i := congrFun form i
  have shorter : totalWordLength (fun i => w (order.symm i)) < totalWordLength f := by
    apply Finset.sum_lt_sum
    · intro i _
      simpa only [←en,Equiv.apply_symm_apply] using le (order.symm i)
    · obtain ⟨j,strict⟩ := cut
      exact ⟨order j,Finset.mem_univ _,by simpa only [Equiv.symm_apply_apply,←en] using strict⟩
  intro code
  have completed := input.shorter _ shorter (code.reindex order.symm.injective)
  have done : Completable w := by simpa only [Equiv.symm_apply_apply] using completed.reindex order.injective
  exact obstruction ((completable_reindex_iff f order).mp (form.symm ▸ crossed_of_completable_pieces done))

end ThreeWordCodes
