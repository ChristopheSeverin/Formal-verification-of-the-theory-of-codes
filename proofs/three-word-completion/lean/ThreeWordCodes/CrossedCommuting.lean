module

public import ThreeWordCodes.CrossedPieces
public import ThreeWordCodes.PureCorollaries

/-! # The commuting-piece cases of the four crossed forms -/

@[expose] public section
namespace ThreeWordCodes
open BinaryGaps
variable {A : Type*}

theorem spell_crossed {I : Type*} (g : I → Word A) (row : CrossedShape) (t u v : Word I) :
    (fun i => spell g (crossedWords row t u v i)) = crossedWords row (spell g t) (spell g u) (spell g v) := by
  funext i
  cases row <;> rcases i with _ | (_ | _) <;> simp [crossedWords,addToken,pair]

private theorem indexed_prefix [Fintype A] {I : Type*} [Fintype I] (v : I → Word A)
    (nz : ∀ i,v i≠[]) (sep : ∀ i j, v i <+: v j → i=j) : Completable v := by
  apply completable_prefix
  · intro x y eqn
    exact sep x y (by rw [eqn])
  · exact nz
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ pr
    rw [sep i j pr]

private theorem shorter_power_first (i j : ℕ) (pos : 0 < i) (smaller : i < j) :
    Completable (crossedWords .overlap [b] (run i) (run j)) := by
  let v := addToken (pair (run i++[b]) [b]) (run j)
  have limit : (0:ℕ)<j := by omega
  have sep : ∀ s t, v s <+: v t → s=t := by
    rintro (_ | (_ | _)) (_ | (_ | _)) cp <;> try rfl
    · exact (Nat.not_le_of_gt smaller (pure_prefix_bound cp)).elim
    · exact (Nat.not_le_of_gt limit (pure_prefix_bound (s:=0) cp)).elim
    · exact (marked_not_prefix_pure j i [] cp).elim
    · exact (Nat.ne_of_gt pos (marked_prefix (h:=0) cp).1).elim
    · exact (marked_not_prefix_pure j 0 [] cp).elim
    · exact (Nat.ne_of_lt pos (marked_prefix (i:=0) cp).1).elim
  have base := indexed_prefix v (by rintro (_ | (_ | _)) <;> simp [v,addToken,pair,run,Nat.ne_of_gt limit]) sep
  let d : Option Bool → Word (Option Bool) := addToken (pair [some false] [some true,none]) [some false,none]
  let rd (x) := (d x).reverse
  have outer : Completable d := by
    have back := (indexed_prefix rd (by decide) (by decide)).reverse
    simpa [rd] using back
  have word : (fun x => spell v (d x))=crossedWords .overlap [b] (run i) (run j) := by
    funext x
    rcases x with _ | (_ | _) <;> simp [v,d,addToken,pair,crossedWords,List.append_assoc]
  exact word ▸ base.substitute outer

private theorem overlap_powers (i j : ℕ) (pi : 0 < i) (pj : 0 < j)
    (code : NamedCode (crossedWords .overlap [b] (run i) (run j))) :
    Completable (crossedWords .overlap [b] (run i) (run j)) := by
  rcases lt_trichotomy i j with lt | rfl | gt
  · exact shorter_power_first i j pi lt
  · have eqn : spell (crossedWords .overlap [b] (run i) (run i)) [some false,none] =
        spell (crossedWords .overlap [b] (run i) (run i)) [none,some true] := by
      simp [crossedWords,addToken,pair,List.append_assoc]
    exact ((by decide : ([some false,none] : Word (Option Bool)) ≠ [none,some true]) (code eqn)).elim
  · let swap (i : Option Bool) := i.map (!·)
    have done := (shorter_power_first j i pj gt).reverse.reindex (f:=swap) (by decide)
    have form : (fun k => (crossedWords .overlap [b] (run j) (run i) (swap k)).reverse)=
        crossedWords .overlap [b] (run i) (run j) := by
      funext k
      rcases k with _ | (_ | _) <;> simp [crossedWords,addToken,pair,swap,run,List.append_assoc]
    exact form ▸ done

private theorem complete_pure_outer [Fintype A] (g : Bool → Word A) (row : CrossedShape)
    (T U V : Word Bool) (pieces : Option Bool → Word A)
    (read : crossedWords row (spell g T) (spell g U) (spell g V)=pieces) (code : NamedCode pieces)
    (simple : (∃ i z n,crossedWords row T U V i=List.replicate n z) ∨
      ∃ i j, 0 < i ∧ 0 < j ∧ crossedWords row T U V=crossedWords .overlap [b] (run i) (run j)) :
    Completable pieces := by
  let d := crossedWords row T U V
  have eqn := (spell_crossed g row T U V).trans read
  have actual : NamedCode (fun i => spell g (d i)) := eqn.symm ▸ code
  have base := pair_basis_of_coded_reading g d actual
  have named := (base.1.preserves_equations d).namedCode_iff.mpr actual
  rcases simple with pure | ⟨i,j,pi,pj,form⟩
  · exact eqn ▸ base.substitute (named_pure_power_completion threeOrder named pure)
  · change d = crossedWords .overlap [b] (run i) (run j) at form
    have inner : Completable d := form.symm ▸ overlap_powers i j pi pj (form ▸ named)
    exact eqn ▸ base.substitute inner

/-- In all four rows a commuting pair among t,u,v settles the prescribed
triple. This theorem constructs completions on the actual word alphabet. -/
theorem crossed_commuting_completion [Fintype A] (row : CrossedShape) (t u v : Word A)
    (nu : u≠[]) (nv : v≠[]) (code : NamedCode (crossedWords row t u v))
    (commuting : t++u=u++t ∨ t++v=v++t ∨ u++v=v++u) : Completable (crossedWords row t u v) := by
  rcases commuting with tu | tv | uv
  · obtain ⟨r,i,j,et,eu⟩ := (commuting_iff_common_power _ _).mp tu
    apply complete_pure_outer (pair r v) row (run i) (run j) [b] _ _ code
    · left
      cases row with
      | sharedShort | intermediate => exact ⟨some false,a,i,rfl⟩
      | disjoint => exact ⟨some false,a,j,rfl⟩
      | overlap => exact ⟨some false,a,j+i,(List.replicate_add j i a).symm⟩
    · simp [run,spell_replicate,pair,a,b,et,eu]
  · obtain ⟨r,i,j,et,ev⟩ := (commuting_iff_common_power _ _).mp tv
    apply complete_pure_outer (pair r u) row (run i) [b] (run j) _ _ code
    · left
      cases row with
      | sharedShort | intermediate => exact ⟨some false,a,i,rfl⟩
      | disjoint => exact ⟨some true,a,j,rfl⟩
      | overlap => exact ⟨some true,a,i+j,(List.replicate_add i j a).symm⟩
    · simp [run,spell_replicate,pair,a,b,et,ev]
  · obtain ⟨r,i,j,eu,ev⟩ := (commuting_iff_common_power _ _).mp uv
    apply complete_pure_outer (pair r t) row [b] (run i) (run j) _ _ code
    · cases row with
      | sharedShort | intermediate => exact Or.inl ⟨some false,b,1,rfl⟩
      | disjoint => exact Or.inl ⟨some false,a,i,rfl⟩
      | overlap =>
        refine Or.inr ⟨i,j,Nat.pos_of_ne_zero ?_,Nat.pos_of_ne_zero ?_,rfl⟩
        · rintro rfl; exact nu (by simpa using eu)
        · rintro rfl; exact nv (by simpa using ev)
    · simp [run,spell_replicate,pair,a,b,eu,ev]

/-- The remaining crossed cases have an ambiguous, pairwise noncommuting
triple of pieces, and both single shortenings are ambiguous. -/
theorem crossed_obstruction_conditions {f : Fin 3 → Word Bool} (input : ClassificationInput f)
    (obstruction : ¬ Completable f) (row : CrossedShape) (t u v : Word Bool)
    (nt : t≠[]) (nu : u≠[]) (nv : v≠[]) (order : Option Bool ≃ Fin 3)
    (form : (fun i => f (order i))=crossedWords row t u v) :
    ¬NamedCode (crossedPieces row t u v) ∧ t++u≠u++t ∧ t++v≠v++t ∧ u++v≠v++u ∧
    ∀ side, ¬NamedCode (crossedShortening row side t u v) := by
  have words : NamedCode (crossedWords row t u v) := form ▸ input.code.reindex order.injective
  have no (comm : t++u=u++t ∨ t++v=v++t ∨ u++v=v++u) : False := by
    have done := crossed_commuting_completion row t u v nu nv words comm
    exact obstruction ((completable_reindex_iff f order).mp (form.symm ▸ done))
  exact ⟨crossed_pieces_ambiguous input obstruction row t u v nt nu nv order form,fun e => no (Or.inl e),
    fun e => no (Or.inr (Or.inl e)),fun e => no (Or.inr (Or.inr e)),
    both_crossed_shortenings_ambiguous input obstruction row t u v nt nu nv order form⟩

end ThreeWordCodes
