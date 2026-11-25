module

public import ThreeWordCodes.BorderFirstLetter
public import ThreeWordCodes.BorderOneMarker

/-! # The second-letter case and elimination of every border -/

@[expose] public section
namespace ThreeWordCodes.Border
open BinaryGaps

private theorem swap_pieces {A : Type*} {u v w : Word A} (bad : ¬NamedCode (pieces u v w)) :
    ¬NamedCode (pieces v u w) := by
  let swap (i : Option Bool) := i.map (!·)
  have form : (fun i => pieces v u w (swap i))=pieces u v w := by funext i; rcases i with _|(_|_) <;> rfl
  exact fun h => bad (form ▸ h.reindex (f:=swap) (by decide))

/-- If both mixed words have at least two markers, the ambiguous lengthening
bounds their common gap by one. Both outside margins of z are one. -/
private theorem second_many (gs es : List ℕ) (n i j : ℕ) (pg : 0<gs.length) (pe : 0<es.length)
    (cop : (es.length+1).Coprime (gs.length+1))
    (model : Model (mixed 0 gs 0) [a] (mixed 1 es 1) n i j)
    (old : ¬NamedCode (layout 0 gs 0 1 es 1)) (longer : ¬NamedCode (extended 0 gs 0 1 es 1)) : False := by
  have ne : gs.length≠es.length := by
    intro e
    rw [e,Nat.coprime_self] at cop
    omega
  obtain ⟨c,below,G,E⟩ := uniform_lengthening_bound_unordered (i:=0) (j:=0) (h:=1) (q:=1)
    (Or.inl rfl) (Or.inl rfl) old longer pg pe ne cop
  obtain ⟨c',g',_,_,_,le,_⟩ := uniform_gaps_of_distinct_counts old pg pe ne cop
  obtain ⟨v,mem⟩ := List.exists_mem_of_ne_nil gs (List.length_pos_iff.mp pg)
  have one : c=1 := by have same := (G v mem).symm.trans (g' v mem); omega
  have gform : gs=List.replicate gs.length 1 := List.eq_replicate_iff.mpr ⟨rfl,fun u hu => (G u hu).trans one⟩
  have eform : es=List.replicate es.length 1 := List.eq_replicate_iff.mpr ⟨rfl,fun u hu => (E u hu).trans one⟩
  let h : Word Bool := [a,b]
  have first (l : List ℕ) (form : l=List.replicate l.length 1) :
      [a]++mixed 0 l 0=wordPow h (l.length+1) :=
    (congrArg (fun g => [a]++mixed 0 g 0) form).trans (uniform_power 1 l.length)
  have zform : mixed 1 es 1=wordPow h (es.length+1)++[a] := by
    have endA : mixed 1 es 1=mixed 1 es 0++[a] := (append_pure es 1 0 1).symm
    rw [endA]; exact congrArg (·++[a]) (first es eform)
  have comm : wordPow (mixed 1 es 1) (0+1)++mixed 0 gs 0=wordPow h ((es.length+1)+(gs.length+1)) := by
    rw [wordPow_one,zform,List.append_assoc,first gs gform,wordPow_add h (es.length+1) (gs.length+1)]
  apply model.forbidden 0
  rw [first gs gform,comm]; exact wordPow_comm ..

theorem no_second_letter (p z : Word Bool) (n i j : ℕ) (model : Model p [a] z n i j) : False := by
  have hz : z.head?=some a := model.first.2.symm
  have tz : z.getLast?=some a := model.last.2.symm
  obtain ⟨gs,pform⟩ := body_form (w:=p) (model.nonempty P) (hz ▸ model.first.1) (tz ▸ model.last.1)
  have bz : b∈z := by
    rcases decompose z with ⟨t,word⟩ | ⟨h,es,k,rfl⟩
    · exfalso
      apply model.noncommuting
      rw [word]; change run 1++run t=run t++run 1
      rw [←run_add,←run_add,Nat.add_comm]
    · exact List.count_pos_iff.mp (by rw [mixed_count]; omega)
  obtain ⟨h,es,k,zform⟩ := mixed_of_contains_marker bz
  have base := swap_pieces (model.cuts .pieces)
  change ¬NamedCode (pieces [a] p z) at base
  have new := model.cuts .rightJoin
  change ¬NamedCode (pieces p (p++[a]) z) at new
  have tail : mixed 0 gs 0++[a]=mixed 0 gs 1 := append_pure gs 0 0 1
  rw [pform,zform] at base
  rw [pform,tail,zform] at new
  change ¬NamedCode (extended 0 gs 0 h es k) at new
  obtain ⟨_,ke,_,he⟩ := normalized_lengthening_margins new (Or.inl rfl) (Or.inl rfl)
  have start : h≠0 := by rintro rfl; simp [zform,mixed,run,a,b] at hz
  have finish : k≠0 := by
    rintro rfl
    have rev : (mixed 0 es.reverse h).head?=some a := by simpa only [zform,←List.head?_reverse,reverse_mixed] using tz
    simp [mixed,run,a,b] at rev
  obtain rfl : h=1 := by omega
  obtain rfl : k=1 := by omega
  have actual : Model (mixed 0 gs 0) [a] (mixed 1 es 1) n i j := by rwa [←pform,←zform]
  cases es with
  | nil => exact one_marker_forbidden actual base new
  | cons u us =>
    have pg : 0<gs.length := by
      apply List.length_pos_iff.mpr
      rintro rfl
      have bound := model.other_length (k:=Q) (l:=P) (by decide) rfl
      change 2≤p.length at bound
      simp [pform,mixed,gapTail,run] at bound
    have cop : ((u::us).length+1).Coprime (gs.length+1) := by
      apply Nat.dvd_one.mp
      apply model.divisors b
      rintro (_|(_|_))
      · simpa only [pieces,addToken,zform,mixed_count] using Nat.gcd_dvd_left ((u::us).length+1) (gs.length+1)
      · simpa only [pieces,addToken,pair,pform,mixed_count] using Nat.gcd_dvd_right ((u::us).length+1) (gs.length+1)
      · simp [pieces,addToken,pair,a,b]
    exact second_many gs (u::us) n i j pg (by simp) cop actual base new

theorem no_model (p q z : Word Bool) (n i j : ℕ) : ¬Model p q z n i j := by
  intro model
  obtain ⟨t,letter⟩ := model.letter
  rcases t with _|(_|_)
  · change z=[a] at letter
    exact no_third_letter p q n i j (letter ▸ model)
  · change p=[a] at letter
    exact no_first_letter q z n i j (letter ▸ model)
  · change q=[a] at letter
    exact no_second_letter p z n i j (letter ▸ model)

/-- Section 4. A minimal binary counterexample cannot have one word as both
a proper prefix and a proper suffix of another. -/
theorem border_completion (f : Fin 3 → Word Bool) (input : ClassificationInput f)
    (border : HasBorder f) : Completable f := border_of_no_model no_model f input border

end ThreeWordCodes.Border

namespace ThreeWordCodes

/-- After Section 4, only the four crossed rows are required for the main theorem. -/
theorem four_crossed_rows_suffice.{u}
    (rows : ∀ v, ClassificationInput v → InCrossedTable v → Completable v) : ThreeWordTheorem.{u} :=
  border_and_four_rows_suffice Border.border_completion rows

end ThreeWordCodes
