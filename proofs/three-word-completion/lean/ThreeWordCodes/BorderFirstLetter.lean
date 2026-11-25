module

public import ThreeWordCodes.BorderUniform
public import ThreeWordCodes.UniformCoordinates

/-! # The first piece cannot be the letter in the border model -/

@[expose] public section
namespace ThreeWordCodes.Border
open BinaryGaps

def marks (n : ℕ) : Word Bool := List.replicate (n+1) b

/-- The change sends a to D⁻¹ and H to D J^(m+1) D^(r+1) for gap r+2. -/
theorem body_image (m r : ℕ) :
    GroupCoordinates.change 1 (r+1 : ℕ) (groupWord (body m (r+2))) =
      groupWord ([a]++marks m++run (r+1)) := by
  have e := uniform_coordinate_change 1 (r+1) 0 m (r+2) 0 (by omega) (by omega) (by omega)
  have word : [a]++marks m++run (r+1)=mixed 1 (List.replicate m 0) (r+1) := by
    simpa only [body_zero,marks,show run 1=[a] from rfl] using body_bracket m 0 1 (r+1)
  rw [word]
  simpa only [body,Nat.cast_one,Nat.sub_zero,show 1+(r+1)-(r+2)=0 from by omega] using e

/-- Even when a gap at a token boundary has length two, the marked block
D J^(t+1) D is distinguishable from a product of D and J^(m+1). Lemma 2
would otherwise bound its outside margins by its internal gap, which is zero. -/
theorem marked_body_basis (m t : ℕ) (pm : 0<m) (pt : 0<t) (ne : m≠t) (cop : (t+1).Coprime (m+1)) :
    NamedCode (pieces [a] (marks m) ([a]++marks t++[a])) := by
  by_contra amb
  have eqQ : marks m=mixed 0 (List.replicate m 0) 0 := (body_zero m).symm
  have eqZ : [a]++marks t++[a]=mixed 1 (List.replicate t 0) 1 := by
    simpa only [body_zero,marks,show run 1=[a] from rfl] using body_bracket t 0 1 1
  rw [eqQ,eqZ] at amb
  have bounds := uniform_bounds (s:=0) (v:=0) (h:=1) (k:=1) (g:=0) pm pt ne cop amb
  omega

/-- Every positive n and gap at least two yields an injective middle cut.
The three readings on the marked basis have three distinct initial names. -/
theorem first_large_gap (m t r n : ℕ) (pm : 0<m) (pt : 0<t) (ne : m≠t) (cop : (t+1).Coprime (m+1)) :
    NamedCode (cutWords .middle [a] (body m (r+2)) (body t (r+2)) (n+1)) := by
  let g := pieces [a] (marks m) ([a]++marks t++[a])
  let tail := List.replicate r P
  let core := Q::tail
  let ce := P::core
  let xe := core++wordPow ce n
  let ze := Z::tail
  let outer := pieces xe ce ze
  let F := GroupCoordinates.change 1 (r+1 : ℕ)
  have gp : F (groupWord [a]) = (groupWord [a])⁻¹ := GroupCoordinates.change_a ..
  have dc : spell g ce=[a]++spell g core := rfl
  have cs : spell g core=marks m++run r := by simp [g,core,tail,P,Q,pieces,addToken,pair,spell_replicate,singleton_power,run]
  have ext : spell g ce++[a]=[a]++marks m++run (r+1) := by
    rw [dc,cs,run_add r 1]; simp [List.append_assoc,run]
  have zi : spell g ze=[a]++marks t++run (r+1) := by
    simp [g,ze,tail,Z,P,pieces,addToken,pair,spell_replicate,singleton_power,run,List.replicate_succ,List.append_assoc]
  have imageC : F (groupWord (body m (r+2)++[a]))=groupWord (spell g ce) := by
    rw [groupWord_append,map_mul,gp,show F (groupWord (body m (r+2)))=_ from body_image m r,←ext,groupWord_append]
    group
  have imageZ : F (groupWord (body t (r+2)))=groupWord (spell g ze) := by rw [zi]; exact body_image t r
  have imageX : F (groupWord (short [a] (body m (r+2)) (n+1))) = groupWord (spell g xe) := by
    change F (groupWord ([a]++wordPow (body m (r+2)++[a]) (n+1)))=groupWord (spell g (core++wordPow ce n))
    rw [groupWord_append,map_mul,gp,Palindromic.group_word_pow,map_pow,imageC,pow_succ',
      spell_append,spell_wordPow,groupWord_append,Palindromic.group_word_pow]
    conv_lhs => arg 2; arg 1; rw [dc,groupWord_append]
    group
  have kern : SameEquations (cutWords .middle [a] (body m (r+2)) (body t (r+2)) (n+1))
      (fun k => spell g (outer k)) := by
    apply sameEquations_of_group_change F (GroupCoordinates.change_involutive 1 (r+1 : ℕ)).injective
    rintro (_|(_|_))
    · exact imageZ
    · exact imageX
    · exact imageC
  have nonempty : ∀ k,outer k≠[] := by rintro (_|(_|_)) <;> simp [outer,xe,ce,ze,core,pieces,addToken,pair]
  have head : Function.Injective (fun k => (outer k).head?) := by
    rintro (_|(_|_)) (_|(_|_)) h <;> simp_all [outer,xe,ce,ze,core,pieces,addToken,pair,P,Q,Z]
  obtain ⟨inj,pf⟩ := marked_facts outer nonempty head
  exact kern.namedCode_iff.mpr ((marked_body_basis m t pm pt ne cop).substitution (completable_prefix inj nonempty pf).1)

/-- All exponents of the first-letter case in Section 4. -/
theorem no_first_letter (q z : Word Bool) (n i j : ℕ) (model : Model [a] q z n i j) : False := by
  cases n with
  | zero => exact first_letter_zero model
  | succ n =>
    obtain ⟨⟨m,t,g,pm,pt,ne,cop,pos,eqQ,eqZ⟩⟩ := first_letter_data model
    by_cases one : g=1
    · apply model.forbidden 0
      have qBlock : q++[a]=wordPow [b,a] (m+1) := by
        rw [eqQ,one]; exact body_trailing m 1
      have zBlock : wordPow z (0+1)++[a]=wordPow [b,a] (t+1) := by
        rw [wordPow_one,eqZ,one]; exact body_trailing t 1
      rw [qBlock,zBlock]; exact wordPow_comm ..
    · have gap : 2≤g := by have := pos; omega
      obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le gap
      have bound : g=r+2 := by omega
      apply model.cuts .middle
      rw [eqQ,eqZ,bound]
      exact first_large_gap m t r n pm pt ne cop

end ThreeWordCodes.Border
