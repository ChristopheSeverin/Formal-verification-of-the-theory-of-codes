module

public import ThreeWordCodes.CrossedDisjointTheorem

/-! # Joined words with a lateral letter in rows I and II -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

theorem body_ab (n : ℕ) : Border.body n 1=[b]++wordPow [a,b] n := by
  have e := Border.uniform_power 1 n
  change [a]++Border.body n 1=wordPow [a,b] (n+1) at e
  rw [wordPow_succ' [a,b] n] at e
  exact List.cons.inj e |>.2

theorem head_body_ab (n : ℕ) : Border.body n 1=wordPow [b,a] n++[b] := by
  rw [body_ab]
  exact (rotate_power [b] [a] n).symm

/-- A letter appended and a letter prepended are the two columns needed
for the signed coordinate cases. -/
theorem gap_two_image (i n j : ℕ) (ini : i≤1) (fin : j≤1) :
    GroupCoordinates.change 1 1 (groupWord (mixed i (List.replicate n 2) j)) =
      groupWord (run (1-i)++Border.marks n++run (1-j)) := by
  have e := uniform_coordinate_change 1 1 i n 2 j ini fin (by decide)
  have word := Border.body_bracket n 0 (1-i) (1-j)
  rw [Border.body_zero] at word
  simpa only [Border.marks,word,Nat.cast_one,show 1+1-2=0 from rfl] using e

theorem residue_with_prefix (w : Word Bool) (m n : ℕ) (pm : 0<m) (cop : (n+1).Coprime (m+1)) :
    NamedCode (pieces (w++[a]) (Border.marks m) ([a]++Border.marks n)) := by
  let pre := pair (w.map (letterFlip true)) []
  let tail (i : Bool) := if i then n+1 else 0
  have nonzero : (n+1)%(m+1)≠0 := by
    intro h
    have d := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl (m+1))
    change (n+1).gcd (m+1)=1 at cop
    rw [cop] at d
    have := Nat.dvd_one.mp d
    omega
  have unique : Function.Injective (fun i => tail i%(m+1)) := by
    rintro (_|_) (_|_) h <;> simp_all [tail]
  let perm : Option Bool → Option Bool
    | none => some true
    | some false => some false
    | some true => none
  let g := pieces (w++[a]) (Border.marks m) ([a]++Border.marks n)
  have shape : (fun k => (g k).map (letterFlip true))=fun k => residueWords (m+1) pre tail (perm k) := by
    funext k
    rcases k with _|(_|_) <;> simp [g,perm,pre,tail,pieces,addToken,pair,residueWords,Border.marks,run,a,b,letterFlip]
  apply (named_flip_iff g true).mp
  rw [shape]
  exact (residue_completion (m+1) (by omega) pre tail unique).1.reindex (by decide : Function.Injective perm)

theorem residue_triple (m n : ℕ) (pm : 0<m) (cop : (n+1).Coprime (m+1)) :
    NamedCode (pieces (Border.marks m++[a]) (Border.marks m) ([a]++Border.marks n)) :=
  residue_with_prefix (Border.marks m) m n pm cop

theorem pa_test_two (m n : ℕ) (pm : 0<m) (cop : (n+1).Coprime (m+1)) :
    NamedCode (extended 1 (List.replicate m 2) 0 0 (List.replicate n 2) 1) := by
  let dest := pieces (Border.marks m++[a]) (Border.marks m) ([a]++Border.marks n)
  have same : SameEquations (extended 1 (List.replicate m 2) 0 0 (List.replicate n 2) 1) dest := by
    apply sameEquations_of_group_change (GroupCoordinates.change 1 1) (GroupCoordinates.change_involutive 1 1).injective
    rintro (_|(_|_))
    · simpa [extended,dest,pieces,addToken,pair,run] using gap_two_image 0 n 1 (by decide) (by decide)
    · simpa [extended,dest,pieces,addToken,pair,run] using gap_two_image 1 m 0 (by decide) (by decide)
    · simpa [extended,dest,pieces,addToken,pair,run] using gap_two_image 1 m 1 (by decide) (by decide)
  exact same.namedCode_iff.mpr (residue_triple m n pm cop)

/-- The common gap in the ambiguous list a, P, QP is forced by the join
between Q and P. Internal gaps of both pieces are equal to this value. -/
theorem joined_uniform {i h q : ℕ} {G E : List ℕ} (many : 0<G.length)
    (cop : (E.length+1).Coprime (G.length+1))
    (bad : ¬NamedCode (pieces [a] (mixed i G 0) (mixed h E q++mixed i G 0))) :
    G=List.replicate G.length (q+i) ∧ E=List.replicate E.length (q+i) ∧ i≤q+i ∧ h≤q+i := by
  rw [join_mixed] at bad
  let L := E++(q+i)::G
  have len : L.length+1=(E.length+1)+(G.length+1) := by simp [L]; omega
  have cpn : (L.length+1).Coprime (G.length+1) := len.symm ▸ Nat.coprime_add_self_left.mpr cop
  obtain ⟨c,pg,all,bi,_,bh,_⟩ := uniform_gaps_of_ambiguity
    (i:=i) (g:=G) (j:=0) (h:=h) (e:=L) (q:=0) bad (by omega) (by omega) cpn
  have join := all (q+i) (by simp [L])
  exact ⟨List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (pg x hx).trans join.symm⟩,
    List.eq_replicate_iff.mpr ⟨rfl,fun x hx => (all x (List.mem_append_left _ hx)).trans join.symm⟩,
    by omega,by omega⟩

/-- Normalize two marked pieces with opposite initials when the first ends in b. -/
theorem lateral_pair {p q : Word Bool} (pm : b∈p) (qm : b∈q) (cop : (q.count b).Coprime (p.count b))
    (diff : p.head?≠q.head?) (last : p.getLast?≠some a) :
    ∃ i G h E s,p=mixed i G 0 ∧ q=mixed h E s ∧ ((i=0 ∧ 0<h) ∨ (0 < i ∧ h=0)) ∧
      (E.length+1).Coprime (G.length+1) := by
  obtain ⟨i,G,j,pf⟩ := mixed_of_contains_marker pm
  obtain ⟨h,E,s,qf⟩ := mixed_of_contains_marker qm
  have np : p≠[] := by rintro rfl; exact List.not_mem_nil pm
  have endB : p.getLast?=some b := by
    have nb : p.reverse.head?≠some a := by simpa using last
    simpa using Border.head_b (w:=p.reverse) (by simpa using np) nb
  obtain rfl : j=0 := last_zero (pf ▸ endB)
  rw [pf,qf] at diff
  have ends : (i=0 ∧ 0<h) ∨ (0 < i ∧ h=0) := by
    have one := initial_zero diff
    have both : ¬(i=0 ∧ h=0) := by rintro ⟨rfl,rfl⟩; exact diff rfl
    omega
  exact ⟨i,G,h,E,s,pf,qf,ends,by simpa [pf,qf,mixed_count] using cop⟩

theorem lateral_shapes {r p q : Word Bool} {row : CrossedShape} (m : Model row p r q) (r_a : r=[a])
    (diff : p.head?≠q.head?) (last : p.getLast?≠some a) :
    ∃ i G h E s,p=mixed i G 0 ∧ q=mixed h E s ∧ ((i=0 ∧ 0<h) ∨ (0 < i ∧ h=0)) ∧
      (E.length+1).Coprime (G.length+1) :=
  lateral_pair (m.has_marker (k:=Q) (l:=P) (by decide) r_a)
    (m.has_marker (k:=Q) (l:=Z) (by decide) r_a)
    (m.marker_coprime (k:=Q) (l:=Z) (s:=P) (by decide) (by decide) (by decide) r_a) diff last

end ThreeWordCodes.CrossedCase
