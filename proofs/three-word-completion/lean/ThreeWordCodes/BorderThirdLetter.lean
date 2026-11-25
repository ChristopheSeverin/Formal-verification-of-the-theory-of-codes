module

public import ThreeWordCodes.BorderModel

/-! # The third piece cannot be the letter in the border model -/

@[expose] public section
namespace ThreeWordCodes.Border
open BinaryGaps

theorem Model.other_length {p q z : Word Bool} {n i j : ℕ} (m : Model p q z n i j)
    {k l : Option Bool} (ne : k≠l) (one : (pieces p q z k).length=1) :
    2≤(pieces p q z l).length := by
  obtain ⟨s,_,unique⟩ := m.unique_letter
  have pos := List.length_pos_iff.mpr (m.nonempty l)
  have diff : (pieces p q z l).length≠1 := fun h => ne ((unique k one).trans (unique l h).symm)
  omega

theorem cycle_ambiguity {A : Type*} {u v w : Word A} (bad : ¬NamedCode (pieces u v w)) :
    ¬NamedCode (pieces w u v) := by
  let cycle : Option Bool → Option Bool
    | none => some false
    | some false => some true
    | some true => none
  have form : (fun k => pieces w u v (cycle k))=pieces u v w := by
    funext k; rcases k with _|(_|_) <;> rfl
  exact fun h => bad (form ▸ h.reindex (f:=cycle) (by decide))

theorem head_b {w : Word Bool} (ne : w≠[]) (other : w.head?≠some a) : w.head?=some b := by
  cases w with
  | nil => contradiction
  | cons c w => cases c <;> first | rfl | exact (other rfl).elim

/-- Uniform internal gaps with one leading full gap and empty right margin
make an exact power of the block a^g b. -/
theorem uniform_power (g t : ℕ) :
    mixed g (List.replicate t g) 0=wordPow (run g++[b]) (t+1) := by
  induction t with
  | zero => simp [mixed,gapTail,run]
  | succ t ih =>
    calc _ = (run g++[b])++mixed g (List.replicate t g) 0 := by
                simp [mixed,gapTail,List.replicate_succ,List.append_assoc]
         _ = _ := by rw [ih,wordPow_succ' _ (t+1)]

theorem singleton_power (c : Bool) (n : ℕ) : wordPow [c] n=List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ',ih]; rfl

/-- Both joins of the shorter mixed word have the gap fixed by an internal
gap of that word. Hence qp and z^g p are powers of the same a^g b. -/
theorem no_third_letter (p q : Word Bool) (n i j : ℕ) (m : Model p q [a] n i j) : False := by
  have nzP := m.nonempty P
  change p≠[] at nzP
  have hp : p.head?=some b := head_b nzP m.first.1
  have tp : p.getLast?=some b := by
    have endNe : p.reverse.head?≠some a := by simpa using m.last.1
    simpa only [List.head?_reverse] using head_b (w:=p.reverse) (by simpa using nzP) endNe
  have bp : b∈p := List.mem_of_mem_head? hp
  have bq : b∈q := by
    rcases decompose q with ⟨t,h⟩ | ⟨h,es,t,rfl⟩
    · exfalso
      apply m.noncommuting
      rw [h]
      change run t++run 1=run 1++run t
      rw [←run_add,←run_add,Nat.add_comm]
    · exact List.count_pos_iff.mp (by rw [mixed_count]; omega)
  obtain ⟨d,gs,r,ep⟩ := mixed_of_contains_marker bp
  obtain ⟨h,es,t,eqn⟩ := mixed_of_contains_marker bq
  obtain rfl : d=0 := head_zero (ep ▸ hp)
  obtain rfl : r=0 := last_zero (ep ▸ tp)
  have many : gs≠[] := by
    rintro rfl
    have pk : p.length=1 := by simp [ep,mixed,gapTail,run]
    have bound := m.other_length (k:=Z) (l:=P) (by decide) rfl
    change 2≤p.length at bound
    omega
  have hpos : 0<h := by
    by_contra! zero
    have he : h=0 := by omega
    have first := m.first.2
    simp [eqn,he,mixed,run,b,a] at first
  let L := es++t::gs
  let R := gs++h::es
  have dl : q++p=mixed h L 0 := by rw [eqn,ep,join_mixed,Nat.add_zero]
  have dr : p++q=mixed 0 R t := by rw [eqn,ep,join_mixed,Nat.zero_add]
  have lAmb := cycle_ambiguity (m.cuts .leftJoin)
  have rAmb := cycle_ambiguity (m.cuts .rightJoin)
  change ¬NamedCode (pieces [a] p (q++p)) at lAmb
  change ¬NamedCode (pieces [a] p (p++q)) at rAmb
  rw [dl,ep] at lAmb
  rw [dr,ep] at rAmb
  have gcd : (es.length+1).Coprime (gs.length+1) := by
    apply Nat.dvd_one.mp
    apply m.divisors b
    rintro (_|(_|_))
    · simp [pieces,addToken,a,b]
    · simpa only [pieces,addToken,pair,ep,mixed_count] using Nat.gcd_dvd_right (es.length+1) (gs.length+1)
    · simpa only [pieces,addToken,pair,eqn,mixed_count] using Nat.gcd_dvd_left (es.length+1) (gs.length+1)
  have dlSize : L.length+1=(es.length+1)+(gs.length+1) := by simp [L]; omega
  have drSize : R.length+1=(es.length+1)+(gs.length+1) := by simp [R]; omega
  have num : (es.length+1+(gs.length+1)).Coprime (gs.length+1) := Nat.coprime_add_self_left.mpr gcd
  have manyN := List.length_pos_iff.mpr many
  obtain ⟨c,pg,leftG,_⟩ := uniform_gaps_of_ambiguity (i:=0) (g:=gs) (j:=0) (h:=h) (e:=L) (q:=0)
    lAmb (by omega) (by omega) (dlSize ▸ num)
  obtain ⟨c',pg',rightG,_⟩ := uniform_gaps_of_ambiguity (i:=0) (g:=gs) (j:=0) (h:=0) (e:=R) (q:=t)
    rAmb (by omega) (by omega) (drSize ▸ num)
  obtain ⟨v,mem⟩ := List.exists_mem_of_ne_nil gs many
  have same : c'=c := (pg' v mem).symm.trans (pg v mem)
  subst c'
  have joinEq : h=c := rightG h (by simp [R])
  subst h
  have cpos : 0<c := hpos
  have eg : gs=List.replicate gs.length c := List.eq_replicate_iff.mpr ⟨rfl,pg⟩
  have el : L=List.replicate L.length c := List.eq_replicate_iff.mpr ⟨rfl,leftG⟩
  have qc : q++p=wordPow (run c++[b]) (L.length+1) :=
    dl.trans ((congrArg (fun l => mixed c l 0) el).trans (uniform_power c L.length))
  have pc : wordPow [a] c++p=wordPow (run c++[b]) (gs.length+1) := by
    calc wordPow [a] c++p = mixed c gs 0 := by rw [singleton_power,ep]; rfl
         _ = _ := (congrArg (fun l => mixed c l 0) eg).trans (uniform_power c gs.length)
  obtain ⟨e,ce⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cpos)
  apply m.forbidden e
  rw [show e+1=c from ce.symm,qc,pc]; exact wordPow_comm ..

end ThreeWordCodes.Border
