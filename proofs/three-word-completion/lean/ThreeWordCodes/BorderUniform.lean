module

public import ThreeWordCodes.BorderThirdLetter

/-! # Uniform marker blocks in the border model -/

@[expose] public section
namespace ThreeWordCodes.Border
open BinaryGaps

/-- The first parameter is the number of internal gaps. -/
def body (m g : ℕ) := mixed 0 (List.replicate m g) 0

theorem body_bracket (m g i j : ℕ) : run i++body m g++run j=mixed i (List.replicate m g) j := by
  rw [List.append_assoc,body,append_pure,Nat.zero_add]
  simp [mixed,run]

theorem body_reverse (m g : ℕ) : (body m g).reverse=body m g := by simp [body,reverse_mixed]

theorem body_trailing (m g : ℕ) : body m g++run g=wordPow ([b]++run g) (m+1) := by
  have front : run g++body m g=wordPow (run g++[b]) (m+1) := by
    simpa only [show run 0=[] from rfl,List.append_nil] using (body_bracket m g g 0).trans (uniform_power g m)
  simpa only [List.reverse_append,List.reverse_singleton,reverse_pow,body_reverse,run,List.reverse_replicate] using
    congrArg List.reverse front

theorem body_zero (m : ℕ) : body m 0=List.replicate (m+1) b := by
  simpa [run,singleton_power] using body_trailing m 0

theorem body_form {w : Word Bool} (nw : w≠[]) (initial : w.head?≠some a) (final : w.getLast?≠some a) :
    ∃ g,w=mixed 0 g 0 := by
  have head := head_b nw initial
  have last : w.getLast?=some b := by
    have rev := head_b (w:=w.reverse) (by simpa using nw) (by simpa using final)
    simpa using rev
  obtain ⟨i,gs,j,word⟩ := mixed_of_contains_marker (List.mem_of_mem_head? head)
  obtain rfl : i=0 := head_zero (word ▸ head)
  obtain rfl : j=0 := last_zero (word ▸ last)
  exact ⟨gs,word⟩

structure FirstLetterData (q z : Word Bool) where
  m : ℕ
  t : ℕ
  g : ℕ
  m_pos : 0<m
  t_pos : 0<t
  counts_ne : m≠t
  coprime : (t+1).Coprime (m+1)
  gap_pos : 0<g
  second : q=body m g
  third : z=body t g

theorem first_letter_data {q z : Word Bool} {n i j : ℕ} (model : Model [a] q z n i j) :
    Nonempty (FirstLetterData q z) := by
  have hz : z.head?≠some a := Ne.symm model.first.1
  have tz : z.getLast?≠some a := Ne.symm model.last.1
  obtain ⟨gs,hq⟩ := body_form (w:=q) (model.nonempty Q) (model.first.2 ▸ hz) (model.last.2 ▸ tz)
  obtain ⟨es,he⟩ := body_form (w:=z) (model.nonempty Z) hz tz
  have nonempty (w : Word Bool) (l : List ℕ) (word : w=mixed 0 l 0) (len : 2≤w.length) : 0<l.length := by
    apply List.length_pos_iff.mpr
    rintro rfl
    simp [word,mixed,gapTail,run] at len
  have pg := nonempty _ _ hq (model.other_length (k:=P) (l:=Q) (by decide) rfl)
  have pe := nonempty _ _ he (model.other_length (k:=P) (l:=Z) (by decide) rfl)
  have cop : (es.length+1).Coprime (gs.length+1) := by
    apply Nat.dvd_one.mp
    apply model.divisors b
    rintro (_|(_|_))
    · simpa only [pieces,addToken,he,mixed_count] using Nat.gcd_dvd_left (es.length+1) (gs.length+1)
    · simp [pieces,addToken,pair,a,b]
    · simpa only [pieces,addToken,pair,hq,mixed_count] using Nat.gcd_dvd_right (es.length+1) (gs.length+1)
  have ne : gs.length≠es.length := by
    intro same
    rw [same,Nat.coprime_self] at cop
    omega
  have amb : ¬NamedCode (layout 0 gs 0 0 es 0) := by
    have bad := model.cuts .pieces
    change ¬NamedCode (pieces [a] q z) at bad
    rw [hq,he] at bad; exact bad
  obtain ⟨g,allG,allE,_⟩ := uniform_gaps_of_distinct_counts amb pg pe ne cop
  have formQ : q=body gs.length g := hq.trans (congrArg (fun l => mixed 0 l 0) (List.eq_replicate_iff.mpr ⟨rfl,allG⟩))
  have formZ : z=body es.length g := he.trans (congrArg (fun l => mixed 0 l 0) (List.eq_replicate_iff.mpr ⟨rfl,allE⟩))
  have pos : 0<g := by
    by_contra! h
    have zero : g=0 := by omega
    exact model.noncommuting (by simp [formQ,formZ,zero,body_zero,Nat.add_comm])
  exact ⟨⟨_,_,g,pg,pe,ne,cop,pos,formQ,formZ⟩⟩

theorem uniform_bounds {g m t s v h k : ℕ} (pm : 0<m) (pt : 0<t) (ne : m≠t) (cop : (t+1).Coprime (m+1))
    (amb : ¬NamedCode (layout s (List.replicate m g) v h (List.replicate t g) k)) :
    s≤g ∧ v≤g ∧ h≤g ∧ k≤g := by
  obtain ⟨d,allG,_,margins⟩ := uniform_gaps_of_distinct_counts amb (by simpa) (by simpa)
    (by simpa) (by simpa)
  exact (allG g (List.mem_replicate.mpr ⟨by omega,rfl⟩)).symm ▸ margins

/-- At n=0, apply the margin bound of Lemma 2 to both end cuts. The two
resulting bounds give an explicit pair of crossed parsings by uniform tiling. -/
theorem first_letter_zero {q z : Word Bool} {i j : ℕ} (model : Model [a] q z 0 i j) : False := by
  obtain ⟨⟨m,t,g,pm,pt,ne,cop,pos,eqQ,eqZ⟩⟩ := first_letter_data model
  have left : ¬NamedCode (layout 0 (List.replicate m g) (j+1) 0 (List.replicate t g) 0) := by
    have amb := model.endCuts false
    change ¬NamedCode (pieces [a] ((q++[a])++wordPow [a] j) z) at amb
    have word : (q++[a])++wordPow [a] j=mixed 0 (List.replicate m g) (j+1) := by
      rw [List.append_assoc,←wordPow_succ',singleton_power,eqQ]
      simpa [run] using body_bracket m g 0 (j+1)
    rw [word,eqZ] at amb; exact amb
  have right : ¬NamedCode (layout (i+1) (List.replicate m g) 0 0 (List.replicate t g) 0) := by
    have amb := model.endCuts true
    change ¬NamedCode (pieces [a] (wordPow [a] i++([a]++q)) z) at amb
    have word : wordPow [a] i++([a]++q)=mixed (i+1) (List.replicate m g) 0 := by
      rw [←List.append_assoc,←wordPow_succ,singleton_power,eqQ]
      simpa [run] using body_bracket m g (i+1) 0
    rw [word,eqZ] at amb; exact amb
  have hj := (uniform_bounds pm pt ne cop left).2.1
  have hi := (uniform_bounds pm pt ne cop right).1
  have no := uniform_cross_ambiguity g (i+1) m (j+1) 0 t 0 (by omega) (by omega)
  apply no
  have code := model.code
  change NamedCode (pieces [a] ((wordPow [a] (i+1)++(q++[a]))++wordPow [a] j) z) at code
  have word : (wordPow [a] (i+1)++(q++[a]))++wordPow [a] j =
      mixed (i+1) (List.replicate m g) (j+1) := by
    rw [List.append_assoc,List.append_assoc,←wordPow_succ',singleton_power,singleton_power,eqQ]
    simpa [run,List.append_assoc] using body_bracket m g (i+1) (j+1)
  rw [word,eqZ] at code; exact code

end ThreeWordCodes.Border
