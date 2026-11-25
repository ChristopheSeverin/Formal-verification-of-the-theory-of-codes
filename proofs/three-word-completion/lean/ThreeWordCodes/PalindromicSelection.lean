module

public import ThreeWordCodes.PalindromicRecords

/-! # Recognizing a prescribed sequence of gaps from a visible initial

A literal prefix may stop inside its final x token. Its first letter still
identifies that token. A matching suffix either finishes at an earlier ba,
or recognizes the entire demand with the final gap possibly enlarged.
-/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem compare_visible (s h : ℕ) (p q : Word Bool) (t : Word Bool)
    (visible : spell (readers s h) p ++ [a] <+: t)
    (compare : Comparable t (spell (readers s h) q)) :
    Comparable (p++[a]) q := by
  let v := readers s h
  obtain ⟨inj,nz,pf⟩ := reader_prefix s h
  have base : spell v p <+: t := (List.prefix_append ..).trans visible
  have nameCmp : Comparable p q := by
    rcases compare with tpre | qpre
    · exact Or.inl (prefix_reflection inj nz pf (base.trans tpre))
    · exact (List.prefix_or_prefix_of_prefix base qpre).imp
        (prefix_reflection inj nz pf) (prefix_reflection inj nz pf)
  rcases nameCmp with ⟨u,form⟩ | first
  · cases u with
    | nil => right; rw [←form,List.append_nil]; exact List.prefix_append ..
    | cons i u =>
      cases i with
      | false => left; exact ⟨u,by simpa using form⟩
      | true =>
        have firstB : spell v p++[b] <+: spell v q := by
          rw [←form,spell_append,spell_cons]
          exact ⟨_,(List.append_assoc ..)⟩
        have conflict : ¬Comparable (spell v p++[a]) (spell v p++[b]) := by
          rintro (⟨u,e⟩ | ⟨u,e⟩) <;> simp [List.append_assoc,a,b] at e
        rcases compare with tpre | qpre
        · exact (conflict (List.prefix_or_prefix_of_prefix (visible.trans tpre) firstB)).elim
        · exact (conflict (List.prefix_or_prefix_of_prefix visible (firstB.trans qpre))).elim
  · exact Or.inr (first.trans (List.prefix_append ..))

theorem tail_append (j : ℕ) (u v : List ℕ) :
    gapTail j (u++v)=gapTail 0 u++gapTail j v := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [gapTail,ih,List.append_assoc]

private theorem append_run_tail (r : ℕ) (xs : List ℕ) (h : ℕ) :
    gapTail r xs ++ run h = gapTail (r+h) xs := by
  induction xs with
  | nil => exact (run_add ..).symm
  | cons x xs ih => simp [gapTail,List.append_assoc,ih]

theorem gap_names_join (cut front : List ℕ) :
    mixed 0 (cut++front) 0=mixed 0 cut 0 ++ gapTail 0 front := by
  simp [mixed,tail_append,run]

private theorem last_name (g : ℕ) (front : List ℕ) :
    gapTail g front ++ [a]=gapTail (g+1) front := append_run_tail g front 1

private theorem parse_visible {p : List ℕ} {g r : ℕ} {us : List ℕ} (pos : 0<g)
    (overlap : Comparable (gapTail g p) (mixed r us 0)) :
    (r::us <+: p) ∨ (∃ j t,r::us=p++j::t ∧ g≤j) := by
  change gapTail g p <+: gapTail 0 (r::us) ∨ gapTail 0 (r::us) <+: gapTail g p at overlap
  rcases overlap with full | early
  · obtain ⟨⟨tail,form⟩,le⟩ := tail_prefix full
    right
    cases tail with
    | nil => simp [←form] at le; omega
    | cons j t => exact ⟨j,t,form.symm,by simpa [←form] using le⟩
  · exact Or.inl (tail_prefix early).1

/-- Numerical tests for a demand ending at a long gap. The cut, the
demand, and the host suffixes use the numbers of free x tokens after grouping
h forced x tokens with each ba. -/
theorem selected_completion (s k l h d : ℕ) (cuts : List (List ℕ)) (cut front : List ℕ)
    (g : ℕ) (later : List ℕ) (z : Word Bool)
    (read : Reading s ((cut++front++g::later).map (h+·)) z)
    (height : h≤l) (width : d≤k) (pos : 0<g) (chosen : cut∈cuts)
    (last : ∀ p∈cuts, ∃ pre z, p=pre++[z] ∧ z≤d)
    (antichain : ∀ p∈cuts, ∀ q∈cuts, p <:+ q → p=q)
    (test : ∀ r us, (us=[] ∧ r≤d ∨ ∃ p∈cuts, ∃ pre v, p=pre++v::us ∧ r≤v) →
      ((r::us <+: front) → cut++r::us∈cuts) ∧
      (∀ j tail, r::us=front++j::tail → g≤j → False))
    (ending : z.getLast?=some b) : Completable (triple s k l z) := by
  let v := readers s h
  let norm (ls : List ℕ) := ls.map (h+·)
  have grouped (ls : List ℕ) : spell v (mixed 0 ls 0)=(c++following s (norm ls))++wordPow (x s) h := by
    have restore : (norm ls).map (·-h)=ls := by simp [norm,List.map_map,Function.comp_def]
    rw [←grouped_spelling s h (norm ls) (by intro n hn; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hn; omega),restore]
  have raw : Reading s (norm (cut++front)++(h+g)::norm later) z := by
    simpa [norm] using read
  have canSee := raw.visible_prefix (norm (cut++front)) (h+g) (h+(g-1)) (norm later) (by omega)
  let P := gapTail (g-1) front
  have combined : spell v (mixed 0 cut 0)++spell v P =
      (c++following s (norm (cut++front)))++wordPow (x s) (h+(g-1)) := by
    have nameEq : mixed 0 cut 0 ++ P=mixed 0 (cut++front) 0 ++ run (g-1) := by
      rw [gap_names_join,List.append_assoc,append_run_tail,Nat.zero_add]
    rw [←spell_append,nameEq,spell_append,grouped,wordPow_add,List.append_assoc]
    simp [run,spell_replicate,v,readers,pair]
  rw [←combined,List.append_assoc] at canSee
  obtain ⟨remaining,cutEq⟩ := canSee
  let t := (spell v P++[a])++remaining
  have form : spell v (mixed 0 cut 0)++t=z := by simpa [t,List.append_assoc] using cutEq
  have visible : spell v P++[a] <+: t := List.prefix_append ..
  have nt : t≠[] := by simp [t]
  have endT : t.getLast?=some b := by
    simpa only [←form,List.getLast?_append,List.getLast?_eq_getLast_of_ne_nil nt,Option.some_or] using ending
  have endA (r : ℕ) (ns : List ℕ) : (spell v (mixed r ns 0)).getLast?=some a := by
    have shape : ∃ p,mixed r ns 0=p++[b] := by
      have he : (mixed r ns 0).getLast?=some b := by rw [←List.head?_reverse,reverse_mixed]; rfl
      exact List.getLast?_eq_some_iff.mp he
    obtain ⟨p,eqn⟩ := shape
    rw [eqn,spell_append,spell_cons,spell_nil,List.append_nil]
    cases h with
    | zero => simp [v,readers,pair,c]
    | succ h =>
      change (spell (readers s (h+1)) p ++ (c++wordPow (x s) (h+1))).getLast?=some a
      rw [wordPow_succ]
      simp [x]
  obtain ⟨hi,ne,pf⟩ := reader_prefix s h
  have cert := selected_gap_certificate v hi ne pf d cuts cut t chosen nt last antichain (by
    intro r us origin
    refine ⟨fun eq => by have e := (endA r us).symm.trans ((congrArg List.getLast? eq).trans endT); contradiction,?_⟩
    intro cp
    have name := compare_visible s h P (mixed r us 0) t visible cp
    have lastEq : P++[a]=gapTail g front := by
      rw [show P=gapTail (g-1) front from rfl,last_name,show g-1+1=g by omega]
    rw [lastEq] at name
    rcases parse_visible pos name with early | ⟨j,tail,full,le⟩
    · exact (test r us origin).1 early
    · exact ((test r us origin).2 j tail full le).elim)
  have mid : spell v (mixed (d+1) [] 0)=y s d h := by simp [v,readers,pair,mixed,run,gapTail,y,spell_replicate,List.append_assoc]
  rw [mid,form] at cert
  have initial : z.head?=some b := by rw [←form,grouped]; rfl
  exact raise_exponents (from_certificate initial cert) k l width height

end ThreeWordCodes.Palindromic
