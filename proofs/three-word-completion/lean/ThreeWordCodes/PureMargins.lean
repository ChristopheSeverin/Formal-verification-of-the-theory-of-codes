module

public import ThreeWordCodes.PureReduction
public import ThreeWordCodes.Alphabet

/-! # Normal form of a minimal pure-power counterexample (Proposition 6)

Equal terminal residues force the exponent of the pure entry to be one.
The coprime two-marker argument then reduces the problem to a single bounded
list of gaps between consecutive markers.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {A : Type*}

private def leading : Word Bool → ℕ
  | [] => 0
  | false :: t => leading t + 1
  | true :: _ => 0

private theorem leading_run (n : ℕ) (t : Word Bool) : leading (run n ++ t) = n + leading t := by
  induction n with
  | zero => simp [run]
  | succ n ih => change leading (run n ++ t) + 1 = _; omega

private def trailing (w : Word Bool) : ℕ := leading w.reverse

private theorem trailing_run (n : ℕ) : trailing (run n) = n := by
  simpa [trailing,run,leading] using leading_run n []

private theorem trailing_mixed (s : Word Bool) (i : ℕ) (gs : List ℕ) (j : ℕ) :
    trailing (s ++ mixed i gs j) = j := by
  rw [trailing,List.reverse_append,reverse_mixed]
  simp only [mixed,List.append_assoc,leading_run,
    List.cons_append,leading,Nat.add_zero]

private theorem run_of_no_marker (w : Word Bool) (missing : b ∉ w) : w = run w.length :=
  List.eq_replicate_iff.mpr ⟨rfl,fun x hx => by cases x <;> first | rfl | exact (missing hx).elim⟩

private theorem trailing_cut (n : ℕ) (s t : Word Bool) (hs : n ∣ trailing s)
    (hst : n ∣ trailing (s++t)) : n ∣ trailing t := by
  by_cases hb : b ∈ t
  · obtain ⟨i,g,j,rfl⟩ := mixed_of_contains_marker hb
    simpa only [trailing_mixed,List.nil_append] using
      (show n ∣ trailing ([] ++ mixed i g j) from (trailing_mixed [] i g j).symm ▸
        ((trailing_mixed s i g j) ▸ hst))
  · let k := t.length
    have ht : t = run k := run_of_no_marker t hb
    rw [ht,trailing_run]
    rw [ht] at hst
    have eqn : trailing (s++run k) = k + trailing s := by
      simpa [trailing,run] using leading_run k s.reverse
    rw [eqn] at hst
    exact (Nat.dvd_add_left hs).mp hst

private theorem trailing_of_last {w : Word Bool} (he : w.getLast? = some b) : trailing w = 0 := by
  have head : w.reverse.head? = some b := by simpa using he
  cases e : w.reverse with
  | nil => simp [e] at head
  | cons x s =>
    simp only [e,List.head?_cons,Option.some.injEq] at head
    simp [trailing,e,head,b,leading]

private theorem mixed_last_form (i : ℕ) (g : List ℕ) (j : ℕ) :
    mixed i g j = (gapTail i g.reverse).reverse ++ b :: run j := by
  calc mixed i g j = (mixed j g.reverse i).reverse := by simp [reverse_mixed]
       _ = _ := by simp [mixed,run,List.append_assoc]

private def resName : Option Bool → Option Bool
  | some false => none
  | some true => some false
  | none => some true

private theorem distinct_tail_completion (n : ℕ) (positive : 0 < n) (i : ℕ) (g : List ℕ) (j h : ℕ)
    (e : List ℕ) (q : ℕ) (ne : j%n ≠ q%n) :
    Completable (addToken (pair (run n) (mixed i g j)) (mixed h e q)) := by
  let pre := pair (gapTail i g.reverse).reverse (gapTail h e.reverse).reverse
  let tail (c : Bool) := if c then q else j
  have hread : (fun k => residueWords n pre tail (resName k)) =
      addToken (pair (run n) (mixed i g j)) (mixed h e q) := by
    funext k
    rcases k with _ | (_ | _)
    · exact (mixed_last_form ..).symm
    · rfl
    · exact (mixed_last_form ..).symm
  refine hread ▸ (residue_completion n positive pre tail ?_).reindex
    (show Function.Injective resName by decide)
  intro x y he
  cases x <;> cases y <;> simp_all [tail,Ne.symm ne]

private theorem obstacle_flip {v : Fin 3 → Word Bool} (obs : PureObstruction v) (c : Bool) :
    PureObstruction (fun i => (v i).map (letterFlip c)) := by
  obtain ⟨k,a,n,hp⟩ := obs.2.2
  exact ⟨(named_flip_iff _ c).mpr obs.1,fun h => obs.2.1 ((completable_flip_iff _ c).mp h),
    k,letterFlip c a,n,by simp [hp]⟩

private theorem minimal_flip {v : Fin 3 → Word Bool} (min : ShortestPureObstruction v) (c : Bool) :
    ShortestPureObstruction (fun i => (v i).map (letterFlip c)) := by
  refine ⟨obstacle_flip min.1 c,fun w obs => ?_⟩
  simpa [totalWordLength] using min.2 _ (obstacle_flip obs c)

private theorem ordered_names (p : Fin 3) (s : Fin 3 → ℕ) :
    ∃ u v : Fin 3, Function.Bijective (threeNames p u v) ∧ s u ≤ s v := by
  obtain ⟨u,v,bijection⟩ := order_three p
  by_cases h : s u ≤ s v
  · exact ⟨u,v,bijection,h⟩
  · have swap : ∀ p u v, Function.Bijective (threeNames p u v) → Function.Bijective (threeNames p v u) := by decide
    exact ⟨v,u,swap _ _ _ bijection,by omega⟩

/-- In a shortest counterexample the distinguished pure power is a single
letter, and the other words have the ordered gap-list form used in the paper. -/
theorem pure_to_letter_layout [Fintype A] {v : Fin 3 → Word A} (obs : PureObstruction v) :
    ∃ i g j h e q, NamedCode (layout i g j h e q) ∧ ¬ Completable (layout i g j h e q) ∧
      g.length ≤ e.length ∧ (e.length+1).Coprime (g.length+1) ∧
      (i=0 ∨ h=0) ∧ (j=0 ∨ q=0) := by
  obtain ⟨v₀,min₀⟩ := shortest_pure_obstruction obs
  obtain ⟨p,c,n,power⟩ := min₀.1.2.2
  let v (k : Fin 3) := (v₀ k).map (letterFlip c)
  have min : ShortestPureObstruction v := minimal_flip min₀ c
  have hp : v p = run n := by cases c <;> simp [v,power,run,letterFlip,a]
  have pos : 0 < n := by
    by_contra! h
    exact min.1.1.entry_ne_nil p (by simpa [Nat.eq_zero_of_le_zero h,run] using hp)
  obtain ⟨u,z,bij,order⟩ := ordered_names p (fun k => (v k).count b)
  let names := Equiv.ofBijective _ bij
  let d (k : Option Bool) := v (names k)
  have code : NamedCode d := min.1.1.reindex bij.1
  have no : ¬ Completable d := fun hc => min.1.2.1 ((completable_reindex_iff v names).mp hc)
  have pure : d (some false) = run n := hp
  have marker (k : Option Bool) (hne : k ≠ some false) : b ∈ d k := by
    by_contra fail
    apply code.noncommuting_entries hne
    calc d k ++ d (some false) = run ((d k).length + n) := by
           rw [run_add,pure]
           exact congrArg (· ++ run n) (run_of_no_marker _ fail)
         _ = run (n + (d k).length) := by rw [Nat.add_comm]
         _ = d (some false) ++ d k := by
           rw [run_add,pure]
           exact congrArg (run n ++ ·) (run_of_no_marker _ fail).symm
  obtain ⟨i,g,j,hu⟩ := mixed_of_contains_marker (marker (some true) (by decide))
  obtain ⟨h,e,q,hz⟩ := mixed_of_contains_marker (marker none (by decide))
  have present : d = addToken (pair (run n) (mixed i g j)) (mixed h e q) := by
    funext k
    rcases k with _ | (_ | _) <;> assumption
  have sizes : g.length ≤ e.length := by
    change (d (some true)).count b ≤ (d none).count b at order
    simpa only [hu,hz,mixed_count,Nat.add_le_add_iff_right] using order
  obtain ⟨heads,lasts,counts,cut⟩ := shortest_pure_invariants min
  have bEnd : ∃ k : Option Bool, (d k).getLast? = some b := by
    obtain ⟨k,hk⟩ := lasts b
    exact ⟨names.symm k,by simpa [d] using hk⟩
  obtain ⟨k,endpoint⟩ := bEnd
  have terminal := trailing_of_last endpoint
  have tailU : trailing (d (some true)) = j := hu ▸ (trailing_mixed [] i g j)
  have tailZ : trailing (d none) = q := hz ▸ (trailing_mixed [] h e q)
  have lastZero : j=0 ∨ q=0 := by
    rcases k with _ | (_ | _)
    · exact Or.inr (tailZ.symm.trans terminal)
    · rw [pure,trailing_run] at terminal
      omega
    · exact Or.inl (tailU.symm.trans terminal)
  have equalRes : j%n = q%n := by
    by_contra ne
    exact no (present.symm ▸ distinct_tail_completion n pos i g j h e q ne)
  have bothDiv : n ∣ j ∧ n ∣ q := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    rcases lastZero with zero | zero
    · have x : j%n = 0 := by simp [zero]
      exact ⟨x,equalRes.symm.trans x⟩
    · have x : q%n = 0 := by simp [zero]
      exact ⟨equalRes.trans x,x⟩
  have divisible (k : Option Bool) : n ∣ trailing (d k) := by
    rcases k with _ | (_ | _)
    · simpa only [tailZ] using bothDiv.2
    · simp [pure,trailing_run]
    · simpa only [tailU] using bothDiv.1
  have one : n = 1 := by
    have all (k : Fin 3) : n ∣ trailing (v k) := by simpa [d] using divisible (names.symm k)
    have dvd := cut (fun w => n ∣ trailing w) (trailing_cut n) all a
    exact Nat.dvd_one.mp dvd
  have firstZero : i=0 ∨ h=0 := by
    obtain ⟨k,head⟩ := heads b
    have start : (d (names.symm k)).head? = some b := by simpa [d] using head
    cases idx : names.symm k with
    | none =>
      rw [idx,hz] at start
      cases h with
      | zero => exact Or.inr rfl
      | succ h => simp [mixed,run,a,b,List.replicate_succ] at start
    | some y =>
      cases y
      · rw [idx,pure,one] at start
        contradiction
      · rw [idx,hu] at start
        cases i with
        | zero => exact Or.inl rfl
        | succ i => simp [mixed,run,a,b,List.replicate_succ] at start
  have cop : (e.length+1).Coprime (g.length+1) := by
    let m := (e.length+1).gcd (g.length+1)
    have each (k : Option Bool) : m ∣ (d k).count b := by
      rcases k with _ | (_ | _)
      · rw [hz,mixed_count]
        exact Nat.gcd_dvd_left ..
      · simp [pure,one,run,a,b]
      · rw [hu,mixed_count]
        exact Nat.gcd_dvd_right ..
    exact Nat.dvd_one.mp (counts b m (fun k => by simpa [d] using each (names.symm k)))
  subst n
  change d = layout i g j h e q at present
  exact ⟨i,g,j,h,e,q,present ▸ code,present ▸ no,sizes,cop,firstZero,lastZero⟩

/-- The remaining one-marker family of Section 3. Every gap is at least
max(k,l) and at least one gap is too short to fit both margins. -/
def OneMarkerConstruction : Prop :=
  ∀ (k l : ℕ) (gs : List ℕ), 0 < k → 0 < l → (∀ g ∈ gs, max k l ≤ g) →
    (∃ g ∈ gs, g < k+l) → NamedCode (oneMarker k l (mixed 0 gs 0)) →
    Completable (oneMarker k l (mixed 0 gs 0))

/-- Proposition 6 for named triples on every finite alphabet. -/
def PurePowerTheorem.{u} : Prop :=
  ∀ (A : Type u) [Fintype A] (v : Fin 3 → Word A), NamedCode v → HasPureEntry v → Completable v

/-- Every counterexample to Proposition 6 yields a counterexample with one
letter a, one word a^k b a^l, and a third word starting and ending in b. -/
theorem one_marker_suffices.{u} (construct : OneMarkerConstruction) : PurePowerTheorem.{u} := by
  intro A _ v code power
  by_contra bad
  obtain ⟨i,g,j,h,e,q,cv,nc,le,cop,leftEnd,rightEnd⟩ :=
    pure_to_letter_layout (show PureObstruction v from ⟨code,bad,power⟩)
  by_cases empty : g = []
  · subst g
    by_cases iz : i=0
    · subst i
      exact nc (right_marker_completion j (mixed h e q) cv)
    by_cases jz : j=0
    · subst j
      exact nc (left_marker_completion i (mixed h e q) cv)
    obtain rfl := leftEnd.resolve_left iz
    obtain rfl := rightEnd.resolve_left jz
    have gaps := one_marker_gaps nc
    by_cases short : ∃ z ∈ e, z < i+j
    · exact nc (construct i j e (Nat.pos_of_ne_zero iz) (Nat.pos_of_ne_zero jz) gaps short cv)
    · push Not at short
      exact long_gap_ambiguity i j e short cv
  · have pos := List.length_pos_iff.mpr empty
    have lt : g.length < e.length := by
      by_contra! he
      have eqn : e.length = g.length := by omega
      rw [eqn,Nat.coprime_self] at cop
      omega
    exact nc (two_mixed_completion cv (by omega) lt cop leftEnd rightEnd)

/-- For the converse, this binary family is itself a family of three-word
inputs with a pure entry. Thus the remaining obligation is exact. -/
theorem pure_power_iff_one_marker : PurePowerTheorem.{0} ↔ OneMarkerConstruction := by
  refine ⟨?_,one_marker_suffices⟩
  intro power k l gs _ _ _ _ hc
  let w := oneMarker k l (mixed 0 gs 0)
  obtain ⟨u,z,bij⟩ := order_three 0
  let e := Equiv.ofBijective _ bij
  let v (j : Fin 3) := w (e.symm j)
  have code : NamedCode v := hc.reindex e.symm.injective
  have pure : HasPureEntry v := ⟨e (some false),a,1,by simp [v,w,oneMarker,addToken,pair]⟩
  simpa only [v,Equiv.symm_apply_apply] using (power Bool v code pure).reindex e.injective

end ThreeWordCodes.BinaryGaps
