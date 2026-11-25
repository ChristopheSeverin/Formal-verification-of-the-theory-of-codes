module

public import ThreeWordCodes.Normalization
public import ThreeWordCodes.OneMarker
public import ThreeWordCodes.Residues
public import ThreeWordCodes.Tilings

/-! # Minimal counterexamples with a pure power

Left decoding preserves the presence of a pure power. In a shortest binary
counterexample both terminal generators for either direction are letters.
This carries properties closed under left shortening down to single letters.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A I : Type*}

theorem NamedCode.noncommuting_entries {v : I → Word A} (hc : NamedCode v) {i j : I} (ne : i ≠ j) :
    v i ++ v j ≠ v j ++ v i := by
  intro comm
  have eqn : spell v [i,j] = spell v [j,i] := by simpa using comm
  exact ne (List.cons.inj (hc eqn)).1

/-- A reading of a pure word on two independent generators uses only one name. -/
theorem pure_decoding {g : Bool → Word A} (code : NamedCode g) (s : Word Bool)
    {a : A} {n : ℕ} (read : spell g s = List.replicate n a) :
    ∃ c : Bool, s = List.replicate s.length c := by
  classical
  have pure (c : Bool) (hc : c ∈ s) : g c = List.replicate (g c).length a := by
    apply List.eq_replicate_iff.mpr ⟨rfl,?_⟩
    intro x hx
    have mem : x ∈ spell g s := List.mem_flatMap.mpr ⟨c,hc,hx⟩
    rw [read] at mem
    exact (List.mem_replicate.mp mem).2
  by_cases f : false ∈ s
  · by_cases t : true ∈ s
    · exfalso
      apply code.noncommuting_entries (Bool.false_ne_true)
      simpa only [←List.replicate_add] using
        (show g false ++ g true = g true ++ g false from by
          calc g false ++ g true = List.replicate ((g false).length + (g true).length) a := by
                 conv_lhs => rw [pure false f,pure true t]
                 rw [List.replicate_add]
               _ = List.replicate ((g true).length + (g false).length) a := by rw [Nat.add_comm]
               _ = g true ++ g false := by
                 rw [List.replicate_add]
                 exact congrArg₂ List.append (pure true t).symm (pure false f).symm)
    · exact ⟨false,List.eq_replicate_iff.mpr ⟨rfl,fun b hb => by cases b <;> simp_all⟩⟩
  · exact ⟨true,List.eq_replicate_iff.mpr ⟨rfl,fun b hb => by cases b <;> simp_all⟩⟩

def HasPureEntry (v : Fin 3 → Word A) : Prop :=
  ∃ i a n, v i = List.replicate n a

def PureObstruction (v : Fin 3 → Word A) : Prop :=
  NamedCode v ∧ ¬ Completable v ∧ HasPureEntry v

def totalWordLength (v : Fin 3 → Word A) : ℕ := ∑ i, (v i).length

def ShortestPureObstruction (v : Fin 3 → Word Bool) : Prop :=
  PureObstruction v ∧ ∀ d : Fin 3 → Word Bool, PureObstruction d → totalWordLength v ≤ totalWordLength d

private theorem read_pure {v : Fin 3 → Word A} {g : Bool → Word A} {d : Fin 3 → Word Bool}
    (hc : NamedCode g) (e : (fun k => spell g (d k)) = v) (h : HasPureEntry v) : HasPureEntry d := by
  obtain ⟨k,a,n,word⟩ := h
  obtain ⟨c,he⟩ := pure_decoding hc (d k) ((congrFun e k).trans word)
  exact ⟨k,c,_,he⟩

theorem shortest_pure_obstruction [Fintype A] {v : Fin 3 → Word A} (h : PureObstruction v) :
    ∃ d : Fin 3 → Word Bool, ShortestPureObstruction d := by
  classical
  obtain ⟨g,d,e,base,code,bad,_⟩ := reduction_of_noncompletion h.1 h.2.1
  let S (n : ℕ) := ∃ p : Fin 3 → Word Bool, PureObstruction p ∧ totalWordLength p = n
  have existsN : ∃ n, S n := ⟨_,d,⟨code,bad,read_pure base.1 e h.2.2⟩,rfl⟩
  obtain ⟨p,obs,sz⟩ := Nat.find_spec existsN
  exact ⟨p,obs,fun q ob => sz ▸ Nat.find_min' existsN ⟨q,ob,rfl⟩⟩

private theorem obstruction_reverse {v : Fin 3 → Word Bool} (obs : PureObstruction v) :
    PureObstruction (fun i => (v i).reverse) := by
  obtain ⟨k,a,n,he⟩ := obs.2.2
  exact ⟨obs.1.reverse,fun hc => obs.2.1 (by simpa using hc.reverse),k,a,n,by simp [he]⟩

private theorem shortest_reverse {v : Fin 3 → Word Bool} (min : ShortestPureObstruction v) :
    ShortestPureObstruction (fun i => (v i).reverse) := by
  refine ⟨obstruction_reverse min.1,fun d ob => ?_⟩
  simpa [totalWordLength] using min.2 _ (obstruction_reverse ob)

private theorem binary_names_used (d : Fin 3 → Word Bool) (code : NamedCode d) (b : Bool) :
    ∃ i, b ∈ d i := by
  by_contra! h
  have pure (i : Fin 3) : d i = List.replicate (d i).length (!b) :=
    List.eq_replicate_iff.mpr ⟨rfl,fun c hc => by cases b <;> cases c <;> simp_all⟩
  apply code.noncommuting_entries (by decide : (0 : Fin 3) ≠ 1)
  calc d 0 ++ d 1 = List.replicate ((d 0).length + (d 1).length) (!b) := by
         rw [List.replicate_add]
         exact congrArg₂ List.append (pure 0) (pure 1)
       _ = List.replicate ((d 1).length + (d 0).length) (!b) := by rw [Nat.add_comm]
       _ = d 1 ++ d 0 := by
         rw [List.replicate_add]
         exact congrArg₂ List.append (pure 1).symm (pure 0).symm

theorem literal_trace_of_minimal_decoding {v : Fin 3 → Word Bool} (cv : NamedCode v) (no : ¬ Completable v)
    (minimal : ∀ (g : Bool → Word Bool) (d : Fin 3 → Word Bool),
      (fun k => spell g (d k)) = v → Completable g → NamedCode d → ¬ Completable d →
      totalWordLength v ≤ totalWordLength d) :
    ∃ f : Bool → Bool, Function.Surjective f ∧ LeftReductionTrace v (fun c => [f c]) := by
  obtain ⟨g,d,e,base,code,bad,trace⟩ := reduction_of_noncompletion cv no
  have lens (k : Fin 3) : (d k).length ≤ (v k).length := by
    rw [←congrFun e k]
    exact coded_length base.1.entry_ne_nil _
  have single (c : Bool) : ∃ a, g c = [a] := by
    apply List.length_eq_one_iff.mp
    have pos := List.length_pos_iff.mpr (base.1.entry_ne_nil c)
    by_contra ne
    obtain ⟨k,hk⟩ := binary_names_used d code c
    have lt := coded_length_strict base.1.entry_ne_nil (show 1 < (g c).length by omega) _ hk
    rw [congrFun e k] at lt
    have total : totalWordLength d < totalWordLength v :=
      Finset.sum_lt_sum (fun i _ => lens i) ⟨k,Finset.mem_univ _,lt⟩
    exact Nat.not_lt_of_ge (minimal g d e base code bad) total
  choose f name using single
  refine ⟨f,Finite.surjective_of_injective (fun i j e => base.1.entries_injective
    (show g i = g j by rw [name i,name j,e])),?_⟩
  simpa only [show (fun c => [f c]) = g from funext fun c => (name c).symm] using trace

/-- Both terminal-generator traces identify the endpoint and count invariants. -/
theorem invariants_of_literal_traces {v : Fin 3 → Word Bool}
    (left : ∃ f : Bool → Bool, Function.Surjective f ∧ LeftReductionTrace v (fun c => [f c]))
    (right : ∃ f : Bool → Bool, Function.Surjective f ∧
      LeftReductionTrace (fun i => (v i).reverse) (fun c => [f c])) :
    (∀ a, ∃ k, (v k).head? = some a) ∧ (∀ a, ∃ k, (v k).getLast? = some a) ∧
    (∀ (a : Bool) (m : ℕ), (∀ k, m ∣ (v k).count a) → m ∣ 1) ∧
    (∀ (P : Word Bool → Prop), (∀ x y, P x → P (x++y) → P y) → (∀ k, P (v k)) → ∀ a, P [a]) := by
  obtain ⟨f,onto,tr⟩ := left
  obtain ⟨r,rot,rtr⟩ := right
  constructor
  · intro a
    obtain ⟨c,rfl⟩ := rot a
    obtain ⟨i,hi⟩ := rtr.finals c
    exact ⟨i,by simpa using hi.symm⟩
  refine ⟨?_,?_,?_⟩
  · intro a
    obtain ⟨c,rfl⟩ := onto a
    obtain ⟨i,hi⟩ := tr.finals c
    exact ⟨i,by simpa using hi.symm⟩
  · intro a m all
    obtain ⟨c,rfl⟩ := onto a
    simpa using tr.divisors (fun w => w.count (f c)) (by simp) m all c
  · intro P cut all a
    obtain ⟨c,rfl⟩ := onto a
    exact tr.inherited P cut all c

private theorem pure_trace {v : Fin 3 → Word Bool} (min : ShortestPureObstruction v) :
    ∃ f : Bool → Bool, Function.Surjective f ∧ LeftReductionTrace v (fun c => [f c]) :=
  literal_trace_of_minimal_decoding min.1.1 min.1.2.1 (fun _ _ e base code bad =>
    min.2 _ ⟨code,bad,read_pure base.1 e min.1.2.2⟩)

/-- A shortest counterexample in the pure-power class uses both end letters in
each direction. Every common divisor of a letter count divides one. -/
theorem shortest_pure_invariants {v : Fin 3 → Word Bool} (min : ShortestPureObstruction v) :
    (∀ a, ∃ k, (v k).head? = some a) ∧ (∀ a, ∃ k, (v k).getLast? = some a) ∧
    (∀ (a : Bool) (m : ℕ), (∀ k, m ∣ (v k).count a) → m ∣ 1) ∧
    (∀ (P : Word Bool → Prop), (∀ x y, P x → P (x++y) → P y) → (∀ k, P (v k)) → ∀ a, P [a]) :=
  invariants_of_literal_traces (pure_trace min) (pure_trace (shortest_reverse min))

end ThreeWordCodes
