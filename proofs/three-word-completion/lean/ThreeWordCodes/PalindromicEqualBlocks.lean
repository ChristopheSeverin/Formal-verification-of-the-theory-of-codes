module

public import ThreeWordCodes.PalindromicPattern

/-! # Repeated equal blocks between every pair of minimum gaps -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

private theorem only_before_separator (m : ℕ) (P tail : List ℕ) (shorter : tail.length<P.length)
    (large : ∀ n∈P,m<n) : OnlyAtStart P (P++m::tail) := by
  intro pre W after occurrence dominates
  by_contra nonempty
  have positive := List.length_pos_iff.mpr nonempty
  have count := dominates.length_eq
  have sizes := congrArg List.length occurrence
  simp only [List.length_append,List.length_cons] at sizes
  have atM := congrArg (fun v : List ℕ => v[P.length]?) occurrence
  rw [List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero] at atM
  rw [List.getElem?_append_right (show pre.length≤P.length by omega),
    List.getElem?_append_left (show P.length-pre.length<W.length by omega)] at atM
  exact Nat.lt_irrefl _ (dominates.lower large m (List.mem_of_getElem? atM.symm))

private theorem equal_end_short (s k l m : ℕ) (P later : List ℕ) (z : Word Bool)
    (read : Reading s (P++m::(P++later)) z) (nonempty : P≠[]) (above : ∀ n∈P,m<n)
    (bound : max k l≤m) (last : P.getLast nonempty≤k+l)
    (low : ∀ n∈P++m::(P++later),l≤n) (ending : z.getLast?=some b) : Completable (triple s k l z) := by
  have uEnd : EndsBelow (k+l) P := ⟨P.dropLast,P.getLast nonempty,(List.dropLast_concat_getLast nonempty).symm,last⟩
  have pos := above _ (List.getLast_mem nonempty)
  apply pattern_completion s k l (k+l) P m [] P later z (by simpa using read) (by omega) le_rfl
    (by simpa using low) nonempty (by omega) uEnd (List.prefix_refl _) _ _ ending
  · intro pre W tail pos dom
    have count := dom.length_eq
    have total := congrArg List.length pos
    exact List.length_eq_zero_iff.mp (by simp at total; omega)
  · intro p hp
    rcases List.prefix_cons_iff.mp hp.1 with rfl | ⟨t,rfl,sub⟩
    · obtain ⟨_,_,e,_⟩ := hp.2.2
      simp at e
    · apply only_before_separator m P t _ above
      have := hp.2.1
      simpa using this

/-- If a nonempty long suffix follows the chosen short gap in P, the next
minimum is internal to the demand. It cannot occur inside the first copy
of P. This argument allows an arbitrary continuation after the second copy. -/
private theorem equal_end_long (s k l m d n : ℕ) (before rest P later : List ℕ) (z : Word Bool)
    (form : P=before++d::n::rest) (read : Reading s (P++m::(P++later)) z)
    (bound : max k l≤m) (short : d≤k+l) (above : ∀ v∈P,m<v)
    (long : ∀ v∈n::rest,d<v) (low : ∀ v∈P++m::(P++later),l≤v) (ending : z.getLast?=some b) :
    Completable (triple s k l z) := by
  let U := before++[d]
  have first : P≠[] := by simp [form]
  let g := P.head first
  let tail := P.tail++later
  have pcons : g::P.tail=P := List.cons_head_tail first
  have inU {v : ℕ} (hv : v∈U) : v∈P := by
    rw [form]
    rcases List.mem_append.mp hv with a | b
    · simp [a]
    · simp [List.mem_singleton.mp b]
  have md := above d (inU (by simp [U]))
  have gLarge := above g (List.head_mem first)
  have shape : U++((n::rest)++[m])++g::tail=P++m::(P++later) := by
    have tailEq : g::tail=P++later := by change (g::P.tail)++later=_; rw [pcons]
    rw [tailEq]
    conv_rhs => lhs; rw [form]
    simp [U,List.append_assoc]
  have lastU : ∀ p∈[U],∃ pre v,p=pre++[v] ∧ v≤d := by
    intro p hp; exact ⟨before,d,List.mem_singleton.mp hp,le_rfl⟩
  apply raw_selection s k l l d [U] U ((n::rest)++[m]) g tail z (shape.symm ▸ read)
    le_rfl (by omega) (by omega) (by omega) (by simp) (shape.symm ▸ low)
    (by intro p hp v hv; obtain rfl := List.mem_singleton.mp hp; exact low v (by simp [inU hv]))
    lastU (by simp) _ ending
  intro r us origin
  have miss : m∉us := by
    rcases origin with ⟨rfl,_⟩ | ⟨p,hp,pre,v,whereAt,_⟩
    · simp
    · intro hm
      obtain rfl := List.mem_singleton.mp hp
      exact Nat.lt_irrefl _ (above m (inU (by rw [whereAt]; simp [hm])))
  constructor
  · intro isPre
    rcases List.prefix_concat_iff.mp isPre with full | early
    · have tailEq := (List.cons.inj full).2
      exact (miss (by simp [tailEq])).elim
    · obtain ⟨p,v,eqn,le⟩ := Origin.ends_short origin lastU
      have := long v (early.sublist.subset (by simp [eqn]))
      omega
  · intro j t full _
    have tailEq := (List.cons.inj full).2
    exact miss (by simp [tailEq])

/-- When all blocks between minimum gaps agree, a code has a completion.
This applies to arbitrarily long lists and arbitrarily many repetitions. -/
theorem equal_blocks_completion (s k l m : ℕ) (P : List ℕ) (j : ℕ) (z : Word Bool)
    (read : Reading s (P++wordPow (m::P) (j+1)) z) (bound : max k l≤m) (short : m≤k+l)
    (above : ∀ n∈P,m<n) (low : ∀ n∈P++wordPow (m::P) (j+1),l≤n)
    (code : NamedCode (triple s k l z)) : Completable (triple s k l z) := by
  by_contra bad
  have ending := (residual_word code bad).2.1
  by_cases small : ∃ n∈P,n<k+l+1
  · obtain ⟨before,d,tail,split,ds,remaining⟩ := last_below (k+l+1) P small
    let extra := wordPow (m::P) j
    have total : P++wordPow (m::P) (j+1)=P++m::(P++extra) := by rw [wordPow_succ']; rfl
    cases tail with
    | nil =>
      have ne : P≠[] := by simp [split]
      have lt : P.getLast?=some d := by rw [split,List.getLast?_concat]
      have last : P.getLast ne=d := Option.some.inj ((List.getLast?_eq_getLast_of_ne_nil ne).symm.trans lt)
      exact bad (equal_end_short s k l m P extra z (total ▸ read) ne above bound (by omega) (total ▸ low) ending)
    | cons n rest =>
      exact bad (equal_end_long s k l m d n before rest P extra z split (total ▸ read) bound (by omega) above
        (fun v hv => by have := remaining v hv; omega) (total ▸ low) ending)
  · have model := (read.equations k l).namedCode_iff.mpr code
    let T := P.map (1+·)
    apply (one_marker_ambiguity_iff (k+1) (l+1) _).mpr _ model
    right
    refine ⟨T,1+m,j,by omega,by omega,?_,?_⟩
    · intro v hv
      obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hv
      have ge : ¬ i<k+l+1 := fun half => small ⟨i,mem,half⟩
      omega
    · simp [T,pow_map]

end ThreeWordCodes.Palindromic
