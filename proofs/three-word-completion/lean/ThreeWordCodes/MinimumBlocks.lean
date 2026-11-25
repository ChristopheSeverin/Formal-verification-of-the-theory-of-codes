module

public import ThreeWordCodes.RepeatedCuts

/-! # Single minima and repeated equal blocks in the one-marker construction -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

theorem last_below (k : ℕ) (P : List ℕ) (found : ∃ x∈P,x<k) :
    ∃ front d tail, P=front++d::tail ∧ d<k ∧ ∀ x∈tail,k≤x := by
  induction P using List.reverseRecOn with
  | nil => simp at found
  | append_singleton pre n ih =>
    by_cases short : n<k
    · exact ⟨pre,n,[],rfl,short,by simp⟩
    · obtain ⟨front,d,tail,eqn,small,above⟩ := ih (by
        obtain ⟨x,mem,lt⟩ := found
        refine ⟨x,?_,lt⟩
        rcases List.mem_append.mp mem with h | h
        · exact h
        · obtain rfl := List.mem_singleton.mp h
          exact (short lt).elim)
      refine ⟨front,d,tail++[n],by rw [eqn]; simp,small,?_⟩
      intro x hx
      rcases List.mem_append.mp hx with older | last
      · exact above x older
      · obtain rfl := List.mem_singleton.mp last
        omega

/-- If the opening block P occurs again after a new short separator and has
some short gap of its own, a graft succeeds. The continuation is unrestricted.
Gap sizes in this theorem are offsets from h. -/
theorem initial_repeated_block_completion (k h m : ℕ) (P later : List ℕ)
    (pos : 0<h) (short : m<k) (fresh : m∉P) (inside : ∃ x∈P,x<k) :
    Completable (oneMarker k h (mixed 0 ((P++m::(P++later)).map (h+·)) 0)) := by
  obtain ⟨front,d,tail,eqn,small,above⟩ := last_below k P inside
  cases tail with
  | nil =>
    have cert := repeated_block_certificate h (k-1) m P later pos (by omega) fresh
      ⟨front,d,eqn,by omega⟩
    exact raise_left_margin (by simp) (show k-1+1≤k by omega) cert
  | cons n tail =>
    have absent : m∉front++[d] := by
      intro h
      apply fresh
      rw [eqn]
      rcases List.mem_append.mp h with h | h
      · simp [h]
      · simp [List.mem_singleton.mp h]
    have cert := new_separator_certificate h d n m front tail (P++later) pos
      (by have := above n (by simp); omega)
      (by intro x hx; have := above x (by simp [hx]); omega) absent
    have reorder : ((front++[d])++n::(tail++m::(P++later))) = P++m::(P++later) := by
      conv_rhs => lhs; rw [eqn]
      simp [List.append_assoc]
    rw [reorder] at cert
    exact raise_left_margin (by simp) (show d+1≤k by omega) cert

theorem pow_map (f : ℕ → ℕ) (xs : List ℕ) (j : ℕ) :
    (wordPow xs j).map f = wordPow (xs.map f) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [wordPow_succ,List.map_append,ih,wordPow_succ]

/-- All blocks between occurrences of the minimum, including the endpoint
blocks, are the same P. Every code in this family completes, for an arbitrary
number of separators and an arbitrary nonuniform block P. -/
theorem equal_minimum_blocks_completion (k h m : ℕ) (P : List ℕ) (j : ℕ)
    (least : ∀ x∈P,m<x) (code : NamedCode (oneMarker k h (mixed 0 (P++wordPow (m::P) (j+1)) 0))) :
    Completable (oneMarker k h (mixed 0 (P++wordPow (m::P) (j+1)) 0)) := by
  by_contra bad
  by_cases hz : h=0
  · subst h
    exact bad (left_marker_completion k _ code)
  by_cases kz : k=0
  · subst k
    exact bad (right_marker_completion h _ code)
  let gs := P++wordPow (m::P) (j+1)
  have low := one_marker_gaps bad
  have hm := low m (by rw [wordPow_succ']; simp)
  have inParts (w : ℕ) (hw : w∈gs) : w=m ∨ w∈P := by
    rcases List.mem_append.mp hw with first | rest
    · exact Or.inr first
    generalize j+1 = N at rest
    induction N with
    | zero => simp at rest
    | succ n ih =>
      rw [wordPow_succ,List.mem_append] at rest
      rcases rest with later | single
      · exact ih later
      · exact List.mem_cons.mp single
  by_cases small : m<k+h
  · by_cases inside : ∃ x∈P,x<k+h
    · let offsets := P.map (·-h)
      let M := m-h
      have base : offsets.map (h+·)=P := restore_offset h P (fun x hx => by have := least x hx; omega)
      have sep : h+M=m := Nat.add_sub_of_le (by omega)
      have missing : M∉offsets := by
        intro mem
        obtain ⟨x,hx,same⟩ := List.mem_map.mp mem
        have above := least x hx
        dsimp [M] at same
        omega
      have piece : ∃ z∈offsets,z<k := by
        obtain ⟨t,mt,lt⟩ := inside
        exact ⟨t-h,List.mem_map.mpr ⟨t,mt,rfl⟩,by omega⟩
      have done := initial_repeated_block_completion k h M offsets (wordPow (M::offsets) j)
        (by omega) (by dsimp [M]; omega) missing piece
      apply bad
      rw [wordPow_succ' (m::P) j]
      simpa only [List.map_append,List.map_cons,base,pow_map,sep,List.cons_append] using done
    · apply ((one_marker_ambiguity_iff k h gs).mpr _) code
      exact Or.inr ⟨P,m,j,hm,small,by push Not at inside; exact inside,rfl⟩
  · apply long_gap_ambiguity k h gs _ code
    intro w hw
    rcases inParts w hw with rfl | mem
    · omega
    · have := least w mem
      omega

/-- A unique minimum may occur anywhere in the gap list, with arbitrary
lengths and gap values on its two sides. -/
theorem unique_minimum_completion (k h m : ℕ) (front back : List ℕ)
    (left : ∀ x∈front,m<x) (right : ∀ x∈back,m<x)
    (code : NamedCode (oneMarker k h (mixed 0 (front++m::back) 0))) :
    Completable (oneMarker k h (mixed 0 (front++m::back) 0)) := by
  by_cases same : front=back
  · subst back
    simpa [wordPow_one] using equal_minimum_blocks_completion k h m front 0 left (by simpa using code)
  · exact unequal_blocks_completion k h m front back left right same code

/-- The residual family for Proposition 6 has repeated interior minima and
at least two different blocks between consecutive minima or at the ends. -/
def RepeatedInteriorConstruction : Prop :=
  ∀ k l m f t (middle : List ℕ), 0<k → 0<l →
    let gs := f::(middle++[t])
    (∀ x∈gs,max k l≤x) → (∀ x∈gs,m≤x) → m<f → m<t → m<k+l →
    2≤gs.count m → 4≤gs.length →
    (¬∃ P j, (∀ x∈P,m<x) ∧ gs=P++wordPow (m::P) (j+1)) →
    NamedCode (oneMarker k l (mixed 0 gs 0)) → Completable (oneMarker k l (mixed 0 gs 0))

theorem pure_power_iff_repeated_interior : PurePowerTheorem.{0} ↔ RepeatedInteriorConstruction := by
  constructor
  · intro all k l m f t mid pk pl gs lower least mf mt short copies _ _ code
    apply (pure_power_iff_one_marker.mp all) k l gs pk pl lower _ code
    exact ⟨m,List.count_pos_iff.mp (by omega),short⟩
  · intro restricted
    apply pure_power_iff_interior_minimum.mpr
    intro k l f t middle pk pl lower withMin code
    obtain ⟨m,mem,mf,mt,short,minimum⟩ := withMin
    let gs := f::(middle++[t])
    by_cases shortList : gs.length≤3
    · exact at_most_three_gaps k l gs shortList code
    by_cases uniform : ∃ P j, (∀ x∈P,m<x) ∧ gs=P++wordPow (m::P) (j+1)
    · obtain ⟨P,j,above,form⟩ := uniform
      change Completable (oneMarker k l (mixed 0 gs 0))
      rw [form]
      apply equal_minimum_blocks_completion k l m P j above
      exact form ▸ (show NamedCode (oneMarker k l (mixed 0 gs 0)) from code)
    by_cases repeated : 2≤gs.count m
    · exact restricted k l m f t middle pk pl lower minimum mf mt short repeated (show 4≤gs.length by omega) uniform code
    have inGs : m∈gs := by simp [gs,mem]
    obtain ⟨front,back,form⟩ := List.mem_iff_append.mp inGs
    have counts : front.count m=0 ∧ back.count m=0 := by
      rw [form,List.count_append,List.count_cons_self] at repeated
      omega
    have lf : ∀ x∈front,m<x := by
      intro x hx
      have le := minimum x (show x∈gs by rw [form]; simp [hx])
      have ne : x≠m := fun e => (List.count_eq_zero.mp counts.1) (e ▸ hx)
      omega
    have rt : ∀ x∈back,m<x := by
      intro x hx
      have le := minimum x (show x∈gs by rw [form]; simp [hx])
      have ne : x≠m := fun e => (List.count_eq_zero.mp counts.2) (e ▸ hx)
      omega
    change Completable (oneMarker k l (mixed 0 gs 0))
    rw [form]
    exact unique_minimum_completion k l m front back lf rt (form ▸ (show NamedCode (oneMarker k l (mixed 0 gs 0)) from code))

end ThreeWordCodes.BinaryGaps
