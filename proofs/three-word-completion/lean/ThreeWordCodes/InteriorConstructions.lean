module

public import ThreeWordCodes.GapSelection
public import ThreeWordCodes.InteriorGaps

/-! # Interior cuts with one or two selected prefixes -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

/-- Graft immediately after a short gap if the next gap exceeds every gap
seen so far. The part preceding the short gap may be arbitrarily long. -/
theorem record_gap_certificate (h d n : ℕ) (before after : List ℕ)
    (pos : 0 < h) (rise : d < n) (record : ∀ x∈before, x<n) :
    HasFiniteCertificate ({[a],mixed (d+1) [] h,
      mixed 0 (((before++[d])++n::after).map (h+·)) 0} : Set (Word Bool)) := by
  let cut := before++[d]
  apply gap_selection_certificate h d [cut] cut n after pos (by simp)
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨before,d,rfl,le_rfl⟩
  · simp
  · omega
  · intro p hp pre z post eqn le _
    obtain rfl := List.mem_singleton.mp hp
    have mem : z∈cut := eqn ▸ (by simp)
    rcases List.mem_append.mp mem with hb | hd
    · have := record z hb
      omega
    · obtain rfl := List.mem_singleton.mp hd
      omega

/-- A smaller middle gap between equal short gaps. Two leaves are selected;
one pays for the comparable suffix of the other. Later gaps are arbitrary. -/
theorem repeated_endpoint_certificate (h d e : ℕ) (later : List ℕ) (pos : 0<h) (small : e<d) :
    HasFiniteCertificate ({[a],mixed (d+1) [] h,
      mixed 0 ((d::e::d::later).map (h+·)) 0} : Set (Word Bool)) := by
  change HasFiniteCertificate ({[a],mixed (d+1) [] h,
    mixed 0 (([d]++e::d::later).map (h+·)) 0} : Set (Word Bool))
  let cuts : List (List ℕ) := [[d],[d,e]]
  apply gap_selection_certificate h d cuts [d] e (d::later) pos (by simp [cuts])
  · intro p hp
    simp [cuts] at hp
    rcases hp with rfl | rfl
    · exact ⟨[],d,rfl,le_rfl⟩
    · exact ⟨[d],e,rfl,small.le⟩
  · intro p hp q hq suf
    simp [cuts] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> try rfl
    · obtain ⟨xs,eqn⟩ := suf
      have hz := congrArg List.getLast? eqn
      simp at hz
      omega
    · have := suf.length_le
      simp at this
  · simp [cuts]
  · intro p hp pre z post eqn _ fit
    simp [cuts] at hp
    have shorter (hn : post=[e]) : False := by
      subst post
      rcases fit with pr | pr
      · obtain ⟨tail,eqn⟩ := pr
        have := (List.cons.inj eqn).1
        omega
      · obtain ⟨tail,eqn⟩ := pr
        have := (List.cons.inj eqn).1
        omega
    suffices post=[] by simp [this,cuts]
    rcases hp with rfl | rfl
    · have lens := congrArg List.length eqn
      simp at lens
      exact List.length_eq_zero_iff.mp (by omega)
    · cases pre with
      | nil =>
        have sub := (List.cons.inj eqn).2
        exact (shorter sub.symm).elim
      | cons w pre =>
        have lens := congrArg List.length eqn
        simp at lens
        exact List.length_eq_zero_iff.mp (by omega)

private theorem ascending_endpoints (k h f m t : ℕ) (pos : 0<h)
    (lower : h≤f ∧ h≤m ∧ h≤t) (short : m<k+h) (mt : m<t) (ft : f<t) :
    Completable (oneMarker k h (mixed 0 [f,m,t] 0)) := by
  have one := record_gap_certificate h (m-h) (t-h) [f-h] [] pos (by omega)
    (by intro x hx; obtain rfl := List.mem_singleton.mp hx; omega)
  have ef : h+(f-h)=f := by omega
  have em : h+(m-h)=m := by omega
  have et : h+(t-h)=t := by omega
  simp only [List.cons_append,List.nil_append,List.map_cons,List.map_nil,ef,em,et] at one
  exact raise_left_margin (by simp) (show m-h+1 ≤ k by omega) one

/-- All one-marker inputs with three internal gaps (four copies of b)
have a positive finite completion whenever the three names form a code. -/
theorem three_gap_completion (k h f m t : ℕ) (code : NamedCode (oneMarker k h (mixed 0 [f,m,t] 0))) :
    Completable (oneMarker k h (mixed 0 [f,m,t] 0)) := by
  by_contra fail
  by_cases hz : h=0
  · subst h
    exact fail (left_marker_completion k _ code)
  by_cases kz : k=0
  · subst k
    exact fail (right_marker_completion h _ code)
  have low := one_marker_gaps fail
  have lf := low f (by simp)
  have lm := low m (by simp)
  have lt := low t (by simp)
  by_cases left : f≤m ∧ f≤t
  · exact fail (minimum_first_gap_completion k h f [m,t] (by simpa using left) code)
  by_cases right : t≤f ∧ t≤m
  · exact fail (minimum_last_gap_completion k h t [f,m] (by simpa using right) code)
  have mf : m<f := by omega
  have mt : m<t := by omega
  by_cases short : m<k+h
  · rcases lt_trichotomy f t with higher | rfl | lower
    · exact fail (ascending_endpoints k h f m t (by omega) (by omega) short mt higher)
    · by_cases high : k+h ≤ f
      · apply ((one_marker_ambiguity_iff k h [f,m,f]).mpr _) code
        exact Or.inr ⟨[f],m,0,lm,short,by simpa using high,rfl⟩
      have d := repeated_endpoint_certificate h (f-h) (m-h) [] (by omega) (by omega)
      have ef : h+(f-h)=f := by omega
      have em : h+(m-h)=m := by omega
      simp only [List.map_cons,List.map_nil,ef,em] at d
      exact fail (raise_left_margin (by simp) (show f-h+1 ≤ k by omega) d)
    · have rev := ascending_endpoints h k t m f (by omega) (by omega) (by omega) mf lower
      have eqn : (fun i => (oneMarker h k (mixed 0 [t,m,f] 0) i).reverse) =
          oneMarker k h (mixed 0 [f,m,t] 0) := by
        funext i
        rcases i with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed]
      exact fail (eqn ▸ rev.reverse)
  · exact long_gap_ambiguity k h [f,m,t] (by simp; omega) code

/-- The previous result includes all shorter gap lists. -/
theorem at_most_three_gaps (k h : ℕ) (gs : List ℕ) (bound : gs.length ≤ 3)
    (code : NamedCode (oneMarker k h (mixed 0 gs 0))) :
    Completable (oneMarker k h (mixed 0 gs 0)) := by
  cases gs with
  | nil => exact (long_gap_ambiguity k h [] (by simp) code).elim
  | cons f rest =>
    cases rest with
    | nil => exact minimum_first_gap_completion k h f [] (by simp) code
    | cons m rest =>
      cases rest with
      | nil =>
        rcases le_total f m with first | last
        · exact minimum_first_gap_completion k h f [m] (by simpa using first) code
        · exact minimum_last_gap_completion k h m [f] (by simpa using last) code
      | cons t tail =>
        have empty : tail=[] := List.length_eq_zero_iff.mp (by simp at bound; omega)
        subst tail
        exact three_gap_completion k h f m t code

end ThreeWordCodes.BinaryGaps
