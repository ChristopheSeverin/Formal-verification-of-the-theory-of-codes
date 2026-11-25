module

public import ThreeWordCodes.FirstShortGap

/-! # A block of short gaps followed by a long gap

The first selected leaf may contain any positive number of short gaps. Each
proper suffix starts with at most d copies of the name A before a name C.
The literal target tail starts with more than d copies of a, so the only
comparable proper suffix is the empty word.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {I : Type*}

private def groups (A C : I) : List ℕ → Word I
  | [] => []
  | n::s => endC A C n ++ groups A C s

private def forest [DecidableEq I] (A C : I) (d : ℕ) (ps : List ℕ) : Finset (Word I) :=
  {[A], A::endC A C d, C::groups A C ps}

private theorem suffix_groups (A C : I) (d : ℕ) (ps : List ℕ) (ok : ∀ x∈ps, x≤d)
    (w : Word I) (suffix : w <:+ groups A C ps) :
    w=[] ∨ ∃ r≤d, ∃ rest, w=endC A C r ++ rest := by
  induction ps with
  | nil => exact Or.inl (by simpa [groups] using suffix)
  | cons x ps ih =>
    have after :=  ih (fun n hn => ok n (by simp [hn]))
    obtain ⟨l,eqn⟩ := suffix
    rcases List.append_eq_append_iff.mp eqn with ⟨r,word,split⟩ | ⟨r,_,word⟩
    · rcases endC_suffixes A C x r ⟨l,word.symm⟩ with nil | ⟨m,le,form⟩
      · apply after
        simp [nil,split]
      · exact Or.inr ⟨m,le.trans (ok x (by simp)),groups A C ps,form ▸ split⟩
    · exact after ⟨r,word.symm⟩

private theorem node_starts [DecidableEq I] (A C : I) (d : ℕ) (ps : List ℕ) (ok : ∀ x∈ps,x≤d)
    (w : Word I) (hw : w ∈ suffixNodes (forest A C d ps)) :
    w=[] ∨ ∃ r≤d, ∃ rest, w=endC A C r ++ rest := by
  rcases mem_suffixNodes.mp hw with nil | ⟨e,he,suf,ne⟩
  · exact Or.inl nil
  · simp only [forest,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inl (by simpa using (List.suffix_cons_iff.mp suf).resolve_left ne)
    · rcases endC_suffixes A C d w ((List.suffix_cons_iff.mp suf).resolve_left ne) with nil | ⟨r,le,eqn⟩
      · exact Or.inl nil
      · exact Or.inr ⟨r,le,[],by simpa using eqn⟩
    · exact suffix_groups A C d ps ok w ((List.suffix_cons_iff.mp suf).resolve_left ne)

private theorem run_size [DecidableEq I] (A C : I) (ne : A≠C) (m n : ℕ) (u v : Word I)
    (he : endC A C m ++ u = endC A C n ++ v) : m = n := by
  let mark (z : I) : Bool := decide (z=C)
  have maps (m : ℕ) (s : Word I) :
      (endC A C m ++ s).map mark = run m ++ b :: s.map mark := by
    simp [endC,mark,run,b,a,ne]
  have eqn := congrArg (List.map mark) he
  rw [maps,maps] at eqn
  simpa only [initial_b] using congrArg initial eqn

private theorem forest_free [DecidableEq I] (A C : I) (ne : A≠C) (d : ℕ) (ps : List ℕ)
    (ok : ∀ x∈ps,x≤d) (nonzero : ps≠[]) :
    ∀ w ∈ forest A C d ps, ∀ v ∈ forest A C d ps, w <:+ v → w=v := by
  intro w hw v hv suf
  by_contra different
  have shape := node_starts A C d ps ok w (mem_suffixNodes.mpr (Or.inr ⟨v,hv,suf,different⟩))
  simp only [forest,Finset.mem_insert,Finset.mem_singleton] at hw hv
  rcases hw with rfl | rfl | rfl
  · obtain nil | ⟨r,_,rest,eqn⟩ := shape
    · contradiction
    · have cmem : C ∈ endC A C r ++ rest := by simp [endC]
      rw [←eqn] at cmem
      exact ne (List.mem_singleton.mp cmem).symm
  · obtain nil | ⟨r,le,rest,eqn⟩ := shape
    · contradiction
    · have eqn' : endC A C (d+1) ++ [] = endC A C r ++ rest := by
        simpa only [endC,List.replicate_succ,List.cons_append,List.append_nil] using eqn
      have := run_size A C ne (d+1) r [] rest eqn'
      omega
  · have marked : 1 < (C::groups A C ps).count C := by
      cases ps with
      | nil => contradiction
      | cons n ps =>
        have elem : C∈groups A C (n::ps) := by simp [groups,endC]
        have := List.count_pos_iff.mpr elem
        simp; omega
    have bound := suf.sublist.count_le C
    rcases hv with rfl | rfl | rfl
    · apply (Nat.not_lt_of_ge (bound.trans (List.count_le_length (l:=[A]) (a:=C)))) marked
    · apply (Nat.not_lt_of_ge (bound.trans ?_)) marked
      simp [endC,List.count_replicate,ne]
    · exact different rfl

/-- If a nonempty initial block has gaps h+p with p≤d and the next gap
is h+n with n>d, the triple prescribed by the letter a, the word
a^(d+1) b a^h, and this gap list has a finite positive certificate. -/
theorem first_long_gap_certificate (h d n : ℕ) (ps later : List ℕ) (q : ℕ)
    (nonzero : ps≠[]) (small : ∀ v∈ps,v≤d) (large : d<n) :
    HasFiniteCertificate ({[a], mixed (d+1) [] h,
      mixed 0 (ps.map (h+·) ++ (h+n)::later) q} : Set (Word Bool)) := by
  let X : Finset (Word Bool) := {[a],b::run h}
  let I := internalNodes X
  have sub : X ⊆ leaves I := subset_leaves (inner_free h) (by simp [X])
  let A : ↥(leaves I) := ⟨[a],sub (by simp [X])⟩
  let C : ↥(leaves I) := ⟨b::run h,sub (by simp [X])⟩
  let phi := fun z : ↥(leaves I) => z.val
  have ne : A≠C := by
    intro eqn
    have he := congrArg Subtype.val eqn
    simp [A,C,a,b] at he
  let E := forest A C d ps
  let s := C::groups A C ps
  let t := run n ++ b::gapTail q later
  have nt : t≠[] := by simp [t]
  have power (m : ℕ) : spell phi (List.replicate m A) = run m := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (a :: ·) ih
  have coded (m : ℕ) : spell phi (endC A C m) = run m ++ b::run h := by
    simp [endC,power,phi,C]
  have apart (p : Word (↥(leaves I))) (node : p∈suffixNodes E) (nonempty : p≠[]) :
      ¬ Comparable t (spell phi p) := by
    obtain ⟨r,le,rest,rfl⟩ := (node_starts A C d ps small p node).resolve_left nonempty
    rw [spell_append,coded,List.append_assoc,List.cons_append]
    rintro (pr | pr)
    · exact (Nat.ne_of_gt (by omega : r<n)) (marked_prefix pr).1
    · exact (Nat.ne_of_lt (by omega : r<n)) (marked_prefix pr).1
  have sIn : s∈E := by simp [s,E,forest]
  have out := tree_extension_certificate I (internalNodes_closed X) E (by simp [E,forest])
    (forest_free A C ne d ps small nonzero) s sIn t nt (by
      rw [mem_codedSet]
      rintro ⟨w,hw,eqn⟩
      by_cases empty : w=[]
      · subst w; exact nt eqn.symm
      · exact apart w hw empty (Or.inl (by rw [←eqn])))
    (by
      intro w hw cp
      by_cases empty : w=[]
      · simpa [empty] using sIn
      · exact (apart w hw empty cp).elim)
  apply out.mono
  rintro w (rfl | rfl | rfl)
  · right
    refine ⟨[A],⟨by simp [E,forest],?_⟩,rfl⟩
    rintro ⟨p,_,eqn⟩
    exact ne (List.cons.inj eqn).1.symm
  · right
    refine ⟨A::endC A C d,⟨by simp [E,forest],?_⟩,?_⟩
    · rintro ⟨p,_,eqn⟩
      exact ne (List.cons.inj eqn).1.symm
    · change [a] ++ spell phi (endC A C d) = _
      rw [coded]
      rfl
  · left
    apply Set.mem_singleton_iff.mpr
    symm
    have rest (xs : List ℕ) : run h ++ (spell phi (groups A C xs) ++ t) =
        gapTail q (xs.map (h+·) ++ (h+n)::later) := by
      induction xs with
      | nil => simp [groups,t,gapTail,run_add,List.append_assoc]
      | cons x xs ih =>
        simp only [List.map_cons,List.cons_append,gapTail,groups,spell_append,coded,run_add,List.append_assoc]
        rw [ih]
    change (b::run h) ++ spell phi (groups A C ps) ++ t = b::gapTail q (ps.map (h+·) ++ (h+n)::later)
    simpa only [List.cons_append,List.append_assoc] using congrArg (b :: ·) (rest ps)

private theorem cut_at_rise (u : ℕ) (xs : List ℕ) (rise : ∃ t∈xs, u<t) :
    ∃ pre t post, xs=pre ++ t::post ∧ (∀ x∈pre, x≤u) ∧ u<t := by
  induction xs with
  | nil => simp at rise
  | cons v xs ih =>
    by_cases large : u<v
    · exact ⟨[],v,xs,rfl,by simp,large⟩
    · have later : ∃ t∈xs, u<t := by
        obtain ⟨t,mt,gt⟩ := rise
        exact ⟨t,(List.mem_cons.mp mt).resolve_left (fun h => large (h ▸ gt)),gt⟩
      obtain ⟨pre,t,post,eqn,bound,gt⟩ := ih later
      exact ⟨v::pre,t,post,congrArg (v :: ·) eqn,by simpa using And.intro (Nat.le_of_not_gt large) bound,gt⟩

/-- If the first gap is short and any later gap is longer, all intervening
smaller gaps can be included in the graft. The original left margin is
restored after the construction. -/
theorem short_first_before_larger (k h u : ℕ) (xs : List ℕ) (q : ℕ)
    (lower : ∀ t∈u::xs, h≤t) (short : u<k+h) (rise : ∃ t∈xs,u<t) :
    Completable (oneMarker k h (mixed 0 (u::xs) q)) := by
  obtain ⟨pre,t,post,eqn,less,large⟩ := cut_at_rise u xs rise
  subst xs
  let front := u::pre
  let ps := front.map (·-h)
  let d := u-h
  let n := t-h
  have low (x : ℕ) (mem : x∈front) : h≤x := lower x (by
    change x∈u::pre at mem
    simp only [List.mem_cons,List.mem_append] at mem ⊢
    tauto)
  have high (x : ℕ) (mem : x∈front) : x≤u := by
    rcases List.mem_cons.mp mem with rfl | hm
    · exact le_rfl
    · exact less x hm
  have ok (v : ℕ) (mem : v∈ps) : v≤d := by
    obtain ⟨x,mx,rfl⟩ := List.mem_map.mp mem
    exact Nat.sub_le_sub_right (high x mx) h
  have decoded : ps.map (h+·) = front := by
    change (front.map (·-h)).map (h+·) = front
    rw [List.map_map]
    calc front.map _ = front.map id := List.map_congr_left (fun x hx => Nat.add_sub_of_le (low x hx))
         _ = front := List.map_id ..
  have one := low u (by simp [front])
  have cert := first_long_gap_certificate h d n ps post q (by simp [ps,front]) ok
    (by dsimp [d,n]; omega)
  have et : h+n=t := by dsimp [n]; omega
  rw [decoded,et] at cert
  exact raise_left_margin (by simp) (show d+1≤k by dsimp [d]; omega) cert

/-- The symmetric completion when a short final gap has an earlier larger gap. -/
theorem short_last_after_larger (k h u : ℕ) (xs : List ℕ) (i : ℕ)
    (lower : ∀ t∈xs++[u], k≤t) (short : u<k+h) (rise : ∃ t∈xs,u<t) :
    Completable (oneMarker k h (mixed i (xs++[u]) 0)) := by
  have first := short_first_before_larger h k u xs.reverse i (by
    intro t ht
    apply lower
    simpa [or_comm] using ht) (by omega) (by simpa using rise)
  have eqn : (fun o => (oneMarker h k (mixed 0 (u::xs.reverse) i) o).reverse) =
      oneMarker k h (mixed i (xs++[u]) 0) := by
    funext o
    rcases o with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed]
  exact eqn ▸ first.reverse

private theorem singleton_power (n t : ℕ) : wordPow [t] n = List.replicate n t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ',ih,List.replicate_succ]; rfl

/-- In Proposition 6, if the smallest gap of W is the first one, every code
of the prescribed form has a positive finite completion. No assumptions on
the relative sizes of the two outside exponents are needed. -/
theorem minimum_first_gap_completion (k h u : ℕ) (xs : List ℕ) (minimum : ∀ t∈xs,u≤t)
    (code : NamedCode (oneMarker k h (mixed 0 (u::xs) 0))) :
    Completable (oneMarker k h (mixed 0 (u::xs) 0)) := by
  by_contra fail
  have lower := one_marker_gaps fail
  have bound := lower u (by simp)
  by_cases short : u<k+h
  · by_cases rise : ∃ t∈xs,u<t
    · exact fail (short_first_before_larger _ _ _ _ _ (fun x hx => (le_max_right ..).trans (lower x hx)) short rise)
    · push Not at rise
      apply ((one_marker_ambiguity_iff k h (u::xs)).mpr _) code
      apply Or.inr
      refine ⟨[],u,xs.length,bound,short,by simp,?_⟩
      rw [singleton_power]
      exact List.eq_replicate_iff.mpr ⟨rfl,fun t ht => by
        rcases List.mem_cons.mp ht with rfl | h
        · rfl
        · exact Nat.le_antisymm (rise _ h) (minimum _ h)⟩
  · apply long_gap_ambiguity k h (u::xs) _ code
    intro t mem
    rcases List.mem_cons.mp mem with rfl | h
    · omega
    · exact (Nat.le_of_not_gt short).trans (minimum _ h)

/-- The reversed endpoint-minimum case of Proposition 6. -/
theorem minimum_last_gap_completion (k h u : ℕ) (xs : List ℕ) (minimum : ∀ t∈xs,u≤t)
    (code : NamedCode (oneMarker k h (mixed 0 (xs++[u]) 0))) :
    Completable (oneMarker k h (mixed 0 (xs++[u]) 0)) := by
  let v := oneMarker k h (mixed 0 (xs++[u]) 0)
  have eqn : (fun x => (v x).reverse) = oneMarker h k (mixed 0 (u::xs.reverse) 0) := by
    funext x
    rcases x with _ | (_ | _) <;> simp [v,oneMarker,addToken,pair,reverse_mixed]
  have result := minimum_first_gap_completion h k u xs.reverse (by simpa using minimum) (eqn ▸ code.reverse)
  rw [←eqn] at result
  simpa only [List.reverse_reverse] using result.reverse

end ThreeWordCodes.BinaryGaps
