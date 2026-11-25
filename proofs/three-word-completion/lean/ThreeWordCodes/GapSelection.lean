module

public import ThreeWordCodes.SelectedGraft
public import ThreeWordCodes.FirstShortGap

/-! # The leaf-selection tests in gap coordinates

In the first application of Section 3 the two names are a and C = b a^h.
All gaps below are counts of free copies of a between successive C names.
The corresponding literal gaps are larger by h. The tests in
`gap_selection_certificate` involve only cuts in finite lists of integers.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private abbrev part (i : ℕ) (gs : List ℕ) := mixed i gs 0
private def coding (h : ℕ) := pair [a] (b :: run h)

private theorem spell_part (h i : ℕ) (gs : List ℕ) :
    spell (coding h) (part i gs) = mixed i (gs.map (h+·)) h := by
  have pure (j : ℕ) : spell (coding h) (run j) = run j := by
    induction j with
    | zero => rfl
    | succ j ih => exact congrArg (a :: ·) ih
  have next (ps : List ℕ) : run h ++ spell (coding h) (gapTail 0 ps) = gapTail h (ps.map (h+·)) := by
    induction ps with
    | nil => simp [gapTail,run]
    | cons p ps ih =>
      simp only [List.map_cons,gapTail,spell_append,pure,spell_cons,run_add,List.append_assoc]
      exact congrArg (run h ++ ·) (congrArg (run p ++ ·) (congrArg (b :: ·) ih))
  simp only [part,mixed,spell_append,pure,spell_cons]
  change run i ++ ((b :: run h) ++ _) = _
  simpa only [List.append_assoc,List.cons_append] using congrArg (run i ++ ·) (congrArg (b :: ·) (next gs))

/-- Group h forced copies of a with each marker. The last group contributes a terminal margin. -/
theorem spell_gap_names (h i : ℕ) (gs : List ℕ) :
    spell (pair [a] (b :: run h)) (mixed i gs 0) = mixed i (gs.map (h+·)) h := spell_part h i gs

private theorem ends_in_b (i : ℕ) (gs : List ℕ) : (part i gs).getLast? = some b := by
  rw [←List.head?_reverse,reverse_mixed]
  rfl

private theorem ends_in_a {h : ℕ} (pos : 0<h) (i : ℕ) (gs : List ℕ) :
    (mixed i gs h).getLast? = some a := by
  rw [←List.head?_reverse,reverse_mixed]
  cases h with
  | zero => omega
  | succ h => rfl

private theorem pure_or_marked_suffix {w : Word Bool} {i : ℕ} {gs : List ℕ} (pr : w <:+ part i gs) :
    w=[] ∨ ∃ r us, w=part r us := by
  by_cases emp : w=[]
  · exact Or.inl emp
  right
  have ending : w.getLast? = some b := by
    obtain ⟨pre,eqn⟩ := pr
    have e := ends_in_b i gs
    rw [←eqn,List.getLast?_append, List.getLast?_eq_getLast_of_ne_nil emp,Option.some_or] at e
    simpa only [List.getLast?_eq_getLast_of_ne_nil emp] using e
  rcases decompose w with ⟨j,rfl⟩ | ⟨r,us,q,rfl⟩
  · have bad := List.mem_of_getLast? ending
    simp [run,a,b] at bad
  · by_cases zero : q=0
    · exact ⟨r,us,zero ▸ rfl⟩
    · have other := ends_in_a (Nat.pos_of_ne_zero zero) r us
      rw [ending] at other
      contradiction

private theorem suffix_origin {i r : ℕ} {us gs : List ℕ} (pr : part r us <:+ part i gs) :
    (us = gs ∧ r ≤ i) ∨ ∃ pre z, gs=pre++z::us ∧ r≤z := by
  obtain ⟨w,eqn⟩ := pr
  rcases decompose w with ⟨n,rfl⟩ | ⟨j,pre,k,rfl⟩
  · have combined : mixed (n+r) us 0 = mixed i gs 0 := by
      simpa only [part,mixed,run_add,List.append_assoc] using eqn
    obtain ⟨a1,a2,_⟩ := mixed_injective combined
    exact Or.inl ⟨a2,by omega⟩
  · rw [show mixed j pre k ++ part r us = mixed j (pre ++ (k+r)::us) 0 from join_mixed ..] at eqn
    obtain ⟨_,a2,_⟩ := mixed_injective eqn
    exact Or.inr ⟨pre,k+r,a2.symm,by omega⟩

private def prescribedLeaves (d : ℕ) (cuts : List (List ℕ)) : List (Word Bool) :=
  [a] :: part (d+1) [] :: cuts.map (part 0)

/-- The marked suffixes of selected words either come from the one-marker
leaf or from a cut inside a selected gap list. -/
private theorem node_origin (d : ℕ) (cuts : List (List ℕ)) (w : Word Bool)
    (mem : w∈SelectedGraft.nodes (prescribedLeaves d cuts)) :
    w=[] ∨ ∃ r us, w=part r us ∧ ((us=[] ∧ r≤d) ∨
      ∃ p∈cuts, ∃ pre z, p=pre++z::us ∧ r≤z) := by
  rcases SelectedGraft.mem_nodes.mp mem with nil | ⟨v,hv,suf,proper⟩
  · exact Or.inl nil
  simp only [prescribedLeaves,List.mem_cons,List.mem_map] at hv
  rcases hv with rfl | rfl | ⟨p,hp,rfl⟩
  · exact Or.inl (by simpa using (List.suffix_cons_iff.mp suf).resolve_left proper)
  · rcases pure_or_marked_suffix suf with nil | ⟨r,us,rfl⟩
    · exact Or.inl nil
    rcases suffix_origin suf with ⟨rfl,bound⟩ | ⟨pre,z,eqn,_⟩
    · refine Or.inr ⟨r,[],rfl,Or.inl ⟨rfl,?_⟩⟩
      have nz : r≠d+1 := fun e => proper (congrArg (fun i => part i []) e)
      omega
    · simp at eqn
  · rcases pure_or_marked_suffix suf with nil | ⟨r,us,rfl⟩
    · exact Or.inl nil
    rcases suffix_origin suf with ⟨he,bound⟩ | hx
    · have rz : r=0 := by omega
      exact (proper (by rw [he,rz])).elim
    · exact Or.inr ⟨r,us,rfl,Or.inr ⟨p,hp,hx⟩⟩

private theorem ends_short {d : ℕ} {cuts : List (List ℕ)}
    (last : ∀ p∈cuts, ∃ pre z, p=pre++[z] ∧ z≤d)
    {p pre : List ℕ} {z : ℕ} (hp : p∈cuts) (eqn : p=pre++[z]) : z≤d := by
  obtain ⟨other,v,ev,le⟩ := last p hp
  have same := congrArg List.getLast? (eqn.symm.trans ev)
  have zv : z = v := by simpa using same
  exact zv ▸ le

private theorem leaves_free (d : ℕ) (cuts : List (List ℕ))
    (last : ∀ p∈cuts, ∃ pre z, p=pre++[z] ∧ z≤d)
    (antichain : ∀ p∈cuts, ∀ q∈cuts, p <:+ q → p=q) :
    ∀ x∈prescribedLeaves d cuts, ∀ y∈prescribedLeaves d cuts, x <:+ y → x=y := by
  intro x hx y hy suf
  by_contra ne
  have atNode := node_origin d cuts x (SelectedGraft.mem_nodes.mpr (Or.inr ⟨y,hy,suf,ne⟩))
  simp only [prescribedLeaves,List.mem_cons,List.mem_map] at hx hy
  rcases hx with rfl | rfl | ⟨p,hp,rfl⟩
  · obtain nil | ⟨r,us,eqn,_⟩ := atNode
    · contradiction
    · have bad := congrArg List.getLast? eqn
      rw [ends_in_b] at bad
      contradiction
  · obtain nil | ⟨r,us,eqn,origin⟩ := atNode
    · have := congrArg (List.count b) nil
      simp [part,mixed_count] at this
    obtain ⟨he,hu,_⟩ := mixed_injective eqn
    rcases origin with ⟨_,le⟩ | ⟨p,hp,pre,z,hp',le⟩
    · omega
    · have hz := ends_short last hp (hu ▸ hp')
      omega
  · rcases hy with rfl | rfl | ⟨q,hq,rfl⟩
    · have := suf.sublist.count_le b
      simp [part,mixed_count,a,b] at this
    · obtain ⟨pre,z,rfl,_⟩ := last p hp
      have := suf.sublist.count_le b
      simp [part,mixed_count] at this
    · apply ne
      apply congrArg (part 0)
      apply antichain p hp q hq
      rcases suffix_origin suf with ⟨eqn,_⟩ | ⟨pre,z,eqn,_⟩
      · rw [eqn]
      · exact ⟨pre++[z],by simpa using eqn.symm⟩

/-- Interpret the same finite family of suffix leaves on any prefix code with
two named tokens. Only the comparison with the literal tail depends on the
choice of the two token images. -/
theorem selected_gap_certificate {A : Type*} [Fintype A] [Nonempty A]
    (v : Bool → Word A) (hi : Function.Injective v) (nz : ∀ i,v i≠[])
    (pf : InformationTheory.IsPrefixFree (Set.range v)) (d : ℕ) (cuts : List (List ℕ))
    (cut : List ℕ) (t : Word A) (chosen : cut∈cuts) (nt : t≠[])
    (last : ∀ p∈cuts, ∃ pre z, p=pre++[z] ∧ z≤d)
    (antichain : ∀ p∈cuts, ∀ q∈cuts, p <:+ q → p=q)
    (matchNode : ∀ r us, (us=[] ∧ r≤d ∨ ∃ p∈cuts, ∃ pre z, p=pre++z::us ∧ r≤z) →
      spell v (mixed r us 0)≠t ∧ (Comparable t (spell v (mixed r us 0)) → cut++r::us∈cuts)) :
    HasFiniteCertificate ({v a,spell v (mixed (d+1) [] 0),spell v (mixed 0 cut 0)++t} : Set (Word A)) := by
  classical
  let E := prescribedLeaves d cuts
  let u := part 0 cut
  have leaf {ls : List ℕ} (mem : ls∈cuts) : part 0 ls∈E := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ls,mem,rfl⟩))
  have ok : SelectedGraft.Valid v E u t := by
    refine ⟨by simp [E,prescribedLeaves,part,mixed],leaf chosen,nt,leaves_free d cuts last antichain,?_⟩
    intro q hq
    rcases node_origin d cuts q hq with rfl | ⟨r,us,rfl,origin⟩
    · exact ⟨Ne.symm nt,fun _ => by simpa [u] using leaf chosen⟩
    obtain ⟨ne,hit⟩ := matchNode r us origin
    refine ⟨ne,fun compare => ?_⟩
    have concat : u++part r us=part 0 (cut++r::us) := by
      simpa [u,part] using join_mixed cut us 0 0 r 0
    exact concat.symm ▸ leaf (hit compare)
  apply (SelectedGraft.certificate v hi nz pf E u t ok).mono
  rintro _ (rfl | rfl | rfl)
  · right
    exact ⟨[a],⟨by simp [E,prescribedLeaves],by rintro ⟨w,e⟩; exact Bool.noConfusion (List.cons.inj e).1⟩,by simp⟩
  · right
    exact ⟨part (d+1) [],⟨by simp [E,prescribedLeaves],by rintro ⟨w,e⟩; exact Bool.noConfusion (List.cons.inj e).1⟩,rfl⟩
  · exact Or.inl rfl

/-- Successful choices of cut prefixes give a finite certificate. The input
list of name-gaps is `cut ++ n :: rest`. For every matching proper suffix,
the hypothesis supplies the required extended leaf. -/
theorem gap_selection_certificate (h d : ℕ) (cuts : List (List ℕ)) (cut : List ℕ)
    (n : ℕ) (rest : List ℕ) (pos : 0<h) (chosen : cut∈cuts)
    (last : ∀ p∈cuts, ∃ pre z, p=pre++[z] ∧ z≤d)
    (antichain : ∀ p∈cuts, ∀ q∈cuts, p <:+ q → p=q)
    (one : n≤d → cut++[n]∈cuts)
    (close : ∀ p∈cuts, ∀ pre z post, p=pre++z::post → n≤z →
      (post <+: rest ∨ rest <+: post) → cut++n::post∈cuts) :
    HasFiniteCertificate ({[a],mixed (d+1) [] h,mixed 0 ((cut++n::rest).map (h+·)) 0} :
      Set (Word Bool)) := by
  let v := coding h
  let E := prescribedLeaves d cuts
  let s := part 0 cut
  let t := mixed n (rest.map (h+·)) 0
  have isLeaf {ps : List ℕ} (hp : ps ∈ cuts) : part 0 ps ∈ E :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ps,hp,rfl⟩))
  have sMem : s∈E := isLeaf chosen
  have nonzero (i : ℕ) (gs : List ℕ) : mixed i gs 0 ≠ [] := by simp [mixed]
  have ok : SelectedGraft.Valid v E s t := by
    refine ⟨?_,sMem,nonzero n (rest.map (h+·)),leaves_free d cuts last antichain,?_⟩
    · simp [E,prescribedLeaves,part,mixed]
    intro w hw
    rcases node_origin d cuts w hw with rfl | ⟨r,us,rfl,origin⟩
    · exact ⟨Ne.symm (nonzero n (rest.map (h+·))),fun _ => by simpa using sMem⟩
    have spelling : spell v (part r us) = mixed r (us.map (h+·)) h := spell_part ..
    rw [spelling]
    constructor
    · intro eqn
      exact (Nat.ne_of_gt pos) (mixed_injective eqn).2.2
    · intro cmp
      have matchGap {a₀ b₀ : ℕ} {xs ys : List ℕ} {l q : ℕ}
          (pr : mixed a₀ (xs.map (h+·)) l <+: mixed b₀ (ys.map (h+·)) q) :
          a₀=b₀ ∧ xs <+: ys := by
        obtain ⟨start,sub⟩ := marked_prefix pr
        exact ⟨start,(List.prefix_map_iff_of_injective (f:=fun z : ℕ => h+z)
          (fun _ _ e => Nat.add_left_cancel e)).mp (tail_prefix sub).1⟩
      have fields : r=n ∧ (us <+: rest ∨ rest <+: us) := by
        rcases cmp with cp | cp
        · obtain ⟨eqn,fit⟩ := matchGap cp
          exact ⟨eqn.symm,Or.inr fit⟩
        · obtain ⟨eqn,fit⟩ := matchGap cp
          exact ⟨eqn,Or.inl fit⟩
      obtain ⟨rfl,fit⟩ := fields
      have add : cut++r::us∈cuts := by
        rcases origin with ⟨rfl,le⟩ | ⟨p,hp,pre,z,eqn,le⟩
        · exact one le
        · exact close p hp pre z us eqn le fit
      have eqn : s ++ part r us = part 0 (cut++r::us) := by simpa [s,part] using join_mixed cut us 0 0 r 0
      rw [eqn]
      exact isLeaf add
  have prefixFree : InformationTheory.IsPrefixFree (Set.range v) := by
    have eqn : Set.range v = ({[a], b :: run h} : Finset (Word Bool)) := by
      ext x
      simp only [Set.mem_range,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨(_ | _),rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨false,rfl⟩
        · exact ⟨true,rfl⟩
    rw [eqn]
    exact inner_free h
  have out := SelectedGraft.certificate v (by rintro (_ | _) (_ | _) e <;> simp_all [v,coding,pair,a,b])
    (by rintro (_ | _) <;> simp [v,coding,pair]) prefixFree E s t ok
  apply out.mono
  rintro w (rfl | rfl | rfl)
  · right
    refine ⟨[a],⟨by simp [E,prescribedLeaves],?_⟩,rfl⟩
    rintro ⟨q,eqn⟩
    exact Bool.noConfusion (List.cons.inj eqn).1
  · right
    refine ⟨part (d+1) [],⟨by simp [E,prescribedLeaves],?_⟩,spell_part ..⟩
    rintro ⟨q,eqn⟩
    exact Bool.noConfusion (List.cons.inj eqn).1
  · left
    have target : spell v s ++ t = mixed 0 ((cut++n::rest).map (h+·)) 0 := by
      rw [show spell v s = mixed 0 (cut.map (h+·)) h from spell_part ..]
      simpa [t] using join_mixed (cut.map (h+·)) (rest.map (h+·)) 0 h n 0
    exact target.symm

end ThreeWordCodes.BinaryGaps
