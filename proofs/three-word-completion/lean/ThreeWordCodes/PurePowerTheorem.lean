module

public import ThreeWordCodes.RunLifting

/-! # Positive finite completion for an entry that is a power of a letter -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private theorem joined_run (m : ℕ) (F : List ℕ) (r : ℕ) :
    joinBlocks m (List.replicate (r+1) F) = blockPattern m F r := by
  induction r with
  | zero => simp [joinBlocks,blockPattern]
  | succ r ih =>
    rw [List.replicate_succ]
    change [m].intercalate (F::List.replicate (r+1) F) = _
    rw [List.intercalate_cons_of_ne_nil (by simp),show [m].intercalate (List.replicate (r+1) F)=_ from ih]
    simp [blockPattern,wordPow_succ',List.append_assoc]

theorem run_is_prefix (m : ℕ) (F : List ℕ) (r : ℕ) (ts : List (List ℕ)) :
    blockPattern m F r <+: joinBlocks m (List.replicate (r+1) F ++ ts) := by
  cases ts with
  | nil => simp [joined_run]
  | cons t ts =>
    rw [cut_blocks _ _ _ (by simp),separated_run,List.append_assoc]
    exact ⟨_,rfl⟩

/-- The first sufficiently long return gives a cut and a distinguished run.
The same layout is used in both applications of the graft. -/
theorem return_layout (m : ℕ) (F : List ℕ) (r : ℕ) (rs : List (List ℕ × ℕ))
    (valid : ∀ e∈rs,e.1≠F) (returns : ∃ e∈rs,r+1≤e.2) :
    let bs := List.replicate (r+1) F++BlockRuns.after F rs
    ∃ ps D next, let history := List.replicate (r+1) F++BlockRuns.after F ps
      D≠F ∧ (∀ e∈ps,e.1≠F ∧ e.2<r+1) ∧ (∀ B∈history++[D,F],B∈bs) ∧
      joinBlocks m bs=(separated m history++D)++m::(blockPattern m F r++next) := by
  obtain ⟨ps,D,j,later,whereRun,ne,large,bounds⟩ := BlockRuns.first_return rs (r+1) valid returns
  let history := List.replicate (r+1) F ++ BlockRuns.after F ps
  let rest := List.replicate (j-(r+1)) F ++ BlockRuns.after F later
  let bs := List.replicate (r+1) F ++ BlockRuns.after F rs
  have split : bs=history++D::(List.replicate (r+1) F++rest) := by
    have count : List.replicate j F=List.replicate (r+1) F++List.replicate (j-(r+1)) F := by
      rw [←List.replicate_add,Nat.add_sub_of_le large]
    simp [bs,history,rest,whereRun,count,List.append_assoc]
    rw [List.replicate_add,List.append_assoc]
  have inB (B : List ℕ) (mem : B∈history++[D,F]) : B∈bs := by
    rw [split]
    rcases List.mem_append.mp mem with old | new
    · exact List.mem_append_left _ old
    · rcases List.mem_cons.mp new with rfl | hF
      · simp
      · obtain rfl := List.mem_singleton.mp hF
        simp
  obtain ⟨continuation,part⟩ := run_is_prefix m F r rest
  have form : joinBlocks m bs=(separated m history++D)++m::(blockPattern m F r++continuation) := by
    rw [split,cut_blocks _ _ _ (by simp)]
    change _ ++ [m].intercalate (D::(List.replicate (r+1) F++rest)) = _
    rw [List.intercalate_cons_of_ne_nil (by simp),show [m].intercalate (List.replicate (r+1) F++rest)=_ from part.symm]
    simp [List.append_assoc]
  exact ⟨ps,D,continuation,ne,bounds,inB,form⟩

private theorem return_completes (k h m : ℕ) (F : List ℕ) (r : ℕ) (rs : List (List ℕ × ℕ))
    (pos : 0<h) (low : h≤m) (short : m<k+h) (nonempty : F≠[])
    (valid : ∀ e∈rs,e.1≠F) (returns : ∃ e∈rs,r+1≤e.2)
    (long : ∀ B∈List.replicate (r+1) F++BlockRuns.after F rs,∀ x∈B,m<x)
    (recognize : RecognizesBlock F (List.replicate (r+1) F++BlockRuns.after F rs)) :
    Completable (oneMarker k h (mixed 0 (joinBlocks m (List.replicate (r+1) F++BlockRuns.after F rs)) 0)) := by
  let bs := List.replicate (r+1) F++BlockRuns.after F rs
  obtain ⟨ps,D,continuation,ne,bounds,inB,form⟩ := return_layout m F r rs valid returns
  have after (x : ℕ) (hx : x∈continuation) : h≤x := low.trans (blocks_lower m bs long x
    (by rw [form]; simp [hx]))
  have out := maximum_run_completion k h m F D r ps continuation pos low short ne nonempty bounds after
    (fun B hb => long B (inB B hb)) (fun B hb => recognize B (inB B hb))
  change Completable (oneMarker k h (mixed 0 (joinBlocks m bs) 0))
  rw [form]
  exact out

/-- If this orientation failed to complete, its initial run of maximum blocks
could occur only at position zero. -/
private theorem obstruction_run {k h m : ℕ} {F : List ℕ} {other : List (List ℕ)}
    (pos : 0<h) (low : h≤m) (short : m<k+h) (nonempty : F≠[])
    (long : ∀ B∈F::other,∀ x∈B,m<x) (recognize : RecognizesBlock F (F::other))
    (fail : ¬ Completable (oneMarker k h (mixed 0 (joinBlocks m (F::other)) 0))) :
    ∃ n, List.replicate n F <+: F::other ∧
      ∀ pre tail, F::other=pre++(List.replicate n F++tail) → pre=[] := by
  obtain ⟨n,rs,eqn,valid⟩ := BlockRuns.decompose F (F::other)
  have nonzero : n≠0 := by
    rintro rfl
    cases rs with
    | nil => simp at eqn
    | cons e rs =>
      rcases e with ⟨x,j⟩
      exact valid (x,j) (by simp) ((List.cons.inj eqn).1.symm)
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have small : ∀ e∈rs,e.1≠F ∧ e.2<r+1 := by
    intro e he
    refine ⟨valid e he,?_⟩
    by_contra! big
    apply fail
    rw [eqn]
    exact return_completes k h m F r rs pos low short nonempty valid ⟨e,he,big⟩ (eqn ▸ long) (eqn ▸ recognize)
  refine ⟨r+1,⟨_,eqn.symm⟩,?_⟩
  intro pre tail found
  exact BlockRuns.initial_run (Nat.succ_pos _) rs small pre tail (eqn.symm.trans found)

theorem incompatible_runs (F : List ℕ) (bs : List (List ℕ)) (n q : ℕ)
    (order : n≤q) (last : List.replicate q F.reverse <+: bs.reverse.map List.reverse)
    (onlyStart : ∀ pre tail,bs=pre++(List.replicate n F++tail) → pre=[])
    (different : ∃ B∈bs,B≠F) : False := by
  have sub : List.replicate n F.reverse <+: List.replicate q F.reverse := by
    exact ⟨List.replicate (q-n) _,by rw [←List.replicate_add,Nat.add_sub_of_le order]⟩
  have reversed := ((sub.trans last).reverse).map List.reverse
  have suf : List.replicate n F <:+ bs := by
    simpa [List.map_reverse,List.map_map,Function.comp_def] using reversed
  obtain ⟨pre,endEq⟩ := suf
  have empty := onlyStart pre [] (by simpa using endEq.symm)
  obtain ⟨B,mem,ne⟩ := different
  rw [←endEq,empty,List.nil_append] at mem
  exact ne (List.eq_of_mem_replicate mem)

theorem common_maximum_construction : CommonMaximumConstruction := by
  intro k h m F mid pk ph low short nz long different light gs code
  by_contra fail
  let bs := F::(mid++[F])
  let rev := F.reverse::(mid.reverse.map List.reverse++[F.reverse])
  have oriented : bs.reverse.map List.reverse=rev := by simp [bs,rev]
  have back : rev.reverse.map List.reverse=bs := by
    simp [bs,rev,List.map_reverse,List.map_map]
  have memb {B : List ℕ} : B∈rev ↔ B.reverse∈bs := by
    rw [←oriented,List.mem_map]
    constructor
    · rintro ⟨P,hP,rfl⟩; simpa using hP
    · intro hB; exact ⟨B.reverse,by simpa using hB,List.reverse_reverse _⟩
  have all (B : List ℕ) (hb : B∈bs) : ∀ x∈B,m<x := by
    apply long B
    simpa [bs,or_assoc,or_left_comm,or_comm] using hb
  have weight (B : List ℕ) (hb : B∈bs) : blockWeight B≤blockWeight F := by
    by_cases same : B=F
    · rw [same]
    · exact (light B (by simpa [bs,same] using hb) same).le
  have one : ¬ Completable (oneMarker k h (mixed 0 (joinBlocks m bs) 0)) := fail
  have two : ¬ Completable (oneMarker h k (mixed 0 (joinBlocks m rev) 0)) := by
    intro done
    have eqn : (fun i => (oneMarker h k (mixed 0 (joinBlocks m rev) 0) i).reverse) =
        oneMarker k h (mixed 0 (joinBlocks m bs) 0) := by
      have vrev : (joinBlocks m rev).reverse=joinBlocks m bs := by rw [reverse_blocks,back]
      funext i
      rcases i with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed,vrev]
    exact one (eqn ▸ done.reverse)
  obtain ⟨n,prN,rootN⟩ := obstruction_run ph (by omega) short nz all (recognizes_of_weight weight) one
  have rLong (B : List ℕ) (hb : B∈rev) (x : ℕ) (hx : x∈B) :=
    all B.reverse (memb.mp hb) x (by simpa using hx)
  have rWeight (B : List ℕ) (hb : B∈rev) : blockWeight B≤blockWeight F.reverse := by
    simpa using weight B.reverse (memb.mp hb)
  obtain ⟨q,prQ,rootQ⟩ := obstruction_run pk (by omega) (by omega) (F:=F.reverse) (by simpa using nz)
    rLong (recognizes_of_weight rWeight) two
  obtain ⟨B,hb,bne⟩ := different
  have member : B∈bs := by simp [bs,hb]
  rcases le_total n q with dir | dir
  · exact incompatible_runs F bs n q dir (oriented ▸ prQ) rootN ⟨B,member,bne⟩
  · have prev : List.replicate n F.reverse.reverse <+: rev.reverse.map List.reverse := by
      rw [back,List.reverse_reverse]
      exact prN
    exact incompatible_runs F.reverse rev q n dir prev rootQ
      ⟨B.reverse,memb.mpr (by simpa using member),by simpa using bne⟩

/-- Proposition 6. Every three-word code on a finite alphabet with an entry
that is a power of a letter admits a finite positive completion. -/
theorem pure_power_completion.{u} : PurePowerTheorem.{u} := by
  apply one_marker_suffices
  exact pure_power_iff_one_marker.mp (pure_power_iff_common_maximum.mpr common_maximum_construction)

/-- The entire first application of the leaf selection in Section 3. -/
theorem one_marker_construction : OneMarkerConstruction :=
  pure_power_iff_one_marker.mp pure_power_completion

end ThreeWordCodes.BinaryGaps
