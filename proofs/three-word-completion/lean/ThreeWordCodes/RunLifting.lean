module

public import ThreeWordCodes.MaximumRunGraft

/-! # Reading a maximum-block graft on the original binary alphabet -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private theorem map_separated (f : ℕ → ℕ) (m : ℕ) (blocks : List (List ℕ)) :
    (separated m blocks).map f = separated (f m) (blocks.map (List.map f)) := by
  induction blocks with
  | nil => rfl
  | cons B bs ih => simp [ih]

private theorem map_pattern (f : ℕ → ℕ) (m : ℕ) (F : List ℕ) (r : ℕ) :
    (blockPattern m F r).map f = blockPattern (f m) (F.map f) r := by
  induction r with
  | zero => simp [blockPattern]
  | succ r ih =>
    have form (m) (F : List ℕ) : blockPattern m F (r+1)=F++m::blockPattern m F r := by
      simp [blockPattern,wordPow_succ']
    rw [form,form,List.map_append,List.map_cons,ih]

private theorem map_runs {A B : Type*} (f : A → B) (F : A) (ps : List (A × ℕ)) :
    (BlockRuns.after F ps).map f = BlockRuns.after (f F) (ps.map (fun e => (f e.1,e.2))) := by
  induction ps with
  | nil => rfl
  | cons e ps ih => rcases e with ⟨x,k⟩; simp [ih]

/-- Undo the offset h after choosing cuts. Every gap of a long block is
strictly greater than m. The condition recognizing maximum blocks is on
the original lists, so the same weights may be used after reversal. -/
theorem maximum_run_completion (k h m : ℕ) (F D : List ℕ) (r : ℕ) (ps : List (List ℕ × ℕ))
    (later : List ℕ) (pos : 0<h) (low : h≤m) (short : m<k+h) (different : D≠F) (nonempty : F≠[])
    (bounded : ∀ e∈ps,e.1≠F ∧ e.2<r+1) (after : ∀ x∈later,h≤x)
    (long : ∀ B∈(List.replicate (r+1) F ++ BlockRuns.after F ps) ++ [D,F],∀ x∈B,m<x)
    (recognize : RecognizesBlock F ((List.replicate (r+1) F ++ BlockRuns.after F ps) ++ [D,F])) :
    let history := List.replicate (r+1) F ++ BlockRuns.after F ps
    Completable (oneMarker k h (mixed 0 (separated m history ++ D++m::(blockPattern m F r++later)) 0)) := by
  let norm (B : List ℕ) := B.map (·-h)
  let history := List.replicate (r+1) F ++ BlockRuns.after F ps
  let all := history++[D,F]
  let runs := ps.map (fun e => (norm e.1,e.2))
  let normHist := List.replicate (r+1) (norm F) ++ BlockRuns.after (norm F) runs
  have normed : history.map norm = normHist := by simp [history,normHist,runs,map_runs]
  have restored (B : List ℕ) (inc : B∈all) : (norm B).map (h+·)=B :=
    restore_offset h B (fun x hx => low.trans (long B inc x hx).le)
  have fIn : F∈all := by simp [all]
  have dIn : D∈all := by simp [all]
  have fh := restored F fIn
  have dh := restored D dIn
  have restorHist : normHist.map (List.map (h+·))=history := by
    rw [←normed,List.map_map]
    calc history.map _ = history.map id := List.map_congr_left (fun B hB => restored B (List.mem_append_left _ hB))
         _ = history := List.map_id ..
  have mn : h+(m-h)=m := Nat.add_sub_of_le low
  have nd : norm D ≠ norm F := fun e => different (dh.symm.trans ((congrArg (List.map (h+·)) e).trans fh))
  have marks (B : List ℕ) (hb : B∈all) (v : ℕ) (hv : v∈norm B) : m-h<v := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    have := long B hb x hx
    omega
  have bounded' (e : List ℕ × ℕ) (he : e∈runs) : e.1≠norm F ∧ e.2<r+1 := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    have := bounded p hp
    have inc : p.1∈BlockRuns.after F ps := List.mem_flatMap.mpr ⟨p,hp,by simp⟩
    have rest := restored p.1 (by simp [all,history,inc])
    exact ⟨fun same => this.1 (rest.symm.trans ((congrArg (List.map (h+·)) same).trans fh)),this.2⟩
  have recoded : RecognizesBlock (norm F) (normHist++[norm D,norm F]) := by
    intro B mem sub
    have basis : all.map norm=normHist++[norm D,norm F] := by simp [all,normed]
    rw [←basis] at mem
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp mem
    have back := sub.map (h+·)
    rw [fh,restored P hP] at back
    exact congrArg norm (recognize P hP back)
  have result := maximum_run_certificate h (m-h) (norm F) (norm D) r runs (norm later) pos nd
    (marks D dIn) (fun x => Nat.lt_irrefl _ (marks F fIn _ x)) (by simpa [norm] using nonempty) bounded' recoded
  have er : (norm later).map (h+·)=later := restore_offset h later after
  change HasFiniteCertificate ({[a],mixed (m-h+1) [] h,
    mixed 0 ((separated (m-h) normHist ++ norm D ++ (m-h)::(blockPattern (m-h) (norm F) r++norm later)).map (h+·)) 0}
    : Set (Word Bool)) at result
  simp only [List.map_append,List.map_cons,map_separated,map_pattern,mn,restorHist,fh,dh,er] at result
  exact raise_left_margin (by simp) (show m-h+1≤k by omega) result

end ThreeWordCodes.BinaryGaps
