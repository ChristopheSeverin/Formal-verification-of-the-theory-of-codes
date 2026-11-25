module

public import ThreeWordCodes.MaximalBlock

/-! # Unequal endpoint blocks at the minimum gap -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

def joinBlocks (m : ℕ) (blocks : List (List ℕ)) := [m].intercalate blocks

theorem cut_blocks (m : ℕ) (front tail : List (List ℕ)) (nonempty : tail≠[]) :
    joinBlocks m (front++tail)=separated m front ++ joinBlocks m tail := by
  induction front with
  | nil => simp
  | cons b bs ih =>
    have ne : bs++tail≠[] := by simp [nonempty]
    change [m].intercalate (b::(bs++tail)) = _
    rw [List.intercalate_cons_of_ne_nil ne,show [m].intercalate (bs++tail)=_ from ih,separated_cons]
    simp [List.append_assoc]

theorem last_block (m : ℕ) (front : List (List ℕ)) (last : List ℕ) (nonempty : front≠[]) :
    joinBlocks m (front++[last])=joinBlocks m front ++ m::last := by
  induction front with
  | nil => contradiction
  | cons f rest ih =>
    cases rest with
    | nil => simp [joinBlocks]
    | cons r rest => simp [joinBlocks,List.append_assoc] at ih ⊢; exact ih

theorem reverse_blocks (m : ℕ) (blocks : List (List ℕ)) :
    (joinBlocks m blocks).reverse = joinBlocks m (blocks.reverse.map List.reverse) := by
  induction blocks with
  | nil => rfl
  | cons f rest ih =>
    cases rest with
    | nil => simp [joinBlocks]
    | cons r rest =>
      have eqn : joinBlocks m (f::r::rest) = f++m::joinBlocks m (r::rest) := by simp [joinBlocks]
      rw [eqn,List.reverse_cons,List.map_append,List.map_singleton,last_block _ _ _ (by simp),
        List.reverse_append,List.reverse_cons,ih]
      simp [List.append_assoc]

theorem split_first {A : Type*} [DecidableEq A] (x : A) (xs : List A) (mem : x∈xs) :
    ∃ pre tail, xs=pre++x::tail ∧ x∉pre := by
  induction xs with
  | nil => simp at mem
  | cons z zs ih =>
    by_cases same : z=x
    · exact ⟨[],zs,by simp [same],by simp⟩
    · obtain ⟨pre,tail,eqn,miss⟩ := ih ((List.mem_cons.mp mem).resolve_left (Ne.symm same))
      exact ⟨z::pre,tail,by simp [eqn],by simp [miss,Ne.symm same]⟩

theorem blocks_lower (m : ℕ) (blocks : List (List ℕ))
    (ok : ∀ B∈blocks, ∀ x∈B,m<x) : ∀ x∈joinBlocks m blocks,m≤x := by
  induction blocks with
  | nil => simp [joinBlocks]
  | cons f rest ih =>
    intro x mem
    have less := ok f (by simp)
    cases rest with
    | nil => exact (less x (by simpa [joinBlocks] using mem)).le
    | cons r rest =>
      change x∈[m].intercalate (f::r::rest) at mem
      rw [List.intercalate_cons_cons,List.append_assoc] at mem
      rcases List.mem_append.mp mem with hf | later
      · exact (less x hf).le
      · rcases List.mem_cons.mp later with rfl | h
        · rfl
        · exact ih (fun B hb => ok B (by simp [hb])) x h

theorem before_first_maximum (k h m : ℕ) (front L : List ℕ) (other : List (List ℕ))
    (pos : 0<h) (low : h≤m) (short : m<k+h) (nonempty : L≠[]) (different : front≠L)
    (atL : L∈front::other) (all : ∀ B∈front::other,∀ x∈B,m<x)
    (maximum : ∀ B∈front::other,blockWeight B≤blockWeight L) :
    Completable (oneMarker k h (mixed 0 (joinBlocks m (front::other)) 0)) := by
  obtain ⟨pre,tail,eqn,missing⟩ := split_first L other ((List.mem_cons.mp atL).resolve_left (Ne.symm different))
  let past := front::pre
  have np : past≠[] := by simp [past]
  let earlier := past.dropLast
  let prev := past.getLast np
  have last : earlier++[prev]=past := List.dropLast_concat_getLast np
  have form : front::other = past++L::tail := by simp [past,eqn]
  have earlier_in {B : List ℕ} (hb : B∈earlier++[prev]) : B∈front::other := by
    rw [last] at hb
    rw [form]
    simp [hb]
  have lPre : L <+: joinBlocks m (L::tail) := by
    cases tail with
    | nil => simp [joinBlocks]
    | cons c cs => exact ⟨m::joinBlocks m (c::cs),by simp [joinBlocks,List.append_assoc]⟩
  obtain ⟨later,rest⟩ := lPre
  have shape : joinBlocks m (front::other) = separated m (earlier++[prev]) ++ L ++ later := by
    rw [form,cut_blocks _ _ _ (by simp),←rest,last,List.append_assoc]
  have laterLow (x : ℕ) (hx : x∈later) := low.trans (blocks_lower m _ all x
    (by rw [shape]; simp [hx]))
  cases L with
  | nil => contradiction
  | cons n body =>
    rw [shape]
    exact maximum_block_completion k h m n earlier prev body later pos low short (all _ atL _ (by simp))
      (fun x hx => all _ atL x (by simp [hx]))
      (fun B hb x hx => low.trans (all B (earlier_in hb) x hx).le) laterLow
      (fun B hb => maximum B (earlier_in hb)) (by rw [last]; simp [past,Ne.symm different,missing])

/-- Splitting at every minimum may produce any number of blocks. If the two
endpoint blocks differ, the code completes. Ties for greatest weight and
empty blocks are allowed. -/
theorem different_endpoint_blocks_completion (k h m : ℕ) (first last : List ℕ) (middle : List (List ℕ))
    (long : ∀ B∈first::(middle++[last]), ∀ x∈B,m<x) (distinct : first≠last)
    (code : NamedCode (oneMarker k h (mixed 0 (joinBlocks m (first::(middle++[last]))) 0))) :
    Completable (oneMarker k h (mixed 0 (joinBlocks m (first::(middle++[last]))) 0)) := by
  by_contra fail
  by_cases hz : h=0
  · subst h; exact fail (left_marker_completion k _ code)
  by_cases kz : k=0
  · subst k; exact fail (right_marker_completion h _ code)
  let blocks := first::(middle++[last])
  have leading : joinBlocks m blocks = first++m::joinBlocks m (middle++[last]) := by
    change [m].intercalate (first::(middle++[last])) = _
    rw [List.intercalate_cons_of_ne_nil (by simp),List.append_assoc]
    rfl
  have low := one_marker_gaps fail m (by rw [show joinBlocks m (first::(middle++[last]))=_ from leading]; simp)
  by_cases short : m<k+h
  · obtain ⟨L,hL,big⟩ := Finset.exists_max_image blocks.toFinset blockWeight (by simp [blocks])
    have atL := List.mem_toFinset.mp hL
    have maximum (B) (hb : B∈blocks) := big B (List.mem_toFinset.mpr hb)
    have nonempty : L≠[] := by
      rintro rfl
      have one := maximum first (by simp [blocks])
      have two := maximum last (by simp [blocks])
      simp [blockWeight] at one two
      exact distinct (one.2.trans two.2.symm)
    by_cases eqn : first=L
    · subst L
      let bRev := blocks.reverse.map List.reverse
      have revForm : bRev=last.reverse::(middle.reverse.map List.reverse ++ [first.reverse]) := by simp [bRev,blocks]
      have revMem {B : List ℕ} : B∈bRev ↔ B.reverse∈blocks := by
        simp only [bRev,List.mem_map,List.mem_reverse]
        constructor
        · rintro ⟨P,hP,rfl⟩; simpa using hP
        · intro hP; exact ⟨B.reverse,hP,List.reverse_reverse _⟩
      have full : Completable (oneMarker h k (mixed 0 (joinBlocks m bRev) 0)) := by
        rw [revForm]
        apply before_first_maximum h k m last.reverse first.reverse _ (by omega) (by omega) (by omega)
          (by simpa using nonempty) (by simpa using Ne.symm distinct)
        · rw [←revForm,revMem]; simp [blocks]
        · intro B mem x hx
          rw [←revForm,revMem] at mem
          exact long _ mem x (by simpa using hx)
        · intro B mem
          rw [←revForm,revMem] at mem
          simpa using maximum B.reverse mem
      have vrev : (fun i => (oneMarker h k (mixed 0 (joinBlocks m bRev) 0) i).reverse) =
          oneMarker k h (mixed 0 (joinBlocks m blocks) 0) := by
        have g : (joinBlocks m bRev).reverse = joinBlocks m blocks := by rw [←reverse_blocks,List.reverse_reverse]
        funext i
        rcases i with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed,g]
      exact fail (vrev ▸ full.reverse)
    · exact fail (before_first_maximum k h m first L _ (by omega) (by omega) short nonempty eqn atL long maximum)
  · exact long_gap_ambiguity k h _ (fun x hx => (Nat.le_of_not_gt short).trans (blocks_lower m _ long x hx)) code

end ThreeWordCodes.BinaryGaps
