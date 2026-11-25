module

public import ThreeWordCodes.InteriorConstructions

/-! # Selecting a long block absent from the preceding gaps -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

theorem ends_after_split {front pre post : List ℕ} {m z : ℕ}
    (eqn : front++[m]=pre++z::post) (above : m<z) : m∈post := by
  induction post using List.reverseRecOn with
  | nil =>
    have same := congrArg List.getLast? eqn
    simp at same
    omega
  | append_singleton ps t _ =>
    have eqn' : front++[m]=(pre++z::ps)++[t] := by simpa using eqn
    have same := congrArg List.getLast? eqn'
    simp only [List.getLast?_concat,Option.some.injEq] at same
    simp [same]

/-- A nonempty long block following a short separator cannot match a proper
suffix of the prefix before the cut when its first gap may increase but its
remaining gaps do not occur there in the required order. -/
theorem fresh_block_certificate (h m n : ℕ) (front blockTail later : List ℕ)
    (pos : 0<h) (long : m<n) (block : ∀ x∈blockTail, m<x)
    (fresh : ∀ pre z after, front++[m] = pre++z::(blockTail++after) → n≤z → False) :
    HasFiniteCertificate ({[a],mixed (m+1) [] h,
      mixed 0 (((front++[m])++n::(blockTail++later)).map (h+·)) 0} : Set (Word Bool)) := by
  let cut := front++[m]
  apply gap_selection_certificate h m [cut] cut n (blockTail++later) pos (by simp)
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨front,m,rfl,le_rfl⟩
  · simp
  · omega
  · intro p hp pre z post eqn le cmp
    obtain rfl := List.mem_singleton.mp hp
    have marked := ends_after_split eqn (long.trans_le le)
    have preBlock : blockTail <+: blockTail++later := ⟨_,rfl⟩
    have matched : blockTail <+: post := by
      rcases cmp with pr | pr
      · rcases List.prefix_or_prefix_of_prefix preBlock pr with ok | early
        · exact ok
        · exact (Nat.lt_irrefl _ (block m (early.sublist.subset marked))).elim
      · exact preBlock.trans pr
    obtain ⟨after,shape⟩ := matched
    exact (fresh pre z after (by simpa only [shape] using eqn) le).elim

/-- The manuscript's weight of a block counts each gap and its following marker. -/
def blockWeight (xs : List ℕ) := xs.sum + xs.length

@[simp] private theorem weight_nil : blockWeight []=0 := rfl
@[simp] private theorem weight_cons (x : ℕ) (xs : List ℕ) : blockWeight (x::xs)=x+1+blockWeight xs := by
  simp [blockWeight]; omega
@[simp] private theorem weight_append (xs ys : List ℕ) : blockWeight (xs++ys)=blockWeight xs+blockWeight ys := by
  simp [blockWeight]; omega
@[simp] theorem blockWeight_reverse (xs : List ℕ) : blockWeight xs.reverse=blockWeight xs := by simp [blockWeight]
private theorem zero_block {xs : List ℕ} (zero : blockWeight xs=0) : xs=[] := by
  cases xs with
  | nil => rfl
  | cons x xs => simp at zero

private theorem maximum_excludes {front tail : List ℕ} {m n : ℕ}
    (size : blockWeight front ≤ blockWeight (n::tail)) (distinct : front≠n::tail)
    (start : m<n) (long : ∀ x∈tail,m<x)
    (pre : List ℕ) (z : ℕ) (after : List ℕ) (eqn : front++[m] = pre++z::(tail++after))
    (more : n≤z) : False := by
  induction after using List.reverseRecOn with
  | nil =>
    have mem := ends_after_split (by simpa using eqn : front++[m]=pre++z::tail) (start.trans_le more)
    exact Nat.lt_irrefl _ (long m mem)
  | append_singleton rest a _ =>
    have e : front++[m]=(pre++z::(tail++rest))++[a] := by simpa using eqn
    have ends := congrArg List.getLast? e
    simp only [List.getLast?_concat,Option.some.injEq] at ends
    subst a
    have full := List.append_cancel_right e
    rw [full] at size
    simp only [weight_append,weight_cons] at size
    have preEmpty := zero_block (xs:=pre) (by omega)
    have restEmpty := zero_block (xs:=rest) (by omega)
    have same : z=n := by omega
    exact distinct (by simpa [preEmpty,restEmpty,same] using full)

theorem restore_offset (h : ℕ) (xs : List ℕ) (lower : ∀ x∈xs,h≤x) :
    (xs.map (·-h)).map (h+·) = xs := by
  rw [List.map_map]
  calc xs.map _ = xs.map id := List.map_congr_left (fun x hx => Nat.add_sub_of_le (lower x hx))
       _ = xs := List.map_id ..

/-- Two unequal long blocks separated by their only minimum. The right block
has at least as much weight as the left. Comparisons are made on literal gaps,
so reversal may later exchange the two outside exponents. -/
private theorem unequal_blocks_directed (k h m : ℕ) (front : List ℕ) (n : ℕ) (tail : List ℕ)
    (pos : 0<h) (lower : h≤m) (short : m<k+h) (endLong : m<n)
    (longL : ∀ x∈front,m<x) (longR : ∀ x∈tail,m<x)
    (size : blockWeight front ≤ blockWeight (n::tail)) (distinct : front≠n::tail) :
    Completable (oneMarker k h (mixed 0 (front++m::n::tail) 0)) := by
  let f := front.map (·-h)
  let bdy := tail.map (·-h)
  have frontId : f.map (h+·) = front := restore_offset h front (fun x hx => lower.trans (longL x hx).le)
  have tailId : bdy.map (h+·) = tail := restore_offset h tail (fun x hx => lower.trans (longR x hx).le)
  have mId := Nat.add_sub_of_le lower
  have nId := Nat.add_sub_of_le (lower.trans endLong.le)
  have proof := fresh_block_certificate h (m-h) (n-h) f bdy [] pos (by omega)
    (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      have := longR y hy
      omega)
    (by
      intro pre z after eqn more
      have literal := congrArg (List.map (h+·)) eqn
      simp only [List.map_append,List.map_cons,List.map_nil,frontId,tailId,mId] at literal
      exact maximum_excludes size distinct endLong longR _ (h+z) _ literal (by omega))
  simp only [List.append_nil,List.map_append,List.map_cons,frontId,tailId,mId,nId,
    List.append_assoc,List.singleton_append] at proof
  apply raise_left_margin (gs:=front++m::n::tail) (by simp) (show m-h+1≤k by omega) proof

/-- When the unique minimum of the internal gaps separates two different
blocks, every injective one-marker triple has a positive finite completion. -/
theorem unequal_blocks_completion (k h m : ℕ) (front back : List ℕ)
    (fLong : ∀ x∈front,m<x) (bLong : ∀ x∈back,m<x) (distinct : front ≠ back)
    (code : NamedCode (oneMarker k h (mixed 0 (front++m::back) 0))) :
    Completable (oneMarker k h (mixed 0 (front++m::back) 0)) := by
  by_contra fail
  by_cases hz : h=0
  · subst h; exact fail (left_marker_completion k _ code)
  by_cases kz : k=0
  · subst k; exact fail (right_marker_completion h _ code)
  have lower := one_marker_gaps fail m (by simp)
  have minTo (x : ℕ) (hx : x∈front++m::back) : m≤x := by
    rcases List.mem_append.mp hx with hf | rest
    · exact (fLong x hf).le
    · rcases List.mem_cons.mp rest with rfl | hb
      · rfl
      · exact (bLong x hb).le
  by_cases short : m < k+h
  · rcases le_total (blockWeight front) (blockWeight back) with orient | orient
    · cases back with
      | nil => exact fail (minimum_last_gap_completion k h m front (fun x hx => (fLong x hx).le) code)
      | cons n tail =>
        exact fail (unequal_blocks_directed k h m front n tail (by omega) (by omega) short (bLong n (by simp))
          fLong (fun x hx => bLong x (by simp [hx])) orient distinct)
    · let rev := front.reverse
      have eqn : (fun i => (oneMarker h k (mixed 0 (back.reverse++m::rev) 0) i).reverse) =
          oneMarker k h (mixed 0 (front++m::back) 0) := by
        funext i
        rcases i with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed,rev,List.append_assoc]
      have fRev (x : ℕ) (hx : x∈rev) : m<x := fLong x (by simpa [rev] using hx)
      have bRev (x : ℕ) (hx : x∈back.reverse) : m<x := bLong x (by simpa using hx)
      have sep : back.reverse≠rev := fun e => distinct (List.reverse_inj.mp e).symm
      have wt : blockWeight back.reverse ≤ blockWeight rev := by simpa [rev] using orient
      have done : Completable (oneMarker h k (mixed 0 (back.reverse++m::rev) 0)) := by
        cases er : rev with
        | nil =>
          have base : NamedCode (oneMarker h k (mixed 0 (back.reverse++m::rev) 0)) := by
            have first : NamedCode (fun i => (oneMarker h k (mixed 0 (back.reverse++m::rev) 0) i).reverse) := eqn.symm ▸ code
            have second := first.reverse
            simpa using second
          rw [er] at base
          exact minimum_last_gap_completion h k m back.reverse (fun x hx => (bRev x hx).le) base
        | cons n tail =>
          rw [er] at fRev wt sep
          exact unequal_blocks_directed h k m _ n tail (by omega) (by omega) (by omega) (fRev n (by simp))
            bRev (fun x hx => fRev x (by simp [hx])) wt sep
      exact fail (eqn ▸ done.reverse)
  · exact long_gap_ambiguity k h _ (fun x hx => (Nat.le_of_not_gt short).trans (minTo x hx)) code

end ThreeWordCodes.BinaryGaps
