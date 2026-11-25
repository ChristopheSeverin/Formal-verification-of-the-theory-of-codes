module

public import ThreeWordCodes.EndpointBlocks

/-! # The remaining maximum-block selection in Proposition 6 -/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

theorem split_at (m : ℕ) (xs : List ℕ) :
    ∃ first rest, xs=joinBlocks m (first::rest) ∧ ∀ B∈first::rest, m∉B := by
  induction xs with
  | nil => exact ⟨[],[],rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨f,r,rfl,fresh⟩ := ih
    by_cases isM : x=m
    · subst x
      exact ⟨[],f::r,by simp [joinBlocks],by simpa using fresh⟩
    · refine ⟨x::f,r,?_,?_⟩
      · change x :: [m].intercalate (f::r) = [m].intercalate ((x::f)::r)
        rw [List.intercalate_cons_cons_left]
      · intro B mem
        rcases List.mem_cons.mp mem with rfl | rest
        · simp [Ne.symm isM,fresh f (by simp)]
        · exact fresh B (List.mem_cons_of_mem _ rest)

theorem block_mem {m : ℕ} (blocks : List (List ℕ)) {B : List ℕ} {x : ℕ}
    (hb : B∈blocks) (hx : x∈B) : x∈joinBlocks m blocks := by
  induction blocks with
  | nil => simp at hb
  | cons f r ih =>
    cases r with
    | nil => simpa [joinBlocks,List.mem_singleton.mp hb] using hx
    | cons R rs =>
      change x∈[m].intercalate (f::R::rs)
      rw [List.intercalate_cons_cons,List.append_assoc]
      rcases List.mem_cons.mp hb with rfl | later
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ih later))

theorem flat_equal_blocks (m : ℕ) (P : List ℕ) (xs : List (List ℕ))
    (all : ∀ B∈xs,B=P) :
    joinBlocks m (P::xs)=P++wordPow (m::P) xs.length := by
  induction xs with
  | nil => simp [joinBlocks]
  | cons Q xs ih =>
    obtain rfl := all Q (by simp)
    have inductionEq := ih (fun B hb => all B (by simp [hb]))
    change [m].intercalate (Q::Q::xs) = _
    rw [List.intercalate_cons_cons,show [m].intercalate (Q::xs)=_ from inductionEq,
      List.length_cons,wordPow_succ']
    simp [List.append_assoc]

/-- Only the case in which both endpoint blocks are the same nonempty block
and every different block is strictly lighter remains. -/
def CommonMaximumConstruction : Prop :=
  ∀ k h m (F : List ℕ) (middle : List (List ℕ)), 0<k → 0<h → max k h ≤ m → m<k+h → F≠[] →
    (∀ B∈F::middle,∀ x∈B,m<x) → (∃ B∈middle,B≠F) →
    (∀ B∈middle,B≠F → blockWeight B<blockWeight F) →
    let gs := joinBlocks m (F::(middle++[F]))
    NamedCode (oneMarker k h (mixed 0 gs 0)) → Completable (oneMarker k h (mixed 0 gs 0))

theorem pure_power_iff_common_maximum : PurePowerTheorem.{0} ↔ CommonMaximumConstruction := by
  constructor
  · intro all k h m F middle pk ph low short _ long _ _ gs code
    have bounds : ∀ B∈F::(middle++[F]), ∀ x∈B,m<x := by
      intro B hb
      apply long
      simpa [or_assoc,or_left_comm,or_comm] using hb
    have sep : m∈gs := by
      change m∈[m].intercalate (F::(middle++[F]))
      rw [List.intercalate_cons_of_ne_nil (by simp)]
      simp
    exact (pure_power_iff_one_marker.mp all) k h gs pk ph (fun x hx => low.trans (blocks_lower m _ bounds x hx))
      ⟨m,sep,short⟩ code
  · intro boundary
    apply pure_power_iff_repeated_interior.mpr
    intro k h m f t middle pk ph gs lower least mf mt short repeated _ nonuniform code
    have mem : m∈gs := List.count_pos_iff.mp (by omega)
    have low := lower m mem
    obtain ⟨F,rest,form,clear⟩ := split_at m gs
    have long (B : List ℕ) (hb : B∈F::rest) (x : ℕ) (hx : x∈B) : m<x := by
      have le := least x (form ▸ block_mem _ hb hx)
      have ne : m≠x := fun e => clear B hb (e.symm ▸ hx)
      omega
    have nz : rest≠[] := by
      rintro rfl
      exact clear F (by simp) (by simpa [form,joinBlocks] using mem)
    let last := rest.getLast nz
    let mid := rest.dropLast
    have snoc : mid++[last]=rest := List.dropLast_concat_getLast nz
    have word : gs=joinBlocks m (F::(mid++[last])) := by rwa [snoc]
    have named : NamedCode (oneMarker k h (mixed 0 (joinBlocks m (F::(mid++[last]))) 0)) := word ▸ code
    have marked (B : List ℕ) (hb : B∈F::(mid++[last])) := long B (snoc ▸ hb)
    rw [word]
    by_cases ends : F=last
    · have different : ∃ B∈mid,B≠F := by
        by_contra! same
        have eqAll (B : List ℕ) (hb : B∈mid++[last]) : B=F := by
          rcases List.mem_append.mp hb with earlier | final
          · exact same B earlier
          · exact (List.mem_singleton.mp final).trans ends.symm
        apply nonuniform
        exact ⟨F,mid.length,marked F (by simp),by
          rw [word,flat_equal_blocks m F _ eqAll]
          simp⟩
      let blocks := F::(mid++[last])
      by_cases heavier : ∃ B∈mid,B≠F ∧ blockWeight F≤blockWeight B
      · obtain ⟨B,bIn,bne,up⟩ := heavier
        have bMem : B∈blocks := by simp [blocks,bIn]
        obtain ⟨L,hl,top⟩ := Finset.exists_max_image blocks.toFinset blockWeight (by simp [blocks])
        have inL := List.mem_toFinset.mp hl
        have maxL (s : List ℕ) (hs : s∈blocks) := top s (List.mem_toFinset.mpr hs)
        have nonempty {P : List ℕ} (bound : ∀ s∈blocks,blockWeight s≤blockWeight P) : P≠[] := by
          rintro rfl
          have f0 := bound F (by simp [blocks])
          have b0 := bound B bMem
          simp [blockWeight] at f0 b0
          exact bne (b0.2.trans f0.2.symm)
        by_cases atHead : L=F
        · subst L
          have maxB (s : List ℕ) (hs : s∈blocks) := (maxL s hs).trans up
          exact before_first_maximum k h m F B _ ph (by omega) short (nonempty maxB) (Ne.symm bne) bMem marked maxB
        · exact before_first_maximum k h m F L _ ph (by omega) short (nonempty maxL) (Ne.symm atHead) inL marked maxL
      · have lighter (B : List ℕ) (hb : B∈mid) (ne : B≠F) : blockWeight B<blockWeight F :=
          Nat.lt_of_not_ge (fun ge => heavier ⟨B,hb,ne,ge⟩)
        have nonempty : F≠[] := by
          obtain ⟨B,hB,ne⟩ := different
          have lt := lighter B hB ne
          rintro rfl
          exact Nat.not_lt_zero _ lt
        rw [←ends] at named ⊢
        exact boundary k h m F mid pk ph low short nonempty (fun B hB => marked B (by
          rcases List.mem_cons.mp hB with rfl | hm
          · simp
          · simp [hm])) different lighter named
    · exact different_endpoint_blocks_completion k h m F last mid marked ends named

end ThreeWordCodes.BinaryGaps
