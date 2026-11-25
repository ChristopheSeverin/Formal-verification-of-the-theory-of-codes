module

public import ThreeWordCodes.Graft
public import ThreeWordCodes.OneMarker

/-! # The first-short-gap tree construction

On the two named leaves A and C, use A, A^(d+1)C, and C A^d C. Every proper
nonempty suffix has the form A^r C with r at most d. A literal tail beginning
with more than d copies of a followed by b is incomparable with its image.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps
variable {I : Type*} [DecidableEq I]

def endC (A C : I) (d : ℕ) := List.replicate d A ++ [C]
def firstCutLeaves (A C : I) (d : ℕ) : Finset (Word I) :=
  {[A], A :: endC A C d, C :: endC A C d}

omit [DecidableEq I] in
theorem endC_suffixes (A C : I) (d : ℕ) (w : Word I) (p : w <:+ endC A C d) :
    w=[] ∨ ∃ r≤d, w=endC A C r := by
  induction d with
  | zero =>
    rcases List.suffix_cons_iff.mp p with he | ht
    · exact Or.inr ⟨0,le_rfl,he⟩
    · exact Or.inl (by simpa using ht)
  | succ d ih =>
    rcases List.suffix_cons_iff.mp p with eqn | tail
    · exact Or.inr ⟨_,le_rfl,eqn⟩
    · rcases ih tail with none | ⟨r,hr,h⟩
      · exact Or.inl none
      · exact Or.inr ⟨r,by omega,h⟩

theorem firstCutNode (A C : I) (d : ℕ) (w : Word I) (hw : w ∈ suffixNodes (firstCutLeaves A C d)) :
    w=[] ∨ ∃ r≤d, w=endC A C r := by
  rcases mem_suffixNodes.mp hw with nil | ⟨leaf,hl,tail,proper⟩
  · exact Or.inl nil
  · simp only [firstCutLeaves,Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl (by simpa using (List.suffix_cons_iff.mp tail).resolve_left proper)
    · exact endC_suffixes _ _ _ _ ((List.suffix_cons_iff.mp tail).resolve_left proper)
    · exact endC_suffixes _ _ _ _ ((List.suffix_cons_iff.mp tail).resolve_left proper)

theorem firstCutSuffixFree (A C : I) (d : ℕ) (ne : A≠C) :
    ∀ w ∈ firstCutLeaves A C d, ∀ v ∈ firstCutLeaves A C d, w <:+ v → w=v := by
  intro w hw v hv tail
  by_contra proper
  obtain empty | ⟨r,le,form⟩ := firstCutNode A C d w (mem_suffixNodes.mpr (Or.inr ⟨v,hv,tail,proper⟩))
  · simp only [firstCutLeaves,Finset.mem_insert,Finset.mem_singleton] at hw
    simp [empty] at hw
  · simp only [firstCutLeaves,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · have e := congrArg List.getLast? form
      simp only [endC,List.getLast?_append,List.getLast?_singleton,Option.some_or,Option.some.injEq] at e
      exact ne e
    · have e := congrArg List.length form
      simp [endC] at e
      omega
    · have e := congrArg List.length form
      simp [endC] at e
      omega

theorem inner_free (h : ℕ) :
    InformationTheory.IsPrefixFree (({[a],b::run h} : Finset (Word Bool)) : Set (Word Bool)) := by
  intro x hx y hy cmp
  change x ∈ ({[a],b::run h} : Finset (Word Bool)) at hx
  change y ∈ ({[a],b::run h} : Finset (Word Bool)) at hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    first | rfl | (obtain ⟨t,he⟩ := cmp; simp [a,b] at he)

/-- An infinite family from Section 3. The third word starts with b, its
first gap is h+d and its second gap is h+n. Everything after the third marker
is arbitrary. The proof supplies a positive polynomial certificate. -/
theorem first_short_gap_certificate (h d n : ℕ) (long : d<n) (tail : Word Bool) :
    HasFiniteCertificate ({[a], mixed (d+1) [] h,
      (b::run h) ++ run d ++ (b::run h) ++ run n ++ b::tail} : Set (Word Bool)) := by
  let X : Finset (Word Bool) := {[a],b::run h}
  let I := internalNodes X
  have subset : X ⊆ leaves I := subset_leaves (inner_free h) (by simp [X])
  let A : ↥(leaves I) := ⟨[a],subset (by simp [X])⟩
  let C : ↥(leaves I) := ⟨b :: run h,subset (by simp [X])⟩
  let phi := fun b : ↥(leaves I) => b.val
  have ne : A≠C := by
    intro same
    have e := congrArg Subtype.val same
    simp [A,C,a,b] at e
  let E := firstCutLeaves A C d
  let s := C::endC A C d
  let t := run n ++ b::tail
  have nonempty : t≠[] := by simp [t]
  have power (r : ℕ) : spell phi (List.replicate r A) = run r := by
    induction r with
    | zero => rfl
    | succ r ih => exact congrArg (a :: ·) ih
  have codeEnd (r : ℕ) : spell phi (endC A C r) = run r ++ b::run h := by
    simp [endC,power,phi,C]
  have apart (r : ℕ) (le : r≤d) : ¬ Comparable t (spell phi (endC A C r)) := by
    rw [codeEnd]
    rintro (pr|pr)
    · exact (Nat.ne_of_gt (by omega : r<n)) (marked_prefix pr).1
    · exact (Nat.ne_of_lt (by omega : r<n)) (marked_prefix pr).1
  have noEmpty : [] ∉ E := by simp [E,firstCutLeaves]
  have sIn : s ∈ E := by simp [s,E,firstCutLeaves]
  have out := tree_extension_certificate I (internalNodes_closed X) E noEmpty (firstCutSuffixFree _ _ _ ne) s sIn
    t nonempty (by
      rw [mem_codedSet]
      rintro ⟨w,hw,eqn⟩
      rcases firstCutNode A C d w hw with rfl | ⟨r,le,rfl⟩
      · exact nonempty eqn.symm
      · exact apart r le (Or.inl (by rw [←eqn])))
    (by
      intro w hw cp
      rcases firstCutNode A C d w hw with rfl | ⟨r,le,rfl⟩
      · simpa using sIn
      · exact (apart r le cp).elim)
  apply out.mono
  rintro w (rfl | rfl | rfl)
  · right
    refine ⟨[A],⟨by simp [E,firstCutLeaves],?_⟩,rfl⟩
    rintro ⟨v,_,eqn⟩
    exact ne (List.cons.inj eqn).1.symm
  · right
    refine ⟨A::endC A C d,⟨by simp [E,firstCutLeaves],?_⟩,?_⟩
    · rintro ⟨v,_,eqn⟩
      exact ne (List.cons.inj eqn).1.symm
    · change [a] ++ spell phi (endC A C d) = _
      rw [codeEnd]
      rfl
  · left
    apply Set.mem_singleton_iff.mpr
    symm
    change spell phi (C::endC A C d) ++ t = _
    rw [spell_cons,codeEnd]
    simp [C,phi,t,List.append_assoc]

/-- A certificate for smaller left margin extends to the requested margin.
The third word has at least two markers, so all three names are distinct. -/
theorem raise_left_margin {l k h q : ℕ} {gs : List ℕ} (ne : gs≠[]) (len : l≤k)
    (build : HasFiniteCertificate ({[a],mixed l [] h,mixed 0 gs q} : Set (Word Bool))) :
    Completable (oneMarker k h (mixed 0 gs q)) := by
  let w := mixed 0 gs q
  let small := oneMarker l h w
  have accept : HasPositiveCompletion (Set.range small) := by
    apply build.toPositive.mono
    rintro _ ⟨(_ | (_ | _)),rfl⟩ <;> simp [small,oneMarker,addToken,pair,w]
  have unique : Function.Injective small := by
    cases gs with
    | nil => contradiction
    | cons first gs =>
      rintro (_ | (_ | _)) (_ | (_ | _)) eqn <;> try rfl
      all_goals
        have size := congrArg (fun w : Word Bool => w.count b) eqn
        simp [small,oneMarker,addToken,pair,w,mixed_count,b,a] at size
  have base : Completable small := by
    refine ⟨(namedCode_iff_range _).mpr ⟨unique,?_⟩,accept⟩
    obtain ⟨M,_,_,contains,isMax,_⟩ := accept
    intro s t hs ht
    exact isMax.1 s t (fun z hz => contains (hs z hz)) (fun z hz => contains (ht z hz))
  let pad (x : Option Bool) := if x=some true then List.replicate (k-l) (some false) else []
  have pure (m : ℕ) : spell small (List.replicate m (some false)) = run m := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (a :: ·) ih
  have names : (fun x => spell small (pad x) ++ small x) = oneMarker k h w := by
    funext x
    rcases x with _ | (_ | _)
    · rfl
    · rfl
    · change spell small (List.replicate (k-l) (some false)) ++ mixed l [] h = mixed k [] h
      rw [pure]
      change run (k-l) ++ (run l ++ b::run h) = _
      rw [←List.append_assoc,←run_add,Nat.sub_add_cancel len]
      rfl
  exact names ▸ base.padLeft pad

/-- Complete the family with its original exponents. If the first gap u
is too short for both margins and the next gap v is longer than u, later
markers and the terminal margin are unrestricted. -/
theorem initial_short_gap_completion (k h u v : ℕ) (later : List ℕ) (q : ℕ)
    (lower : h ≤ u) (short : u < k+h) (rise : u<v) :
    Completable (oneMarker k h (mixed 0 (u::v::later) q)) := by
  let d := u-h
  let n := v-h
  let w := mixed 0 (u::v::later) q
  have len : d+1 ≤ k := by dsimp [d]; omega
  have build := first_short_gap_certificate h d n (by dsimp [d,n]; omega) (gapTail q later)
  have text : (b::run h) ++ run d ++ (b::run h) ++ run n ++ b::gapTail q later = w := by
    have eu : u=h+d := by dsimp [d]; omega
    have ev : v=h+n := by dsimp [n]; omega
    change _ = mixed 0 (u::v::later) q
    rw [eu,ev]
    simp [mixed,gapTail,run_add,List.append_assoc,show run 0=[] from rfl]
  rw [text] at build
  exact raise_left_margin (by simp) len build

/-- Reversing the same construction handles a short last gap preceded by a
larger one, with an arbitrary initial margin and arbitrary earlier gaps. -/
theorem final_short_gap_completion (k h u v : ℕ) (earlier : List ℕ) (i : ℕ)
    (lower : k ≤ u) (short : u < k+h) (rise : u<v) :
    Completable (oneMarker k h (mixed i (earlier ++ [v,u]) 0)) := by
  have hc := initial_short_gap_completion h k u v earlier.reverse i lower (by omega) rise
  have actual : (fun n => (oneMarker h k (mixed 0 (u::v::earlier.reverse) i) n).reverse) =
      oneMarker k h (mixed i (earlier ++ [v,u]) 0) := by
    funext n
    rcases n with _ | (_ | _) <;> simp [oneMarker,addToken,pair,reverse_mixed,List.append_assoc]
  exact actual ▸ hc.reverse

end ThreeWordCodes.BinaryGaps
