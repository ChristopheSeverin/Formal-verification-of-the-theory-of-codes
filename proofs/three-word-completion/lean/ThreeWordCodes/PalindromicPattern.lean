module

public import ThreeWordCodes.PalindromicMaximum

/-! # Grafts with several selected prefixes at short gaps -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

def EndsBelow (d : ℕ) (p : List ℕ) := ∃ pre n,p=pre++[n] ∧ n≤d
def ShortPrefix (d : ℕ) (p look : List ℕ) := p <+: look ∧ p.length<look.length ∧ EndsBelow d p

private noncomputable def shortCuts (d : ℕ) (U look : List ℕ) : List (List ℕ) := by
  classical
  exact U::(look.inits.filter (fun p => p.length<look.length ∧ EndsBelow d p)).map (U++·)

private theorem mem_shortCuts {d U look w} : w∈shortCuts d U look ↔
    w=U ∨ ∃ p, ShortPrefix d p look ∧ w=U++p := by
  classical
  simp only [shortCuts,List.mem_cons,List.mem_map,List.mem_filter,decide_eq_true_eq,List.mem_inits]
  constructor
  · rintro (rfl | ⟨p,⟨hp,h,e⟩,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p,⟨hp,h,e⟩,rfl⟩
  · rintro (rfl | ⟨p,⟨hp,h,e⟩,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p,⟨hp,h,e⟩,rfl⟩

/-- Even an entrywise larger copy of the pattern must occur initially. -/
def OnlyAtStart (R H : List ℕ) : Prop :=
  ∀ pre W tail,H=pre++(W++tail) → Dominated R W → pre=[]

theorem pattern_completion (s k l m : ℕ) (U : List ℕ) (n : ℕ) (lead R : List ℕ) (later : List ℕ)
    (z : Word Bool) (read : Reading s (U++(n::(lead++R))++later) z)
    (hm : l≤m) (small : m≤k+l) (low : ∀ i∈U++(n::(lead++R))++later,l ≤ i)
    (nonempty : R≠[]) (long : l<R.getLast nonempty) (endU : EndsBelow m U) (start : R <+: U)
    (root : OnlyAtStart R U) (next : ∀ p, ShortPrefix m p (n::(lead++R)) → OnlyAtStart R (U++p))
    (ending : z.getLast?=some b) : Completable (triple s k l z) := by
  let look := n::(lead++R)
  let cuts := shortCuts m U look
  let g := R.getLast nonempty
  let front := n::(lead++R.dropLast)
  have lookEq : look=front++[g] := by
    have restore : R.dropLast++[g]=R := List.dropLast_concat_getLast nonempty
    simp only [front,look,List.cons_append,List.append_assoc,restore]
  have raw : U++front++g::later=U++look++later := by rw [lookEq]; simp [List.append_assoc]
  have uIn : U∈cuts := mem_shortCuts.mpr (Or.inl rfl)
  have allEnd (p : List ℕ) (hp : p∈cuts) : EndsBelow m p := by
    rcases mem_shortCuts.mp hp with rfl | ⟨q,⟨_,_,pre,x,whereAt,le⟩,rfl⟩
    · exact endU
    · exact ⟨U++pre,x,by simp [whereAt],le⟩
  have roots (p : List ℕ) (hp : p∈cuts) : OnlyAtStart R p := by
    rcases mem_shortCuts.mp hp with rfl | ⟨q,cond,rfl⟩
    · exact root
    · exact next q cond
  have starts (p : List ℕ) (hp : p∈cuts) : R <+: p := by
    rcases mem_shortCuts.mp hp with rfl | ⟨q,_,rfl⟩
    · exact start
    · exact start.trans (List.prefix_append ..)
  have lower (p : List ℕ) (hp : p∈cuts) (i : ℕ) (mem : i∈p) : l ≤ i := by
    apply low i
    rcases mem_shortCuts.mp hp with rfl | ⟨q,cond,rfl⟩
    · simp [mem]
    · rcases List.mem_append.mp mem with inside | right
      · simp [inside]
      · have inLook := cond.1.sublist.subset right
        exact List.mem_append_left _ (List.mem_append_right _ inLook)
  apply raw_selection s k l l m cuts U front g later z (raw.symm ▸ read) le_rfl hm (by omega) long uIn
    (raw.symm ▸ low) lower allEnd _ _ ending
  · intro p hp q hq suf
    obtain ⟨before,eqn⟩ := suf
    obtain ⟨tail,contains⟩ := starts p hp
    have atRoot := roots q hq before R tail (by rw [contains,eqn]) (List.forall₂_refl R)
    simpa [atRoot] using eqn
  · intro r us origin
    constructor
    · intro early
      have part : front <+: look := ⟨[g],lookEq.symm⟩
      have fit : ShortPrefix m (r::us) look := ⟨early.trans part,by
        exact lt_of_le_of_lt early.length_le (by rw [lookEq]; simp),origin.ends_short allEnd⟩
      exact mem_shortCuts.mpr (Or.inr ⟨_,fit,rfl⟩)
    · intro j tail fullMatch le
      obtain ⟨H,member,pre,v,host,bound⟩ := origin.host
      obtain ⟨W,placed,dominates⟩ := increased_ends bound le fullMatch
      rw [←lookEq] at dominates
      change Dominated ((n::lead)++R) W at dominates
      obtain ⟨P,Q,rfl,first,pattern⟩ := dominates.split
      have position : H=(pre++P)++(Q++tail) := by rw [host,placed]; simp [List.append_assoc]
      have plen := first.length_eq
      have qlen := pattern.length_eq
      have positive := List.length_pos_iff.mpr nonempty
      rcases List.mem_cons.mp member with rfl | old
      · have sizes := congrArg List.length position
        simp at sizes plen; omega
      · have atStart := roots H old (pre++P) Q tail position pattern
        have emptyP := (List.append_eq_nil_iff.mp atStart).2
        simp [emptyP] at plen

end ThreeWordCodes.Palindromic
