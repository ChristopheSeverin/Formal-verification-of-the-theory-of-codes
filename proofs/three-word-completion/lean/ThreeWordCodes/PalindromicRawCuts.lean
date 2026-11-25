module

public import ThreeWordCodes.PalindromicSelection

/-! # Leaf selections with the original gap lengths -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

/-- A nonempty suffix begins partway through an entry of a selected leaf or
inside the short, one-marker leaf. -/
def Origin (m : ℕ) (cuts : List (List ℕ)) (r : ℕ) (us : List ℕ) : Prop :=
  (us=[] ∧ r≤m) ∨ ∃ p∈cuts, ∃ pre n, p=pre++n::us ∧ r≤n

/-- Perform a selection in the original lengths and remove h from every gap
only when spelling the selected suffix leaves. This keeps comparisons of block
weights invariant under reversing the two exponents. -/
theorem raw_selection (s k l h m : ℕ) (cuts : List (List ℕ)) (cut front : List ℕ) (g : ℕ)
    (later : List ℕ) (z : Word Bool) (read : Reading s (cut++front++g::later) z)
    (height : h≤l) (hm : h≤m) (width : m-h≤k) (long : h<g) (chosen : cut∈cuts)
    (low : ∀ n∈cut++front++g::later,h≤n) (leafLow : ∀ p∈cuts, ∀ n∈p,h≤n)
    (last : ∀ p∈cuts, ∃ pre n,p=pre++[n] ∧ n≤m)
    (antichain : ∀ p∈cuts, ∀ q∈cuts, p <:+ q → p=q)
    (test : ∀ r us, Origin m cuts r us →
      ((r::us <+: front) → cut++r::us∈cuts) ∧
      (∀ j tail,r::us=front++j::tail → g≤j → False))
    (ending : z.getLast?=some b) : Completable (triple s k l z) := by
  let down (p : List ℕ) := p.map (·-h)
  let up (p : List ℕ) := p.map (h+·)
  have undo (p : List ℕ) (hp : ∀ n∈p,h≤n) : up (down p)=p := restore_offset h p hp
  have downUp (p : List ℕ) : down (up p)=p := by simp [down,up,List.map_map,Function.comp_def]
  have lc : up (down cut)=cut := undo _ (fun n hn => low n (by simp [hn]))
  have lf : up (down front)=front := undo _ (fun n hn => low n (by simp [hn]))
  have ll : up (down later)=later := undo _ (fun n hn => low n (by simp [hn]))
  have add (p : List ℕ) (hp : p∈cuts) : down p∈cuts.map down := List.mem_map.mpr ⟨p,hp,rfl⟩
  apply selected_completion s k l h (m-h) (cuts.map down) (down cut) (down front) (g-h) (down later) z
  · change Reading s (up (down cut++down front++(g-h)::down later)) z
    simpa only [up,List.map_append,List.map_cons,Nat.add_sub_of_le long.le,lc,lf,ll] using read
  · exact height
  · exact width
  · omega
  · exact add cut chosen
  · rintro _ mem
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
    obtain ⟨pr,n,snoc,le⟩ := last p hp
    exact ⟨down pr,n-h,by simp [down,snoc],Nat.sub_le_sub_right le h⟩
  · intro p hp q hq suf
    obtain ⟨P,mP,rfl⟩ := List.mem_map.mp hp
    obtain ⟨Q,mQ,rfl⟩ := List.mem_map.mp hq
    have sub : up (down P) <:+ up (down Q) := suf.map (h+·)
    rw [undo _ (leafLow P mP),undo _ (leafLow Q mQ)] at sub
    exact congrArg down (antichain P mP Q mQ sub)
  · intro r us origin
    have old : Origin m cuts (h+r) (up us) := by
      rcases origin with ⟨rfl,le⟩ | ⟨P,mP,pre,n,shape,le⟩
      · exact Or.inl ⟨rfl,by omega⟩
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mP
        have back := congrArg up shape
        rw [undo _ (leafLow p hp)] at back
        exact Or.inr ⟨p,hp,up pre,h+n,by simpa [up] using back,by omega⟩
    obtain ⟨early,full⟩ := test _ _ old
    constructor
    · intro fits
      have sub : up (r::us) <+: up (down front) := fits.map (h+·)
      rw [lf] at sub
      have permitted := add _ (early sub)
      simpa [down,up,List.map_map,Function.comp_def] using permitted
    · intro j tail shape le
      apply full (h+j) (up tail) _ (by omega)
      have back : up (r::us)=up (down front)++(h+j)::up tail := by simpa [up] using congrArg up shape
      rwa [lf] at back
  · exact ending

end ThreeWordCodes.Palindromic
