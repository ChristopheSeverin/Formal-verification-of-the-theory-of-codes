module

public import ThreeWordCodes.CrossedJoined

/-! # The alternating identities exclude the three lateral configurations in Section 5 -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)
variable {A : Type*}

inductive Column
  | shared | intermediate | reversed

def columnWords (k : Column) (p joined : Word A) (letter : Word A) :=
  match k with
  | .shared => pieces p (p++letter) joined
  | .intermediate => pieces p joined (joined++letter)
  | .reversed => pieces p (p++letter) (joined++letter)

private theorem commute_parse (g : Option Bool → Word A) (x y z : Option Bool) (diff : x≠y)
    (eqn : g x++(g y++g z)=(g y++g z)++g x) : ¬NamedCode g := by
  intro code
  have h := code (show spell g [x,y,z]=spell g [y,z,x] by simpa [List.append_assoc] using eqn)
  exact diff (List.cons.inj h).1

private theorem power_parse (g : Option Bool → Word A) (x y z : Option Bool) (diff : x≠y)
    (n m : ℕ) (eqn : wordPow (g x) (n+1)++g y=g y++wordPow (g z) m) : ¬NamedCode g := by
  intro code
  have h := code (show spell g (List.replicate (n+1) x++[y])=spell g (y::List.replicate m z)
    by simpa only [spell_cons,spell_append,spell_nil,List.append_nil,spell_replicate] using eqn)
  rw [List.replicate_succ] at h
  exact diff (List.cons.inj h).1

theorem alternating_column_first (k : Column) (m n : ℕ) :
    ¬NamedCode (columnWords k (wordPow [a,b] (m+1)) ([b]++wordPow [a,b] n) [a]) := by
  obtain ⟨one,two,three⟩ := comparison_table_first [a] [b] (m+1) n
  cases k with
  | shared => exact commute_parse _ P Q Z (by decide) one
  | intermediate => exact power_parse _ Z Q P (by decide) m (n+1) two.symm
  | reversed => exact power_parse _ P Q Z (by decide) n (m+1) three

theorem alternating_column_second (k : Column) (m n : ℕ) :
    ¬NamedCode (columnWords k (wordPow [b,a] m++[b]) (wordPow [a,b] (n+1)) [a]) := by
  obtain ⟨one,two,three⟩ := comparison_table_second [a] [b] m (n+1)
  cases k with
  | shared => exact power_parse _ Q P Z (by decide) n (m+1) one
  | intermediate => exact commute_parse _ Q Z P (by decide) two
  | reversed => exact commute_parse _ Q P Z (by decide) three

/-- A gap-one join with opposite initial letters is in one of the two
alternating rows. This includes a single marker on either side. -/
theorem joined_one (k : Column) (i h s : ℕ) (G E : List ℕ)
    (ends : (i=0 ∧ h=1) ∨ (i=1 ∧ h=0)) (gap : s+i=1)
    (ge : G=List.replicate G.length 1) (ee : E=List.replicate E.length 1) :
    ¬NamedCode (columnWords k (mixed i G 0) (mixed h E s++mixed i G 0) [a]) := by
  let L := E++(s+i)::G
  have total : L=List.replicate L.length 1 := by
    apply List.eq_replicate_iff.mpr ⟨rfl,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with mem|mem
    · exact (List.eq_replicate_iff.mp ee).2 a mem
    · rcases List.mem_cons.mp mem with rfl|mem
      · exact gap
      · exact (List.eq_replicate_iff.mp ge).2 a mem
  have joined : mixed h E s++mixed i G 0=mixed h (List.replicate L.length 1) 0 :=
    (join_mixed E G h s i 0).trans (congrArg (fun v => mixed h v 0) total)
  rw [joined]
  rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have first : mixed 0 G 0=wordPow [b,a] G.length++[b] :=
      (congrArg (fun ls => mixed 0 ls 0) ge).trans (head_body_ab G.length)
    have other : mixed 1 (List.replicate L.length 1) 0=wordPow [a,b] (L.length+1) := Border.uniform_power 1 L.length
    rw [first,other]; exact alternating_column_second k G.length L.length
  · have first : mixed 1 G 0=wordPow [a,b] (G.length+1) :=
      (congrArg (fun ls => mixed 1 ls 0) ge).trans (Border.uniform_power 1 G.length)
    have other : mixed 0 (List.replicate L.length 1) 0=[b]++wordPow [a,b] L.length := body_ab L.length
    rw [first,other]; exact alternating_column_first k G.length L.length

end ThreeWordCodes.CrossedCase
