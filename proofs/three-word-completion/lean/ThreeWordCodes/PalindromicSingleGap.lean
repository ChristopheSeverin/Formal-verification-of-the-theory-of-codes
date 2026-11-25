module

public import ThreeWordCodes.PalindromicCoordinates

/-! # The single-gap case in Proposition 7 -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

def single (s n : ℕ) := c ++ wordPow (x s) n ++ c.reverse

@[simp] theorem single_reverse (s n : ℕ) : (single s n).reverse=single s n := by
  simp [single,back_pow,List.append_assoc]

private theorem model_single (n : ℕ) : abstractWord (List.replicate n a)=mixed 0 [n+2] 0 := by
  have names := spell_replicate (pair [a] [b,a]) a n
  change spell (pair [a] [b,a]) (List.replicate n a)=wordPow [a] n at names
  have copies : wordPow [a] n=run n := by
    clear names
    induction n with
    | zero => rfl
    | succ n ih => rw [wordPow_succ',ih]; rfl
  rw [abstractWord,names,copies]
  change b::a::(run n ++ [a,b]) = b::(run (n+2) ++ [b])
  rw [show n+2=1+n+1 by omega,run_add,run_add]
  simp [run,List.append_assoc]

/-- When both margins fit the only gap, the two parsings from Section 3
contradict injectivity. -/
theorem single_ambiguity (s k l n : ℕ) (bound : max (k+1) (l+1) ≤ n+2) :
    ¬NamedCode (triple s k l (single s n)) := by
  intro code
  have word : literal s (List.replicate n a)=single s n := by
    simp [literal,single,spell_replicate,pair,a]
  have model := abstract_code (p:=List.replicate n a) (word.symm ▸ code)
  rw [model_single] at model
  apply (one_marker_ambiguity_iff (k+1) (l+1) [n+2]).mpr _ model
  by_cases long : k+1+(l+1)≤n+2
  · exact Or.inl (by simpa using long)
  · exact Or.inr ⟨[],n+2,0,bound,by omega,by simp,by simp⟩

/-- With a larger right exponent, use the prefix words x, z, and f x^j.
After the common prefix f, the first and third of these begin with b and a. -/
theorem single_right_completion (s k l n : ℕ) (large : n+2<l+1) :
    Completable (triple s k l (single s n)) := by
  obtain ⟨j,exponent⟩ := Nat.exists_eq_add_of_le (show n+2≤l by omega)
  let z := single s n
  let F := pal s ++ wordPow (x s) (j+1)
  let v := addToken (pair (x s) F) z
  obtain ⟨u,hu⟩ := x_head s
  obtain ⟨p,hp⟩ := pal_start s
  have xForm : x s=pal s++b::[a] := (f_then_c s).symm
  have fForm : ∃ t,F=pal s++a::t := by
    change ∃ t, pal s ++ wordPow (x s) (j+1)=_
    rw [wordPow_succ',hu]
    exact ⟨_,rfl⟩
  obtain ⟨t,ft⟩ := fForm
  have zForm : ∃ t,z=b::t := ⟨_,rfl⟩
  obtain ⟨t',zt⟩ := zForm
  have xf : ¬Comparable (x s) F := by
    rw [xForm,ft]
    rintro (⟨u,e⟩ | ⟨u,e⟩) <;> simp [List.append_assoc,a,b] at e
  have xz : ¬Comparable (x s) z := by
    rw [hu,zt]; rintro (⟨u,e⟩ | ⟨u,e⟩) <;> simp [a,b] at e
  have fz : ¬Comparable F z := by
    rw [ft,hp,zt]; rintro (⟨u,e⟩ | ⟨u,e⟩) <;> simp [a,b] at e
  have separate (i j : Option Bool) : v i <+: v j → i=j := by
    rintro h
    rcases i with _ | (_ | _) <;> rcases j with _ | (_ | _) <;>
      first | rfl | exact (xf (Or.inl h)).elim | exact (xf (Or.inr h)).elim |
        exact (xz (Or.inl h)).elim | exact (xz (Or.inr h)).elim |
        exact (fz (Or.inl h)).elim | exact (fz (Or.inr h)).elim
  have inner : Completable v := by
    apply completable_prefix (v:=v) (fun i j e => separate i j (by rw [e]))
    · rintro (_ | (_ | _)) <;> simp [v,addToken,pair,zt,hu,ft]
    · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ pr
      exact congrArg v (separate i j pr)
  have middle : z ++ F=c ++ wordPow (x s) l := by
    change ((c++wordPow (x s) n)++c.reverse)++(pal s++wordPow (x s) (j+1))=_
    simp only [List.append_assoc,←List.append_assoc c.reverse (pal s),c_then_f]
    rw [←wordPow_succ' (x s) (j+1),←wordPow_add,exponent]
    congr 2; omega
  let padding (i : Option Bool) := if i=some true then List.replicate (k+1) (some false) ++ [none] else []
  have eqn : (fun i => spell v (padding i) ++ v i)=triple s k l z := by
    funext i
    rcases i with _ | (_ | _)
    · simp [v,padding,triple,addToken]
    · simp [v,padding,triple,addToken,pair]
    · simpa [padding,v,triple,addToken,pair,y,spell_replicate,List.append_assoc] using
        congrArg (wordPow (x s) (k+1) ++ ·) middle
  exact eqn ▸ inner.padLeft padding

/-- Proposition 7 for every third word ba x^n ab. The overlap exponent may
be zero, and s and both exponents of the prescribed second word are arbitrary. -/
theorem single_gap_completion (s k l n : ℕ) (code : NamedCode (triple s k l (single s n))) :
    Completable (triple s k l (single s n)) := by
  by_cases large : n+2<l+1
  · exact single_right_completion s k l n large
  by_cases left : n+2<k+1
  · exact flip_back (by rw [single_reverse]; exact single_right_completion s l k n left)
  exact (single_ambiguity s k l n (by omega) code).elim

theorem single_code_iff (s k l n : ℕ) :
    NamedCode (triple s k l (single s n)) ↔ n+2 < max (k+1) (l+1) := by
  constructor
  · intro code
    exact Nat.lt_of_not_ge (fun le => single_ambiguity s k l n le code)
  · intro h
    by_cases right : n+2<l+1
    · exact (single_right_completion s k l n right).1
    · have back : Completable (triple s l k (single s n).reverse) := by
        rw [single_reverse]
        exact single_right_completion s l k n (by omega)
      exact (flip_back back).1

end ThreeWordCodes.Palindromic
