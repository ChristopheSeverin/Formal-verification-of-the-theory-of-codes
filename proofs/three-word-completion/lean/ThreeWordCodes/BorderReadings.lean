module

public import ThreeWordCodes.BorderWords
public import ThreeWordCodes.PalindromicTheorem

/-! # Reading the pieces of a bordered triple -/

@[expose] public section
namespace ThreeWordCodes.Border
variable {A B : Type*}

def short (p q : Word A) (n : ℕ) := p ++ wordPow (q++p) n

def family (p q z : Word A) (n i j : ℕ) : Option Bool → Word A :=
  let x := short p q n
  addToken (pair x (wordPow x (i+1) ++ (q++p) ++ wordPow x j)) z

theorem Form.words {x y : Word A} (f : Form x y) (z : Word A) :
    family f.p f.q z f.n f.i f.j = addToken (pair x y) z := by
  have eqn : short f.p f.q f.n=x := f.short_word.symm
  funext k
  rcases k with _ | (_ | _) <;> simp [family,eqn,addToken,pair,←f.long_word]

theorem spell_family (g : B → Word A) (p q z : Word B) (n i j : ℕ) :
    (fun t => spell g (family p q z n i j t)) = family (spell g p) (spell g q) (spell g z) n i j := by
  funext t
  rcases t with _ | (_ | _) <;> simp [family,short,addToken,pair,spell_wordPow]

/-- On two single letters a zero exponent gives Proposition 6. Every positive
exponent gives the alternating palindrome of Proposition 7. -/
theorem letter_family (n i j : ℕ) (w : Word Bool)
    (code : NamedCode (family [false] [true] w n i j)) : Completable (family [false] [true] w n i j) := by
  cases n with
  | zero => exact named_pure_power_completion threeOrder code ⟨some false,false,1,rfl⟩
  | succ s =>
    have base : short [false] [true] (s+1)=Palindromic.x s := (rotate_power [false] [true] (s+1)).symm
    have eqn : family [false] [true] w (s+1) i j=Palindromic.triple s i j w := by
      funext t
      rcases t with _ | (_ | _) <;> simp [family,Palindromic.triple,Palindromic.y,Palindromic.c,addToken,pair,base]
    exact eqn.symm ▸ Palindromic.proposition_seven s i j w (eqn ▸ code)

/-- A third word reading on p and q has a completion over the original alphabet. -/
theorem third_on_pieces [Fintype A] (p q z : Word A) (n i j : ℕ)
    (code : NamedCode (family p q z n i j)) (read : ∃ w,spell (pair p q) w=z) :
    Completable (family p q z n i j) := by
  obtain ⟨w,rfl⟩ := read
  let g := pair p q
  let d := family [false] [true] w n i j
  have eqn : (fun t => spell g (d t))=family p q (spell (pair p q) w) n i j := by
    simpa [g,d,pair] using spell_family g [false] [true] w n i j
  have actual := eqn.symm ▸ code
  have base := pair_basis_of_coded_reading g d actual
  exact eqn ▸ base.substitute (letter_family n i j w ((base.1.preserves_equations d).namedCode_iff.mpr actual))

private theorem third_power_reading [Fintype A] (g : Bool → Word A) (P Q : Word Bool) (b : Bool)
    (m n i j : ℕ) (code : NamedCode (family (spell g P) (spell g Q) (wordPow (g b) m) n i j)) :
    Completable (family (spell g P) (spell g Q) (wordPow (g b) m) n i j) := by
  let d := family P Q (List.replicate m b) n i j
  have eqn := spell_family g P Q (List.replicate m b) n i j
  rw [spell_replicate] at eqn
  have actual := eqn.symm ▸ code
  have base := pair_basis_of_coded_reading g d actual
  exact pure_reading_completion threeOrder base d eqn code ⟨none,b,m,rfl⟩

/-- If q reads on p and z, the third word is itself a letter after decoding. -/
theorem second_on_others [Fintype A] (p q z : Word A) (n i j : ℕ)
    (code : NamedCode (family p q z n i j)) (read : ∃ w,spell (pair p z) w=q) :
    Completable (family p q z n i j) := by
  obtain ⟨w,rfl⟩ := read
  let g := pair p z
  exact (by simpa [g,pair] using third_power_reading g [false] w true 1 n i j :
    NamedCode (family p (spell (pair p z) w) z n i j) → _) code

/-- A commuting pair q,z puts the third entry on a pure-power letter in the
reading on p and their common root. -/
theorem commuting_second_third [Fintype A] (p q z : Word A) (n i j : ℕ)
    (code : NamedCode (family p q z n i j)) (comm : q++z=z++q) : Completable (family p q z n i j) := by
  obtain ⟨r,h,m,rfl,rfl⟩ := (commuting_iff_common_power q z).mp comm
  let g := pair p r
  have done := third_power_reading g [false] (List.replicate h true) true m n i j
  exact (by simpa [g,spell_replicate,pair] using done :
    NamedCode (family p (wordPow r h) (wordPow r m) n i j) → _) code

/-- A completable triple of pieces can be substituted into the name-level
family, whose third entry is the private letter. -/
theorem of_completable_pieces [Fintype A] (p q z : Word A) (n i j : ℕ)
    (code : NamedCode (family p q z n i j)) (base : Completable (addToken (pair p q) z)) :
    Completable (family p q z n i j) := by
  let g := addToken (pair p q) z
  let d := family [some false] [some true] [none] n i j
  have eqn : (fun t => spell g (d t))=family p q z n i j := by
    simpa [d,g,addToken,pair] using spell_family g [some false] [some true] [none] n i j
  exact pure_reading_completion threeOrder base d eqn code ⟨none,none,1,rfl⟩

end ThreeWordCodes.Border
