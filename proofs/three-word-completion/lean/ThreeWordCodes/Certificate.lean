module

public import ThreeWordCodes.Series
public import ThreeWordCodes.Names
public import ThreeWordCodes.Kraft
public import Mathlib.Data.Set.Finite.Lattice

/-! # From positive coefficients to a finite maximal code (Lemma 1)

The coefficient one identifies the cuts at both flanks and at every codeword.
A separate induction on word length constructs the factorization.
-/

@[expose] public section
namespace ThreeWordCodes
open WordSeries
open scoped ThreeWordCodes.WordSeries
variable {A : Type*}

/-- The finite set consists exactly of the words with positive coefficient. -/
def Supports (c : Series A) (S : Finset (Word A)) : Prop :=
  ∀ w, w ∈ S ↔ 0 < c w

private theorem center_bound {p q f : Series A} (hp : p [] = 1) (hq : q [] = 1)
    (allWords : (q ⋆ (kleene f ⋆ p)) = fun _ => 1) (w : Word A) :
    (kleene f ⋆ p) w ≤ 1 ∧ kleene f w ≤ 1 := by
  have r := cut_le q (kleene f ⋆ p) [] w
  have l := cut_le (kleene f) p w []
  simp [allWords, hq] at r
  simp [hp] at l
  exact ⟨r, l.trans r⟩

/-- All three input polynomials have coefficients at most one. -/
theorem certificate_coefficients {p q f : Series A} (hp : p [] = 1) (hq : q [] = 1)
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q)) (w : Word A) :
    p w ≤ 1 ∧ q w ≤ 1 ∧ f w ≤ 1 := by
  have allWords := certificate_series hp hq cert
  have bounds := center_bound hp hq allWords w
  have pl := cut_le (kleene f) p [] w
  have qr := cut_le q (kleene f ⋆ p) w []
  have fr := cut_le f (kleene f) w []
  have star := congrFun (kleene_unfold (proper_of_certificate hp hq cert)) w
  simp [allWords, hp] at pl qr fr
  simp only [Pi.add_apply] at star
  exact ⟨pl.trans bounds.1, qr, by omega⟩

private theorem star_positive {f : Series A} {M : Finset (Word A)}
    (proper : f [] = 0) (hm : Supports f M) (s : List (↥M)) :
    0 < kleene f (concatenate s) := by
  induction s with
  | nil => exact Nat.zero_lt_one
  | cons c s ih =>
    have cut := (conv_pos (f := f) (g := kleene f)).mpr
      ⟨c.val, concatenate s, rfl, (hm _).mp c.property, ih⟩
    have eqn := congrFun (kleene_unfold proper) (c.val ++ concatenate s)
    change 0 < kleene f (c.val ++ concatenate s)
    simp only [Pi.add_apply] at eqn
    omega

private theorem star_parses {f : Series A} {M : Finset (Word A)}
    (proper : f [] = 0) (hm : Supports f M) (w : Word A) (hw : 0 < kleene f w) :
    ∃ s : List (↥M), concatenate s = w := by
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    cases w with
    | nil => exact ⟨[], rfl⟩
    | cons a w =>
      have h := congrFun (kleene_unfold proper) (a :: w)
      change kleene f (a :: w) = 0 + (f ⋆ kleene f) (a :: w) at h
      obtain ⟨u, v, e, hu, hv⟩ := conv_pos.mp (show 0 < (f ⋆ kleene f) (a :: w) by omega)
      have un : u ≠ [] := by rintro rfl; omega
      have lens := congrArg List.length e
      simp only [List.length_append, List.length_cons] at lens len
      have upl := List.length_pos_iff.mpr un
      obtain ⟨s, hs⟩ := ih v.length (by omega) v hv rfl
      exact ⟨⟨u, (hm _).mpr hu⟩ :: s, by simpa [concatenate] using (congrArg (u ++ ·) hs).trans e⟩

private theorem star_injective {f : Series A} {M : Finset (Word A)}
    (proper : f [] = 0) (hm : Supports f M) (hb : ∀ w, kleene f w ≤ 1) :
    Function.Injective (concatenate (M := M)) := by
  have nonempty (c : ↥M) : c.val ≠ [] := by
    have := (hm _).mp c.property
    intro h
    simp [h, proper] at this
  intro s
  induction s with
  | nil =>
    intro t ht
    cases t with
    | nil => rfl
    | cons d t => exact (nonempty d (List.append_eq_nil_iff.mp ht.symm).1).elim
  | cons c s ih =>
    intro t ht
    cases t with
    | nil => exact (nonempty c (List.append_eq_nil_iff.mp ht).1).elim
    | cons d t =>
      have he := congrFun (kleene_unfold proper) (c.val ++ concatenate s)
      have hh := hb (c.val ++ concatenate s)
      simp only [Pi.add_apply] at he
      obtain ⟨hcd, hst⟩ := cut_unique (f := f) (g := kleene f)
        (show c.val ++ concatenate s = d.val ++ concatenate t from ht)
        (by omega) ((hm _).mp c.property) (star_positive proper hm s)
        ((hm _).mp d.property) (star_positive proper hm t)
      exact List.cons.injEq .. |>.mpr ⟨Subtype.ext hcd, ih hst⟩

theorem positiveFactorization_code {M P Q : Finset (Word A)} (hf : PositiveFactorization M P Q) :
    InformationTheory.IsUniquelyDecodable (M : Set (Word A)) := by
  obtain ⟨⟨l, s, r⟩, _⟩ := hf.2 []
  have hc : NamedCode (fun x : ↥M => x.val) := by
    intro x y he
    have hc : concatenate x = concatenate y := by simpa [concatenate, spell, List.flatMap_def] using he
    have hargs := hf.1 (a₁ := (l, x, r)) (a₂ := (l, y, r)) (by simp [assemble, hc])
    exact congrArg (fun z : ↥Q × List (↥M) × ↥P => z.2.1) hargs
  simpa using ((namedCode_iff_range _).mp hc).2

/-- Given its three supports, the coefficient certificate yields bijective parsing. -/
theorem factorization_of_certificate {p q f : Series A} {M P Q : Finset (Word A)}
    (hp : p [] = 1) (hq : q [] = 1)
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q))
    (hm : Supports f M) (hP : Supports p P) (hQ : Supports q Q) :
    PositiveFactorization M P Q := by
  have proper := proper_of_certificate hp hq cert
  have allWords := certificate_series hp hq cert
  have bounds := center_bound hp hq allWords
  constructor
  · rintro ⟨l, s, r⟩ ⟨l', s', r'⟩ he
    have cut (b : List (↥M)) (e : ↥P) : 0 < (kleene f ⋆ p) (concatenate b ++ e.val) :=
      conv_pos.mpr ⟨_, _, rfl, star_positive proper hm b, (hP _).mp e.property⟩
    have he' : l.val ++ (concatenate s ++ r.val) = l'.val ++ (concatenate s' ++ r'.val) := by
      simpa [assemble, List.append_assoc] using he
    obtain ⟨hl, ht⟩ := cut_unique he' (by rw [allWords])
      ((hQ _).mp l.property) (cut s r) ((hQ _).mp l'.property) (cut s' r')
    obtain ⟨hs, hr⟩ := cut_unique ht (bounds _).1 (star_positive proper hm s)
      ((hP _).mp r.property) (star_positive proper hm s') ((hP _).mp r'.property)
    obtain rfl : l = l' := Subtype.ext hl
    obtain rfl : r = r' := Subtype.ext hr
    obtain rfl := star_injective proper hm (fun w => (bounds w).2) hs
    rfl
  · intro w
    obtain ⟨l, t, e, hl, ht⟩ := conv_pos.mp (show 0 < (q ⋆ (kleene f ⋆ p)) w by rw [allWords]; exact Nat.zero_lt_one)
    obtain ⟨b, r, e', hb, hr⟩ := conv_pos.mp ht
    obtain ⟨s, hs⟩ := star_parses proper hm b hb
    exact ⟨(⟨l, (hQ _).mpr hl⟩, s, ⟨r, (hP _).mpr hr⟩), by simp [assemble, hs, List.append_assoc, e', e]⟩

private theorem finite_support_of_cert {p q f : Series A} [Fintype A]
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q))
    (hP : Set.Finite {w | 0 < p w}) (hQ : Set.Finite {w | 0 < q w}) :
    Set.Finite {w | 0 < f w} := by
  classical
  let side := ((hP.prod (Set.finite_univ (α := A))).image
    (fun z : Word A × A => z.1 ++ [z.2]))
  apply ((side.prod hQ).image (fun z : Word A × Word A => z.1 ++ z.2)
    |>.insert []).subset
  intro w hw
  by_cases nil : w = []
  · exact Or.inl nil
  · apply Set.mem_insert_of_mem
    have h := congrFun cert w
    have z : epsilon w = 0 := by cases w <;> simp_all [epsilon]
    simp only [Pi.add_apply, z, Nat.zero_add] at h
    obtain ⟨v, r, rfl, hv, hr⟩ := conv_pos.mp (show 0 < ((p ⋆ letters) ⋆ q) w by
      change 0 < f w at hw; omega)
    obtain ⟨u, t, rfl, hu, ht⟩ := conv_pos.mp hv
    have single : ∃ a : A, t = [a] := by
      cases t with
      | nil => simp [letters] at ht
      | cons a t => cases t <;> simp_all [letters, epsilon]
    obtain ⟨a, rfl⟩ := single
    exact ⟨(u ++ [a], r), ⟨⟨(u, a), ⟨hu, Set.mem_univ _⟩, rfl⟩, hr⟩, rfl⟩

/-- Lemma 1, with arbitrary natural multiplicities in the finite input polynomials.
The order of the flanks in the parsed word is Q, then M*, then P. -/
theorem certificate_completion [Fintype A] [Nonempty A] {p q f : Series A}
    (hp : p [] = 1) (hq : q [] = 1)
    (hP : Set.Finite {w | 0 < p w}) (hQ : Set.Finite {w | 0 < q w})
    (cert : f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q)) :
    ∃ M P Q : Finset (Word A), Supports f M ∧ Supports p P ∧ Supports q Q ∧
      IsMaximalCode (M : Set (Word A)) ∧ PositiveFactorization M P Q := by
  classical
  have hM := finite_support_of_cert cert hP hQ
  have supports (s : Series A) (hs : Set.Finite {w | 0 < s w}) : Supports s hs.toFinset :=
    fun _ => hs.mem_toFinset
  have hf := factorization_of_certificate hp hq cert (supports f hM) (supports p hP) (supports q hQ)
  exact ⟨_, _, _, supports f hM, supports p hP, supports q hQ,
    maximal_of_finite_flanks _ _ _ (positiveFactorization_code hf) hf.2, hf⟩

/-- A polynomial certificate containing the prescribed words. All input multiplicities
are natural numbers, and finiteness of the output follows from the identity. -/
def HasFiniteCertificate (X : Set (Word A)) : Prop :=
  ∃ p q f : Series A, p [] = 1 ∧ q [] = 1 ∧ Set.Finite {w | 0 < p w} ∧
    Set.Finite {w | 0 < q w} ∧ f + (p ⋆ q) = epsilon + ((p ⋆ letters) ⋆ q) ∧
    ∀ w ∈ X, 0 < f w

theorem HasFiniteCertificate.mono {X Y : Set (Word A)} (h : HasFiniteCertificate Y) (sub : X ⊆ Y) :
    HasFiniteCertificate X := by
  obtain ⟨p,q,f,hp,hq,fp,fq,eqn,supp⟩ := h
  exact ⟨p,q,f,hp,hq,fp,fq,eqn,fun w hw => supp w (sub hw)⟩

theorem HasFiniteCertificate.toPositive [Fintype A] [Nonempty A] {X : Set (Word A)}
    (h : HasFiniteCertificate X) : HasPositiveCompletion X := by
  obtain ⟨p,q,f,hp,hq,fp,fq,eqn,sub⟩ := h
  obtain ⟨M,P,Q,supp,_,_,hm,hf⟩ := certificate_completion hp hq fp fq eqn
  exact ⟨M,Q,P,fun w hw => (supp w).mpr (sub w hw),hm,hf⟩

end ThreeWordCodes
