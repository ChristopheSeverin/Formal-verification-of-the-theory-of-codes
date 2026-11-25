module

public import ThreeWordCodes.Realizations

/-! # Normalizing a binary letter realization, once one exists (Lemma 4) -/

@[expose] public section
namespace ThreeWordCodes
variable {A B : Type*}

def HasNoncommutingPair (v : Fin 3 → Word A) : Prop :=
  ∃ i j, v i ++ v j ≠ v j ++ v i

theorem HasNoncommutingPair.nonperiodic {v : Fin 3 → Word A} (h : HasNoncommutingPair v) :
    Nonperiodic v := by
  obtain ⟨i,j,ne⟩ := h
  rintro ⟨r,p⟩
  obtain ⟨k,hk⟩ := p i
  obtain ⟨l,hl⟩ := p j
  exact ne (by rw [hk,hl]; exact wordPow_comm ..)

theorem SameEquations.noncommutingPair {v : Fin 3 → Word A} {w : Fin 3 → Word B}
    (e : SameEquations v w) (h : HasNoncommutingPair v) : HasNoncommutingPair w := by
  obtain ⟨i,j,ne⟩ := h
  refine ⟨i,j,fun hc => ne ?_⟩
  simpa using (e [i,j] [j,i]).mpr (by simpa using hc)

private def admitsLetter (v : Fin 3 → Word Bool) : Prop := ∃ i b, v i = [b]
private def totalLength (v : Fin 3 → Word Bool) : ℕ := ∑ i, (v i).length
private def Shortest (v : Fin 3 → Word Bool) : Prop :=
  ∀ w, SameEquations v w → admitsLetter w → totalLength v ≤ totalLength w

private theorem shortest_exists {v : Fin 3 → Word A} (h : HasLetterRealization v) :
    ∃ d : Fin 3 → Word Bool, SameEquations v d ∧ admitsLetter d ∧ Shortest d := by
  classical
  let goal (n : ℕ) := ∃ d : Fin 3 → Word Bool, SameEquations v d ∧ admitsLetter d ∧ totalLength d = n
  have witness : ∃ n, goal n := by obtain ⟨d,e,l⟩ := h; exact ⟨_,d,e,l,rfl⟩
  obtain ⟨d,e,letter,sz⟩ := Nat.find_spec witness
  refine ⟨d,e,letter,fun p ep lp => ?_⟩
  rw [sz]
  exact Nat.find_min' witness ⟨p,e.trans ep,lp,rfl⟩

theorem coded_length {g : Bool → Word Bool} (ng : ∀ b, g b ≠ []) (s : Word Bool) :
    s.length ≤ (spell g s).length := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    have := List.length_pos_iff.mpr (ng b)
    simp only [spell_cons,List.length_append,List.length_cons]
    omega

theorem coded_length_strict {g : Bool → Word Bool} (ng : ∀ b, g b ≠ [])
    {b : Bool} (big : 1 < (g b).length) (s : Word Bool) (occurs : b ∈ s) :
    s.length < (spell g s).length := by
  induction s with
  | nil => simp at occurs
  | cons c s ih =>
    simp only [spell_cons,List.length_append,List.length_cons]
    rcases List.mem_cons.mp occurs with rfl | h
    · have := coded_length ng s
      omega
    · have := List.length_pos_iff.mpr (ng c)
      have := ih h
      omega

private theorem one_generator {g : Bool → Word Bool} (c : Bool) (s : Word Bool) (no : c ∉ s) :
    spell g s = wordPow (g (!c)) s.length := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    simp only [List.mem_cons,not_or] at no
    have hb : b = !c := by cases b <;> cases c <;> simp_all
    simp [wordPow_succ',hb,ih no.2]

private theorem left_normal {d : Fin 3 → Word Bool} (nz : ∀ i, d i ≠ [])
    (amb : ¬ NamedCode d) (np : Nonperiodic d) (letter : admitsLetter d) (min : Shortest d) :
    (∀ b : Bool, ∃ i, (d i).getLast? = some b) ∧
    (∀ (b : Bool) (m : ℕ), (∀ i, m ∣ (d i).count b) → m ∣ 1) := by
  classical
  obtain ⟨g,p,eqn,code,kernel,trace⟩ := traced_binary_realization d nz amb np
  have lengths (k : Fin 3) : (p k).length ≤ (d k).length := by
    rw [←congrFun eqn k]
    exact coded_length code.entry_ne_nil _
  have newLetter : admitsLetter p := by
    obtain ⟨k,b,word⟩ := letter
    have small := lengths k
    rw [word] at small
    have nempty : p k ≠ [] := fun hh => nz k (by rw [←congrFun eqn k,hh]; rfl)
    have := List.length_pos_iff.mpr nempty
    change (p k).length ≤ 1 at small
    obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp (show (p k).length=1 by omega)
    exact ⟨k,a,ha⟩
  have used (b : Bool) : ∃ k : Fin 3, b ∈ p k := by
    by_contra! no
    apply np
    exact ⟨g (!b),fun k => ⟨_,(congrFun eqn k).symm.trans (one_generator b (p k) (no k))⟩⟩
  have single (b : Bool) : ∃ a, g b = [a] := by
    apply List.length_eq_one_iff.mp
    have pos := List.length_pos_iff.mpr (code.entry_ne_nil b)
    by_contra ne
    obtain ⟨k,hk⟩ := used b
    have lt := coded_length_strict code.entry_ne_nil (show 1 < (g b).length by omega) _ hk
    rw [congrFun eqn k] at lt
    have total : totalLength p < totalLength d := Finset.sum_lt_sum
      (fun k _ => lengths k) ⟨k,Finset.mem_univ _,lt⟩
    exact Nat.not_lt_of_ge (min p kernel newLetter) total
  choose name spellName using single
  have inj : Function.Injective name := by
    intro b c he
    exact code.entries_injective (by rw [spellName b,spellName c,he])
  have cover := Finite.surjective_of_injective inj
  constructor
  · intro b
    obtain ⟨k,rfl⟩ := cover b
    obtain ⟨i,hi⟩ := trace.finals k
    exact ⟨i,by simpa [spellName] using hi.symm⟩
  · intro b m all
    obtain ⟨k,rfl⟩ := cover b
    have div := trace.divisors (fun w => w.count (name k)) (by simp) m all k
    simpa [spellName] using div

private theorem reverse_letter {v : Fin 3 → Word Bool} (h : admitsLetter v) :
    admitsLetter (fun i => (v i).reverse) := by
  obtain ⟨k,b,e⟩ := h
  exact ⟨k,b,by simp [e]⟩

/-- Normalize any available binary letter realization of an ambiguous nonperiodic
triple with a noncommuting pair. Both end letters occur in both directions. For
each letter, the three occurrence counts have no common divisor larger than one. -/
theorem normalize_letter_realization {v : Fin 3 → Word A} (nz : ∀ i, v i ≠ [])
    (amb : ¬ NamedCode v) (nc : HasNoncommutingPair v) (model : HasLetterRealization v) :
    ∃ d : Fin 3 → Word Bool, SameEquations v d ∧ (∃ i b, d i = [b]) ∧
      (∀ b : Bool, ∃ i, (d i).head? = some b) ∧
      (∀ b : Bool, ∃ i, (d i).getLast? = some b) ∧
      ∀ (b : Bool) (m : ℕ), (∀ i, m ∣ (d i).count b) → m ∣ 1 := by
  obtain ⟨d,e,letter,min⟩ := shortest_exists model
  have nzd (i : Fin 3) : d i ≠ [] := by
    intro he
    apply nz i
    simpa using (e [i] []).mpr (by simp [he])
  have ambd : ¬ NamedCode d := fun h => amb (e.namedCode_iff.mpr h)
  have ncd := e.noncommutingPair nc
  obtain ⟨finals,div⟩ := left_normal nzd ambd ncd.nonperiodic letter min
  let rev (k : Fin 3) := (d k).reverse
  have minRev : Shortest rev := by
    intro p eqns lp
    have same : SameEquations d (fun k => (p k).reverse) := by simpa [rev] using eqns.reverse
    simpa [totalLength,rev] using min _ same (reverse_letter lp)
  have ncRev : HasNoncommutingPair rev := by
    obtain ⟨i,j,une⟩ := ncd
    exact ⟨j,i,fun h => une (by simpa [rev] using congrArg List.reverse h)⟩
  have ambRev : ¬ NamedCode rev := fun h => ambd (by simpa [rev] using h.reverse)
  obtain ⟨heads,_⟩ := left_normal (d:=rev) (by simpa [rev] using nzd) ambRev ncRev.nonperiodic
    (reverse_letter letter) minRev
  exact ⟨d,e,letter,by simpa [rev] using heads,finals,div⟩

end ThreeWordCodes
