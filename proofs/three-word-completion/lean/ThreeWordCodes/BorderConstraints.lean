module

public import ThreeWordCodes.BorderEnds

/-! # Equations and ambiguity in the binary model of a bordered triple -/

@[expose] public section
namespace ThreeWordCodes.Border
variable {A B I : Type*}

/-- False removes the full left end power of x. True removes the right end power. -/
def endCut (right : Bool) (p q z : Word A) (n i j : ℕ) : Option Bool → Word A :=
  let x := short p q n
  let r := if right then wordPow x i++(p++q) else (q++p)++wordPow x j
  addToken (pair x r) z

theorem shift_inside (p q : Word A) (n i j : ℕ) :
    let x := short p q n
    wordPow x i++(p++q)++wordPow x (j+1)=wordPow x (i+1)++(q++p)++wordPow x j := by
  intro x
  rw [wordPow_succ' x j,wordPow_succ x i]
  simpa only [List.append_assoc] using congrArg (fun w => wordPow x i++w++wordPow x j)
    (short_shift p q n).symm

theorem end_cuts_ambiguous {f : Fin 3 → Word Bool} (input : ClassificationInput f) (bad : ¬Completable f)
    (p q z : Word Bool) (n i j : ℕ) (order : Option Bool ≃ Fin 3)
    (form : (fun k => f (order k))=family p q z n i j) (right : Bool) :
    ¬NamedCode (endCut right p q z n i j) := by
  let x := short p q n
  have code : NamedCode (family p q z n i j) := form ▸ input.code.reindex order.injective
  have pos : 0<x.length := List.length_pos_iff.mpr (code.entry_ne_nil (some false))
  have strict : (endCut right p q z n i j (some true)).length < (f (order (some true))).length := by
    rw [congrFun form (some true)]
    cases right with
    | false =>
      change ((q++p)++wordPow x j).length < (wordPow x (i+1)++(q++p)++wordPow x j).length
      rw [wordPow_succ']; simp only [List.length_append]; omega
    | true =>
      change (wordPow x i++(p++q)).length < (wordPow x (i+1)++(q++p)++wordPow x j).length
      rw [wordPow_succ x i]; simp only [List.length_append]; omega
  have le (t : Option Bool) : (endCut right p q z n i j t).length ≤ (f (order t)).length := by
    rcases t with _ | (_|_)
    · rw [congrFun form none]; rfl
    · rw [congrFun form (some false)]; rfl
    · exact strict.le
  intro coded
  have small := shorter_named input order _ le ⟨some true,strict⟩ coded
  apply bad
  apply (completable_reindex_iff f order).mp
  rw [form]
  cases right with
  | false =>
    have done := surround x ((q++p)++wordPow x j) z (i+1) 0 small
    simpa only [family,←show short p q n=x from rfl,wordPow_zero,List.append_nil,List.append_assoc] using done
  | true =>
    have done := surround x (wordPow x i++(p++q)) z 0 (j+1) small
    simpa only [family,x,wordPow_zero,List.nil_append,shift_inside p q n i j] using done

abbrev pieces (p q z : Word A) := addToken (pair p q) z

def P : Option Bool := some false
def Q : Option Bool := some true
def Z : Option Bool := none

theorem spell_cut (g : I → Word A) (s : Cut) (p q z : Word I) (n : ℕ) :
    (fun t => spell g (cutWords s p q z n t))=cutWords s (spell g p) (spell g q) (spell g z) n := by
  funext t
  cases s <;> rcases t with _ | (_|_) <;> simp [cutWords,short,addToken,pair,spell_wordPow]

theorem spell_endCut (g : I → Word A) (b : Bool) (p q z : Word I) (n i j : ℕ) :
    (fun t => spell g (endCut b p q z n i j t))=endCut b (spell g p) (spell g q) (spell g z) n i j := by
  funext t
  cases b <;> rcases t with _ | (_|_) <;> simp [endCut,short,addToken,pair,spell_wordPow]

theorem transfer_family {p q z : Word A} {u v w : Word B}
    (rel : SameEquations (pieces p q z) (pieces u v w)) (n i j : ℕ) :
    SameEquations (family p q z n i j) (family u v w n i j) := by
  simpa only [spell_family,spell_cons,spell_nil,List.append_nil,pieces,addToken,pair,P,Q,Z] using
    rel.substitution (family [P] [Q] [Z] n i j)

theorem transfer_cut {p q z : Word A} {u v w : Word B} (rel : SameEquations (pieces p q z) (pieces u v w))
    (s : Cut) (n : ℕ) : SameEquations (cutWords s p q z n) (cutWords s u v w n) := by
  simpa only [spell_cut,spell_cons,spell_nil,List.append_nil,pieces,addToken,pair,P,Q,Z] using
    rel.substitution (cutWords s [P] [Q] [Z] n)

theorem transfer_endCut {p q z : Word A} {u v w : Word B} (rel : SameEquations (pieces p q z) (pieces u v w))
    (b : Bool) (n i j : ℕ) : SameEquations (endCut b p q z n i j) (endCut b u v w n i j) := by
  simpa only [spell_endCut,spell_cons,spell_nil,List.append_nil,pieces,addToken,pair,P,Q,Z] using
    rel.substitution (endCut b [P] [Q] [Z] n i j)

theorem transfer_reading {g : I → Word A} {h : I → Word B} (rel : SameEquations g h) (a b c : I) (s : Word Bool) :
    spell (pair (g a) (g b)) s=g c ↔ spell (pair (h a) (h b)) s=h c := by
  let names (i : Bool) := if i then b else a
  have eqG : (fun k => g (names k))=pair (g a) (g b) := by funext k; cases k <;> rfl
  have eqH : (fun k => h (names k))=pair (h a) (h b) := by funext k; cases k <;> rfl
  rw [←eqG,←eqH,spell_rename g names s,spell_rename h names s]
  simpa only [spell_cons,spell_nil,List.append_nil] using rel (s.map names) [c]

theorem transfer_commuting {p q z : Word A} {u v w : Word B} (rel : SameEquations (pieces p q z) (pieces u v w))
    (m : ℕ) :
    (q++p)++(wordPow z m++p)=(wordPow z m++p)++(q++p) ↔
    (v++u)++(wordPow w m++u)=(wordPow w m++u)++(v++u) := by
  simpa [spell_replicate,P,Q,Z,pieces,addToken,pair,List.append_assoc] using
    rel ([Q,P]++List.replicate m Z++[P]) (List.replicate m Z++[P,Q,P])

/-- Conditions on the actual words that survive passage to the three
letter-entry cases in Section 4. Each field speaks only about words,
parsings, ends or marker counts in the model. -/
structure Model (p q z : Word Bool) (n i j : ℕ) : Prop where
  nonempty : ∀ k,pieces p q z k≠[]
  letter : ∃ k,pieces p q z k=[false]
  first : p.head?≠z.head? ∧ q.head?=z.head?
  last : p.getLast?≠z.getLast? ∧ q.getLast?=z.getLast?
  divisors : ∀ b m,(∀ k,m ∣ (pieces p q z k).count b) → m ∣ 1
  code : NamedCode (family p q z n i j)
  cuts : ∀ s,¬NamedCode (cutWords s p q z n)
  endCuts : ∀ b,¬NamedCode (endCut b p q z n i j)
  noThirdReading : ¬∃ w,spell (pair p q) w=z
  noSecondReading : ¬∃ w,spell (pair p z) w=q
  noncommuting : q++z≠z++q
  forbidden : ∀ e,(q++p)++(wordPow z (e+1)++p)≠(wordPow z (e+1)++p)++(q++p)

private theorem binary_reading {p q : Word Bool} (hp : p.length=1) (hq : q.length=1)
    (ne : p.head?≠q.head?) (w : Word Bool) : ∃ v,spell (pair p q) v=w := by
  obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hp
  obtain ⟨b,rfl⟩ := List.length_eq_one_iff.mp hq
  have covers (c : Bool) : ∃ k,pair [a] [b] k=[c] := by cases a <;> cases b <;> cases c <;> first | contradiction | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩
  induction w with
  | nil => exact ⟨[],rfl⟩
  | cons c w ih =>
    obtain ⟨k,word⟩ := covers c
    obtain ⟨v,rfl⟩ := ih
    exact ⟨k::v,by simp [word]⟩

/-- Exactly one of the three named model words is a single letter. -/
theorem Model.unique_letter {p q z : Word Bool} {n i j : ℕ} (m : Model p q z n i j) :
    ∃! k,(pieces p q z k).length=1 := by
  have pq : ¬(p.length=1 ∧ q.length=1) := fun ⟨a,b⟩ =>
    m.noThirdReading (binary_reading a b (m.first.2.symm ▸ m.first.1) z)
  have pz : ¬(p.length=1 ∧ z.length=1) := fun ⟨a,b⟩ => m.noSecondReading (binary_reading a b m.first.1 q)
  have qz : ¬(q.length=1 ∧ z.length=1) := by
    rintro ⟨a,b⟩
    obtain ⟨c,ec⟩ := List.length_eq_one_iff.mp a
    obtain ⟨d,ed⟩ := List.length_eq_one_iff.mp b
    have same : c=d := by simpa [ec,ed] using m.first.2
    exact m.noncommuting (by rw [ec,ed,same])
  obtain ⟨k,letter⟩ := m.letter
  have len := congrArg List.length letter
  refine ⟨k,len,?_⟩
  rintro t ht
  rcases k with _ | (_|_) <;> rcases t with _ | (_|_)
  all_goals first | rfl | exact (pq ⟨ht,len⟩).elim | exact (pq ⟨len,ht⟩).elim |
    exact (pz ⟨ht,len⟩).elim | exact (pz ⟨len,ht⟩).elim | exact (qz ⟨ht,len⟩).elim | exact (qz ⟨len,ht⟩).elim

end ThreeWordCodes.Border
