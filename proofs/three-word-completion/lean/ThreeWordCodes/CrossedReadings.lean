module

public import ThreeWordCodes.CrossedJoined

/-! # Finishing a prefix at b in the two readings ba and aba -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

abbrev abReaders := pair [b,a] [a,b,a]

/-- Every prefix of a product on ba and aba that ends in b is exactly one
letter short of a complete product. -/
theorem finish_at_b (w : Word Bool) (s : Word Bool) (read : w <+: spell abReaders s)
    (last : w.getLast?=some b) : ∃ p,spell abReaders p=w++[a] := by
  induction s generalizing w with
  | nil => have empty : w=[] := List.prefix_nil.mp read; simp [empty] at last
  | cons k s ih =>
    have first : abReaders k <+: spell abReaders (k::s) := List.prefix_append ..
    rcases List.prefix_or_prefix_of_prefix read first with short|long
    · have possible : ∀ i : Bool,∀ p∈(abReaders i).inits,p.getLast?=some b → abReaders i=p++[a] := by decide
      exact ⟨[k],by simpa using possible k w ((List.mem_inits ..).mpr short) last⟩
    · obtain ⟨t,eqn⟩ := long
      have nz : t≠[] := by
        rintro rfl
        have endA : (abReaders k).getLast?=some a := by cases k <;> rfl
        simp only [←eqn,List.append_nil,endA] at last
        contradiction
      have step : t <+: spell abReaders s := (List.prefix_append_right_inj _).mp (eqn ▸ read)
      have tailEnd : t.getLast?=some b := by rw [←eqn,append_last nz] at last; exact last
      obtain ⟨p,whole⟩ := ih t step tailEnd
      exact ⟨k::p,by rw [spell_cons,whole,←eqn,List.append_assoc]⟩

theorem read_after_b (w : Word Bool) (last : w.getLast?=some b)
    (amb : ¬NamedCode (pieces [b,a] [a,b,a] w)) : ∃ s,spell abReaders s=w++[a] := by
  have nz : ∀ i,abReaders i≠[] := by decide
  have marks : Function.Injective (fun i => (abReaders i).head?) := by decide
  obtain ⟨hi,hp⟩ := Border.marked_facts abReaders nz marks
  obtain ⟨s,r⟩ := prefix_of_products_of_ambiguity hi nz hp w amb
  exact finish_at_b w s r last

theorem read_before_b (w : Word Bool) (head : w.head?=some b)
    (amb : ¬NamedCode (pieces [a,b] [a,b,a] w)) : ∃ s,spell (pair [a,b] [a,b,a]) s=[a]++w := by
  have reverseWords : (fun k => (pieces [b,a] [a,b,a] w.reverse k).reverse)=pieces [a,b] [a,b,a] w := by
    funext k; rcases k with _|(_|_) <;> simp [pieces,pair,addToken]
  have fail : ¬NamedCode (pieces [b,a] [a,b,a] w.reverse) := fun h => amb (reverseWords ▸ h.reverse)
  obtain ⟨s,eqn⟩ := read_after_b w.reverse (by simpa using head) fail
  have back : (fun k => (abReaders k).reverse)=pair [a,b] [a,b,a] := by funext k; cases k <;> rfl
  exact ⟨s.reverse,by rw [←back,spell_reverse,List.reverse_reverse,eqn]; simp⟩

theorem spelled_old {A : Type*} (p q z : Word A) (s : Word Bool) :
    spell (pieces p q z) (s.map some)=spell (pair p q) s := by
  have e : (fun i => pieces p q z (some i))=pair p q := rfl
  rw [←spell_rename (pieces p q z) some,e]

private theorem spaced_after_run (c d : ℕ) (w : Word Bool) (n : ℕ) :
    Spaced c d (w++run n) ↔ Spaced c d w := by
  induction w generalizing d with
  | nil =>
    have base (r : ℕ) (t : ℕ) : Spaced c t (run r) := by
      induction r generalizing t with
      | zero => trivial
      | succ r ih => exact ih (t-1)
    exact ⟨fun _ => trivial,fun _ => base n d⟩
  | cons x w ih => cases x <;> simp only [List.cons_append,Spaced,ih]

/-- Appending b to the third word does not change the ambiguity test for
the names b, ba. This also covers words without any a. -/
theorem append_b_preserves_test (w : Word Bool) :
    ¬NamedCode (pieces [b] [b,a] (w++[b])) ↔ ¬NamedCode (pieces [b] [b,a] w) := by
  let f := letterFlip true
  have flip (z : Word Bool) : NamedCode (pieces [b] [b,a] z) ↔ NamedCode (pieces [a] [a,b] (z.map f)) := by
    have e : (fun k => (pieces [b] [b,a] z k).map f)=pieces [a] [a,b] (z.map f) := by
      funext k; rcases k with _|(_|_) <;> rfl
    exact (named_flip_iff (pieces [b] [b,a] z) true).symm.trans (e ▸ Iff.rfl)
  rw [flip,flip]
  change (¬NamedCode (addToken (pair [a] (run 1++[b])) ((w++[b]).map f))) ↔
     ¬NamedCode (addToken (pair [a] (run 1++[b])) (w.map f))
  rw [ambiguity_left_margin,ambiguity_left_margin,List.map_append]
  exact spaced_after_run 1 0 _ 1

end ThreeWordCodes.CrossedCase
