module

public import ThreeWordCodes.CrossedDifferences

/-! # Changing the distinguished letter and permuting tests -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)
variable {A : Type*}

theorem swap_first_two {p q z : Word A} (bad : ¬NamedCode (pieces p q z)) :
    ¬NamedCode (pieces q p z) := by
  let s (k : Option Bool) := k.map (!·)
  have eqn : (fun k => pieces q p z (s k))=pieces p q z := by
    funext k; rcases k with _|(_|_) <;> rfl
  exact fun h => bad (eqn ▸ h.reindex (f:=s) (by decide))

theorem reverse_pieces (p q z : Word A) :
    (fun k => (pieces p q z k).reverse)=pieces p.reverse q.reverse z.reverse := by
  funext k; rcases k with _|(_|_) <;> rfl

theorem reverse_ambiguity {p q z : Word A} (h : ¬NamedCode (pieces p q z)) :
    ¬NamedCode (pieces p.reverse q.reverse z.reverse) := by
  intro hc
  have rev := hc.reverse
  rw [reverse_pieces] at rev
  exact h (by simpa using rev)

theorem Model.flip {r t u v} (m : Model r t u v) (c : Bool) (unit : ∃ k,pieces t u v k=[c]) :
    Model r (t.map (letterFlip c)) (u.map (letterFlip c)) (v.map (letterFlip c)) := by
  let f := letterFlip c
  let g := pieces t u v
  let h := pieces (t.map f) (u.map f) (v.map f)
  have shape (k : Option Bool) : h k=(g k).map f := by rcases k with _|(_|_) <;> rfl
  have inj : Function.Injective f := Function.LeftInverse.injective (letterFlip_twice c)
  have oi : Function.Injective (Option.map f) := Option.map_injective inj
  have full : crossedWords r (t.map f) (u.map f) (v.map f)=(fun k => (crossedWords r t u v k).map f) := by
    funext k; cases r <;> rcases k with _|(_|_) <;> simp [crossedWords,pair,addToken]
  have cut (b : Bool) : crossedShortening r b (t.map f) (u.map f) (v.map f)=
      (fun k => (crossedShortening r b t u v k).map f) := by
    funext k; cases r <;> cases b <;> rcases k with _|(_|_) <;> simp [crossedShortening,pair,addToken]
  obtain ⟨k,one⟩ := unit
  refine ⟨?_,⟨k,?_⟩,?_,?_,?_,?_,?_,full ▸ (named_flip_iff _ c).mpr m.code,?_⟩
  · intro i; change h i≠[]
    rw [shape]
    simpa using m.nonempty i
  · change h k=[false]
    change g k=[c] at one
    rw [shape,one]; cases c <;> rfl
  · intro d n all
    apply m.divisors (f d) n
    intro i
    have count := List.count_map_of_injective (g i) f inj (f d)
    have id : f (f d)=d := letterFlip_twice c d
    rw [id] at count
    have key : n∣(h i).count d := all i
    rwa [shape,count] at key
  · change (h _).head?≠(h _).head?
    intro eqn
    simp only [shape,List.head?_map] at eqn
    exact m.first (oi eqn)
  · change (h _).getLast?≠(h _).getLast?
    intro eqn
    simp only [shape,List.getLast?_map] at eqn
    exact m.last (oi eqn)
  · intro i j ne eqn
    change h i++h j=h j++h i at eqn
    simp only [shape,←List.map_append] at eqn
    exact m.noncommuting i j ne (List.map_injective_iff.mpr inj eqn)
  · intro code
    change NamedCode h at code
    exact m.ambiguous ((named_flip_iff g c).mp ((funext shape) ▸ code))
  · intro b code
    exact m.cuts b ((named_flip_iff _ c).mp (cut b ▸ code))

theorem intermediate_b (u v : Word Bool) (m : Model .intermediate [b] u v) : False :=
  intermediate_central _ _ (m.flip b ⟨P,rfl⟩)

/-- Once rows I and III are excluded, only lateral instances of II and row IV remain. -/
theorem two_crossed_rows_suffice.{u}
    (rowII : ∀ t u v,t≠[a] → ¬Model .intermediate t u v)
    (rowIV : ∀ t u v,¬Model .overlap t u v) : ThreeWordTheorem.{u} :=
  three_crossed_rows_suffice (fun t u v _ => shared_impossible t u v) rowII rowIV

end ThreeWordCodes.CrossedCase
