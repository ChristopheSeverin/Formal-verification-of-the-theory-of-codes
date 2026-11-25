module

public import ThreeWordCodes.LengtheningMargins
public import ThreeWordCodes.Powers

/-! # A large gap locates the marked bodies

Record one bit for each marker, indicating whether the gap after it is large.
The last bit is false. If boundary gaps are small this signature concatenates
on products. The two body signatures form a code when one contains a true bit
and the other has only a single false bit.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def flag (k : ℕ) (z : ℕ) : Bool := decide (k<z)
private def signature (k : ℕ) (gs : List ℕ) := gs.map (flag k) ++ [false]

private theorem signature_join (k c : ℕ) (x y : List ℕ) (small : c ≤ k) :
    signature k (x ++ c::y) = signature k x ++ signature k y := by
  simp [signature,flag,show ¬k<c by omega,List.append_assoc]

theorem false_commutes_excludes_true {w : Word Bool} (comm : [false] ++ w = w ++ [false]) :
    true ∉ w := by
  induction w with
  | nil => simp
  | cons c w ih =>
    have eqn := List.cons.inj comm
    obtain rfl := eqn.1
    simp [ih eqn.2]

private def start (i h : ℕ) (x : Option Bool) := if x.isNone then h else i
private def finish (q : ℕ) : Option Bool → ℕ
  | none => q
  | some false => 0
  | some true => 1
private def inside (gs : List ℕ) (x : Option Bool) := if x.isNone then [] else gs
private def kind (x : Option Bool) : Bool := x.isSome
private def f (i : ℕ) (gs : List ℕ) (h q : ℕ) := extended i gs 0 h [] q

private theorem token_form (i : ℕ) (g : List ℕ) (h q : ℕ) (x : Option Bool) :
    f i g h q x = mixed (start i h x) (inside g x) (finish q x) := by
  rcases x with _ | (_ | _) <;> rfl

private theorem token_flag (k : ℕ) (g : List ℕ) (x : Option Bool) :
    signature k (inside g x) = pair [false] (signature k g) (kind x) := by
  rcases x with _ | (_ | _) <;> rfl

private theorem text_form (i : ℕ) (g : List ℕ) (h q k : ℕ)
    (small : ∀ x y, finish q x + start i h y ≤ k)
    (x : Option Bool) (s : Word (Option Bool)) :
    ∃ G n, spell (f i g h q) (x::s) = mixed (start i h x) G n ∧
      signature k G = spell (pair [false] (signature k g)) ((x::s).map kind) := by
  induction s generalizing x with
  | nil =>
    refine ⟨inside g x,finish q x,by simp [token_form],?_⟩
    simpa using token_flag k g x
  | cons y s ih =>
    obtain ⟨G,n,word,marks⟩ := ih y
    refine ⟨inside g x ++ (finish q x + start i h y)::G,n,?_,?_⟩
    · rw [spell_cons,token_form,word,join_mixed]
    · rw [signature_join _ _ _ _ (small x y),token_flag,marks]
      rfl

private theorem marked_everywhere (i : ℕ) (g : List ℕ) (h q : ℕ) (x : Option Bool) (s : Word (Option Bool)) :
    b ∈ spell (f i g h q) (x::s) := by
  apply List.mem_append_left
  rw [token_form]
  simp [mixed]

private theorem recover_names (i : ℕ) (g : List ℕ) (h q : ℕ) (s t : Word (Option Bool))
    (labels : s.map kind = t.map kind) (word : spell (f i g h q) s = spell (f i g h q) t) : s=t := by
  let v := f i g h q
  have first (x : Option Bool) (s : Word (Option Bool)) : initial (spell v (x::s)) = start i h x := by
    rw [spell_cons,show v x = _ from token_form i g h q x]
    simp only [mixed,List.append_assoc,List.cons_append,initial_b]
  have tailDiff (s t : Word (Option Bool)) (labels : s.map kind = t.map kind)
      (word : spell v s = a :: spell v t) : False := by
    cases s with
    | nil => contradiction
    | cons x s =>
      cases t with
      | nil => simp at labels
      | cons y t =>
        have kxy := (List.cons.inj labels).1
        have eqn := congrArg initial word
        change initial (spell v (x::s)) = initial (spell v (y::t))+1 at eqn
        rw [first,first] at eqn
        rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;> simp_all [start,kind]
  have join : f i g h q (some true) = f i g h q (some false) ++ [a] :=
    (append_pure g i 0 1).symm
  have split (s t : Word (Option Bool)) (e : spell v ((some false)::s) = spell v ((some true)::t)) :
      spell v s = a :: spell v t := by
    simp only [spell_cons,v,join,List.append_assoc] at e
    exact List.append_cancel_left e
  induction s generalizing t with
  | nil => simpa using labels.symm
  | cons x s ih =>
    cases t with
    | nil => simp at labels
    | cons y t =>
      obtain ⟨kxy,rest⟩ := List.cons.inj labels
      by_cases xy : x=y
      · subst y
        exact congrArg (x :: ·) (ih t rest (List.append_cancel_left word))
      · rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
          first | contradiction | exact (tailDiff _ _ rest (split _ _ word)).elim |
            exact (tailDiff _ _ rest.symm (split _ _ word.symm)).elim

/-- A large interior gap in P forces unique decoding of P, Pa, Q when Q has
one marker and the joins do not have a gap of that size. -/
theorem large_gap_locates_bodies (i : ℕ) (g : List ℕ) (h q k : ℕ)
    (joins : max 1 q + max i h ≤ k) (large : ∃ z ∈ g, k<z) :
    NamedCode (extended i g 0 h [] q) := by
  obtain ⟨z,hz,big⟩ := large
  have tr : true ∈ signature k g := by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨z,hz,by simp [flag,big]⟩
  have code := (noncommuting_pair_completion [false] (signature k g)
    (fun e => false_commutes_excludes_true e tr)).1
  have bound (x y : Option Bool) : finish q x + start i h y ≤ k := by
    rcases x with _ | (_ | _) <;> cases y <;> simp [finish,start] <;> omega
  intro s t eqn
  apply recover_names i g h q s t _ eqn
  apply code
  cases s with
  | nil =>
    cases t with
    | nil => rfl
    | cons y t =>
      have mem := marked_everywhere i g h q y t
      exact (List.not_mem_nil (eqn.symm ▸ mem)).elim
  | cons x s =>
    cases t with
    | nil =>
      have mem := marked_everywhere i g h q x s
      exact (List.not_mem_nil (eqn ▸ mem)).elim
    | cons y t =>
      obtain ⟨G,n,word,marks⟩ := text_form i g h q k bound x s
      obtain ⟨H,m,other,marks'⟩ := text_form i g h q k bound y t
      obtain ⟨_,gh,_⟩ := mixed_injective (word.symm.trans (eqn.trans other))
      exact marks.symm.trans (gh ▸ marks')

end ThreeWordCodes.BinaryGaps
