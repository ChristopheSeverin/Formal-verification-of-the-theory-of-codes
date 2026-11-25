module

public import ThreeWordCodes.Models

/-! # Lifting and substituting completions across alphabets

Pulling back a finite code along a letter map decorates each position of a word.
Each decoration of a parsed word induces exactly one decoration of its tokens.
-/

@[expose] public section
namespace ThreeWordCodes
variable {A B I : Type*}

noncomputable def lifts [Fintype A] (π : A → B) (S : Finset (Word B)) : Finset (Word A) := by
  classical
  exact S.biUnion fun v => (Finset.univ.image (List.ofFn (n := v.length) (α := A))).filter
    (fun w => w.map π = v)

@[simp] theorem mem_lifts [Fintype A] (π : A → B) (S : Finset (Word B)) (w : Word A) :
    w ∈ lifts π S ↔ w.map π ∈ S := by
  classical
  constructor
  · intro hw
    obtain ⟨v, hv, hh⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hh).2 ▸ hv
  · intro hw
    apply Finset.mem_biUnion.mpr
    refine ⟨w.map π, hw, Finset.mem_filter.mpr ⟨?_, rfl⟩⟩
    apply Finset.mem_image.mpr
    have he : (w.map π).length = w.length := List.length_map ..
    rw [he]
    exact ⟨w.get, Finset.mem_univ _, by simp⟩

private def project [Fintype A] (π : A → B) {S : Finset (Word B)} (x : ↥(lifts π S)) : ↥S :=
  ⟨x.val.map π, (mem_lifts _ _ _).mp x.property⟩

private theorem map_concat [Fintype A] (π : A → B) {S : Finset (Word B)}
    (t : List (↥(lifts π S))) :
    (concatenate t).map π = concatenate (t.map (project π)) := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    change (a.val ++ concatenate t).map π = a.val.map π ++ concatenate (t.map (project π))
    simp [ih]

private theorem split_lift (π : A → B) {w : Word A} {x y : Word B} (e : w.map π = x ++ y) :
    ∃ u v, u ++ v = w ∧ u.map π = x ∧ v.map π = y := by
  refine ⟨w.take x.length, w.drop x.length, List.take_append_drop .., ?_, ?_⟩
  · simp [List.map_take, e]
  · simp [List.map_drop, e]

private theorem lift_blocks [Fintype A] (π : A → B) {S : Finset (Word B)}
    (s : List (↥S)) (w : Word A) (e : w.map π = concatenate s) :
    ∃ t : List (↥(lifts π S)), concatenate t = w ∧ t.map (project π) = s := by
  induction s generalizing w with
  | nil =>
    obtain rfl : w = [] := List.map_eq_nil_iff.mp e
    exact ⟨[], rfl, rfl⟩
  | cons b s ih =>
    obtain ⟨u, v, rfl, hu, hv⟩ := split_lift π (show w.map π = b.val ++ concatenate s from e)
    obtain ⟨t, h₁, h₂⟩ := ih v hv
    let c : ↥(lifts π S) := ⟨u, (mem_lifts _ _ _).mpr (hu ▸ b.property)⟩
    have hc : project π c = b := Subtype.ext hu
    exact ⟨c :: t, congrArg (u ++ ·) h₁, by simp [hc, h₂]⟩

private theorem equal_blocks [Fintype A] (π : A → B) {S : Finset (Word B)}
    (s t : List (↥(lifts π S))) (h : concatenate s = concatenate t)
    (p : s.map (project π) = t.map (project π)) : s = t := by
  induction s generalizing t with
  | nil =>
    obtain rfl : t = [] := List.map_eq_nil_iff.mp p.symm
    rfl
  | cons a s ih =>
    cases t with
    | nil => simp at p
    | cons b t =>
      obtain ⟨hab, hp⟩ := List.cons.inj p
      have hm := congrArg (fun c : ↥S => c.val.length) hab
      change (a.val.map π).length = (b.val.map π).length at hm
      have he := List.append_inj h (by simpa using hm : a.val.length = b.val.length)
      exact List.cons.injEq .. |>.mpr ⟨Subtype.ext he.1, ih t he.2 hp⟩

/-- All decorations of the three finite sets have the same unique parsing property. -/
theorem PositiveFactorization.liftLetters [Fintype A] (π : A → B) {M P Q : Finset (Word B)}
    (h : PositiveFactorization M P Q) :
    PositiveFactorization (lifts π M) (lifts π P) (lifts π Q) := by
  constructor
  · rintro ⟨l, s, r⟩ ⟨k, t, j⟩ he
    have e : l.val ++ (concatenate s ++ r.val) = k.val ++ (concatenate t ++ j.val) := by
      simpa [assemble, List.append_assoc] using he
    have out := congrArg (List.map π) he
    simp only [assemble, List.map_append, map_concat] at out
    have hp := h.1 (a₁ := (project π l, s.map (project π), project π r))
      (a₂ := (project π k, t.map (project π), project π j)) out
    obtain ⟨hl, ht, hr⟩ := Prod.ext_iff.mp hp |>.imp_right Prod.ext_iff.mp
    have hlen := congrArg (fun c : ↥Q => c.val.length) hl
    change (l.val.map π).length = (k.val.map π).length at hlen
    obtain ⟨h₁, tail⟩ := List.append_inj e (by simpa using hlen : l.val.length = k.val.length)
    have rlen := congrArg (fun c : ↥P => c.val.length) hr
    change (r.val.map π).length = (j.val.map π).length at rlen
    obtain ⟨h₂, h₃⟩ := List.append_inj' tail (by simpa using rlen : r.val.length = j.val.length)
    exact Prod.ext (Subtype.ext h₁) (Prod.ext (equal_blocks π s t h₂ ht) (Subtype.ext h₃))
  · intro w
    obtain ⟨⟨l, s, r⟩, he⟩ := h.2 (w.map π)
    obtain ⟨u, v, rfl, hu, hv⟩ := split_lift π (show w.map π = l.val ++ (concatenate s ++ r.val) by
      simpa [assemble, List.append_assoc] using he.symm)
    obtain ⟨b, d, rfl, hb, hd⟩ := split_lift π hv
    obtain ⟨t, ht, _⟩ := lift_blocks π s b hb
    exact ⟨(⟨u, (mem_lifts _ _ _).mpr (hu ▸ l.property)⟩, t,
      ⟨d, (mem_lifts _ _ _).mpr (hd ▸ r.property)⟩), by simp [assemble, ht, List.append_assoc]⟩

/-- Compose a completable list on a smaller alphabet of names with a completable inner code. -/
theorem completion_substitution [Fintype A] [Nonempty I] {v : I → Word A} {X : Set (Word I)}
    (iv : Function.Injective v) (inner : HasPositiveCompletion (Set.range v))
    (outer : HasPositiveCompletion X) : HasPositiveCompletion (spell v '' X) := by
  classical
  obtain ⟨M, L, R, sub, _, pos⟩ := inner
  obtain ⟨N, P, Q, sub', _, pos'⟩ := outer
  let inc (i : I) : ↥M := ⟨v i, sub ⟨i, rfl⟩⟩
  have hi : Function.Injective inc := fun _ _ he => iv (congrArg Subtype.val he)
  let π := Function.invFun inc
  have sec : Function.LeftInverse π inc := Function.leftInverse_invFun hi
  have ou := (pos'.liftLetters π).model
  apply (pos.model.compose ou).completion.mono
  rintro _ ⟨s, hs, rfl⟩
  have mem : s.map inc ∈ lifts π N := by
    rw [mem_lifts, List.map_map]
    simpa [show π ∘ inc = id from funext sec] using sub' hs
  exact ⟨⟨s.map inc, mem⟩, by simp [spell, inc, List.flatMap_def, List.map_map]; rfl⟩

end ThreeWordCodes
