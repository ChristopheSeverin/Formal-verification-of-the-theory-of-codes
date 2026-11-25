module

public import ThreeWordCodes.UniformGaps

/-! # The two-many-marker branch of Proposition 6

A common spacing gives explicit parses. Repeated-token tilings handle two short
total margins. When only the cross joins fit, reversing the order of the two
mixed tokens gives two different parses of the same word.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def uniform (c i d j : ℕ) := mixed i (List.replicate d c) j
private abbrev free : Option Bool := some false
private abbrev U : Option Bool := some true
private abbrev V : Option Bool := none
private def padding (k : ℕ) : Word (Option Bool) := List.replicate k free

private theorem spell_pad {v : Option Bool → Word Bool} (ha : v free = [a]) (k : ℕ) :
    spell v (padding k) = run k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change v free ++ spell v (padding k) = a :: run k
    rw [ha,ih]; rfl

private theorem join_uniform (c i d j h e q k : ℕ) (ok : j+k+h=c) :
    uniform c i d j ++ (run k ++ uniform c h e q) = uniform c i (d+1+e) q := by
  rw [← List.append_assoc, uniform, append_pure, uniform, join_mixed, ok]
  rw [← List.replicate_succ, ← List.replicate_add]
  congr 1
  congr 1
  omega

private theorem wrap (c i d j k l : ℕ) :
    run k ++ uniform c i d j ++ run l = uniform c (k+i) d (j+l) := by
  rw [List.append_assoc, uniform, append_pure, uniform]
  simp [mixed,run_add,List.append_assoc]

private def marks (s : Word (Option Bool)) := s.filter (fun t => t != free)

private theorem marks_append (s t : Word (Option Bool)) : marks (s++t) = marks s ++ marks t := by
  simp [marks]

@[simp] private theorem marks_pad (k : ℕ) : marks (padding k) = [] := by simp [marks,padding]

private def tiles (x : Option Bool) (k : ℕ) : ℕ → Word (Option Bool)
  | 0 => [x]
  | n+1 => x :: (padding k ++ tiles x k n)

private theorem marks_tiles {x : Option Bool} (ne : x ≠ free) (k n : ℕ) :
    marks (tiles x k n) = List.replicate (n+1) x := by
  induction n with
  | zero => simp [tiles,marks,ne]
  | succ n ih =>
    have head (s : Word (Option Bool)) : marks (x :: s) = x :: marks s := by simp [marks,ne]
    rw [tiles, head, marks_append, marks_pad, List.nil_append, ih, List.replicate_succ (n := n+1)]

private theorem spell_tiles {v : Option Bool → Word Bool} {x : Option Bool} (ha : v free = [a])
    {c i d j : ℕ} (hx : v x = uniform c i d j) (ok : i+j ≤ c) (n : ℕ) :
    spell v (tiles x (c-(i+j)) n) = uniform c i ((d+1)*(n+1)-1) j := by
  induction n with
  | zero => simp [tiles,hx]
  | succ n ih =>
    rw [tiles,spell_cons,spell_append,spell_pad ha,ih,hx,join_uniform _ _ _ _ _ _ _ _ (by omega)]
    congr 1
    have plus : (d+1)*(n+1) > 0 := Nat.mul_pos (by omega) (by omega)
    rw [Nat.mul_succ (d+1) (n+1)]
    omega

private theorem wrap_parse {v : Option Bool → Word Bool} (ha : v free = [a])
    {s : Word (Option Bool)} {c i d j l r : ℕ} (he : spell v s = uniform c i d j)
    (hl : i ≤ l) (hr : j ≤ r) :
    spell v (padding (l-i) ++ s ++ padding (r-j)) = uniform c l d r := by
  rw [spell_append,spell_append,spell_pad ha,spell_pad ha,he,wrap]
  congr 1 <;> omega

private theorem repeated_obstruction {v : Option Bool → Word Bool} (ha : v free=[a])
    {c i d j h e q : ℕ} (hu : v U = uniform c i d j) (hv : v V = uniform c h e q)
    (ou : i+j ≤ c) (ov : h+q ≤ c) : ¬ NamedCode v := by
  intro code
  let left := max i h
  let right := max j q
  have pu := wrap_parse ha (spell_tiles ha hu ou e) (l:=left) (r:=right) (le_max_left ..) (le_max_left ..)
  have pv := wrap_parse ha (spell_tiles ha hv ov d) (l:=left) (r:=right) (le_max_right ..) (le_max_right ..)
  rw [Nat.mul_comm (e+1) (d+1)] at pv
  have e' := congrArg marks (code (pu.trans pv.symm))
  simp only [marks_append,marks_pad,List.nil_append,List.append_nil,marks_tiles (by decide : U≠free),
    marks_tiles (by decide : V≠free),List.replicate_succ,List.cons.injEq] at e'
  exact Option.some_ne_none _ e'.1

private theorem swapped_obstruction {v : Option Bool → Word Bool} (ha : v free=[a])
    {c i d j h e q : ℕ} (hu : v U = uniform c i d j) (hv : v V = uniform c h e q)
    (ou : j+h ≤ c) (ov : q+i ≤ c) : ¬ NamedCode v := by
  intro code
  have pack {x y : Option Bool} {i d j h e q : ℕ} (hx : v x = uniform c i d j)
      (hy : v y = uniform c h e q) (bound : j+h ≤ c) :
      spell v ([x] ++ padding (c-(j+h)) ++ [y]) = uniform c i (d+1+e) q := by
    simp only [spell_append,spell_cons,spell_nil,List.append_nil,spell_pad ha,hx,hy,List.append_assoc]
    exact join_uniform _ _ _ _ _ _ _ _ (by omega)
  let left := max i h
  let right := max j q
  have pu := wrap_parse ha (pack hu hv ou) (l:=left) (r:=right) (le_max_left ..) (le_max_right ..)
  have pv := wrap_parse ha (pack hv hu ov) (l:=left) (r:=right) (le_max_right ..) (le_max_left ..)
  rw [show e+1+d = d+1+e by omega] at pv
  have bad := congrArg marks (code (pu.trans pv.symm))
  simp [marks,free,U,V,padding] at bad

/-- Repeating either mixed token gives different parses when each token's
own end margins fit inside the common gap. -/
theorem uniform_repeat_ambiguity (g i d j h e q : ℕ) (left : i+j≤g) (right : h+q≤g) :
    ¬NamedCode (layout i (List.replicate d g) j h (List.replicate e g) q) :=
  repeated_obstruction (c:=g) (i:=i) (d:=d) (j:=j) (h:=h) (e:=e) (q:=q) rfl rfl rfl left right

/-- Swapping the two uniformly spaced mixed tokens gives different parses
when the two cross joins fit inside the common gap. -/
theorem uniform_cross_ambiguity (g i d j h e q : ℕ) (left : j+h≤g) (right : q+i≤g) :
    ¬NamedCode (layout i (List.replicate d g) j h (List.replicate e g) q) :=
  swapped_obstruction (c:=g) (i:=i) (d:=d) (j:=j) (h:=h) (e:=e) (q:=q) rfl rfl rfl left right

/-- Proposition 6 on binary triples with a letter, both end letters present,
and two coprime mixed counts 2 ≤ m < n. The remaining branches of the
proposition include the one-marker family. -/
theorem two_mixed_completion {i g j h e q} (code : NamedCode (layout i g j h e q))
    (two : 2 ≤ g.length+1) (long : g.length < e.length) (cop : (e.length+1).Coprime (g.length+1))
    (leftEnd : i=0 ∨ h=0) (rightEnd : j=0 ∨ q=0) : Completable (layout i g j h e q) := by
  by_contra no
  obtain ⟨c,gu,gv,bi,bj,bh,bq⟩ := uniform_gaps_of_no_completion no two long cop
  let v := layout i g j h e q
  have hu : v U = uniform c i g.length j :=
    congrArg (fun z => mixed i z j) (List.eq_replicate_iff.mpr ⟨rfl,gu⟩)
  have hv : v V = uniform c h e.length q :=
    congrArg (fun z => mixed h z q) (List.eq_replicate_iff.mpr ⟨rfl,gv⟩)
  have ha : v free = [a] := rfl
  by_cases both : i+j ≤ c ∧ h+q ≤ c
  · exact repeated_obstruction ha hu hv both.1 both.2 code
  · exact swapped_obstruction ha hu hv (by omega) (by omega) code

end ThreeWordCodes.BinaryGaps
