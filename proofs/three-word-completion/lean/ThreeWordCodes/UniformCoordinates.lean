module

public import ThreeWordCodes.LengtheningMargins
public import ThreeWordCodes.UniformGaps
public import Mathlib.Tactic.Group

/-! # Signed coordinates exclude large uniform gaps under lengthening

For P and Q with at least two markers, subtracting the common internal gap
in group coordinates makes every new gap zero. Lemma 2 applied again forces
both old initial margins to be one.
-/

@[expose] public section
namespace ThreeWordCodes.BinaryGaps

private def uniformWord (i n g q : ℕ) := mixed i (List.replicate n g) q

private def uniformGroup (i : ℤ) (n : ℕ) (g q : ℤ) :=
  GroupCoordinates.a^i * GroupCoordinates.b * (GroupCoordinates.a^g * GroupCoordinates.b)^n *
    GroupCoordinates.a^q

private theorem group_uniform (i n g q : ℕ) :
    groupWord (uniformWord i n g q) = uniformGroup i n g q := by
  induction n generalizing i with
  | zero =>
    change groupWord (run i ++ ([b] ++ run q)) = _
    rw [groupWord_append,groupWord_append,groupWord_singleton,groupWord_run,groupWord_run]
    simp [uniformGroup,GroupCoordinates.b,b,mul_assoc]
  | succ n ih =>
    have eqn : uniformWord i (n+1) g q = (run i ++ [b]) ++ uniformWord g n g q := by
      simp [uniformWord,mixed,gapTail,List.replicate_succ,List.append_assoc]
    rw [eqn,groupWord_append,groupWord_append,groupWord_run,groupWord_singleton,ih]
    simp [uniformGroup,GroupCoordinates.b,b,pow_succ',mul_assoc]

private theorem signed_uniform (l r i g q : ℤ) (n : ℕ) :
    GroupCoordinates.change l r (uniformGroup i n g q) = uniformGroup (l-i) n (l+r-g) (r-q) := by
  let d := GroupCoordinates.a
  let m := GroupCoordinates.b
  have slide : SemiconjBy (d^r) ((d^(-g)) * (d^l * m * d^r)) (d^(l+r-g) * m) := by
    change d^r * _ = _ * d^r
    group
  have move := (slide.pow_right n).eq
  simp only [uniformGroup,map_mul,map_zpow,map_pow,GroupCoordinates.change_a,GroupCoordinates.change_b,
    inv_zpow,←zpow_neg]
  change d^(-i) * (d^l * m * d^r) * (d^(-g) * (d^l * m * d^r))^n * d^(-q) =
    d^(l-i) * m * (d^(l+r-g) * m)^n * d^(r-q)
  rw [show d^(-i) * (d^l * m * d^r) = (d^(l-i) * m) * d^r by group,
    mul_assoc (d^(l-i) * m) (d^r),move]
  group

/-- The uniform transform with positive initial and final coordinates. -/
theorem uniform_coordinate_change (l r i n g q : ℕ) (hi : i ≤ l) (hq : q ≤ r) (hg : g ≤ l+r) :
    GroupCoordinates.change l r (groupWord (mixed i (List.replicate n g) q)) =
      groupWord (mixed (l-i) (List.replicate n (l+r-g)) (r-q)) := by
  change GroupCoordinates.change l r (groupWord (uniformWord i n g q)) =
    groupWord (uniformWord (l-i) n (l+r-g) (r-q))
  rw [group_uniform,group_uniform,signed_uniform]
  simp only [Nat.cast_sub hi,Nat.cast_sub hg,Nat.cast_add,Nat.cast_sub hq]

private theorem two_counts_gap {i n g h m q : ℕ}
    (amb : ¬ NamedCode (extended i (List.replicate n g) 0 h (List.replicate m g) q))
    (first : i=0 ∨ h=0) (positive : 0<n) (pm : 0<m) (ne : n≠m) (cop : (m+1).Coprime (n+1)) :
    g ≤ 1 := by
  by_contra! big
  obtain ⟨_,bq,bi,bh⟩ := normalized_lengthening_margins amb first (Or.inl rfl)
  let r := g-1
  let T := uniformWord (1-i) n 0 (r-1)
  let V := uniformWord (1-h) m 0 (r-q)
  let f := extended i (List.replicate n g) 0 h (List.replicate m g) q
  let dest := addToken (pair (T++[a]) T) V
  let F := GroupCoordinates.change 1 r
  have eg : 1+r = g := by dsimp [r]; omega
  have im (i n q : ℕ) (hi : i≤1) (hq : q≤r) :
      F (groupWord (uniformWord i n g q)) = groupWord (uniformWord (1-i) n 0 (r-q)) := by
    have res := uniform_coordinate_change 1 r i n g q hi hq eg.symm.le
    simpa [F,uniformWord,eg] using res
  have P : uniformWord (1-i) n 0 r = T ++ [a] := by
    have bound : 0 < r := by dsimp [r]; omega
    have e := append_pure (List.replicate n 0) (1-i) (r-1) 1
    change _ = T ++ [a]
    simpa only [uniformWord,T,show r-1+1 = r by omega,show run 1 = [a] from rfl] using e.symm
  have kernel : SameEquations f dest := by
    apply sameEquations_of_group_change F (GroupCoordinates.change_involutive 1 r).injective
    rintro (_ | (_ | _))
    · exact im h m q bh (by dsimp [r]; omega)
    · exact (im i n 0 bi (by omega)).trans (congrArg groupWord P)
    · exact im i n 1 bi (by dsimp [r]; omega)
  let core := addToken (pair [a] T) V
  have bad : ¬ NamedCode core := by
    intro good
    apply amb
    apply kernel.namedCode_iff.mpr
    let pad (k : Option Bool) : Word (Option Bool) := if k=some false then [some true] else []
    have recover : (fun k => spell core (pad k) ++ core k) = dest := by
      funext k
      rcases k with _ | (_ | _) <;> simp [core,pad,dest,addToken,pair]
    exact recover ▸ good.pad_left pad
  obtain ⟨c,all,_,b₁,_,b₂,_⟩ := uniform_gaps_of_distinct_counts (i:=1-i) (g:=List.replicate n 0)
    (j:=r-1) (h:=1-h) (e:=List.replicate m 0) (q:=r-q) bad (by simpa using positive)
    (by simpa using pm) (by simpa using ne) (by simpa using cop)
  have zero := all 0 (List.mem_replicate.mpr ⟨by omega,rfl⟩)
  omega

/-- In the ordered coprime two-count case of Lemma 4, an ambiguous triple and
its ambiguous lengthening force uniform internal gaps no larger than one. -/
theorem uniform_lengthening_bound_unordered {i n j h m q} (first : i=0 ∨ h=0) (last : j=0 ∨ q=0)
    (old : ¬ NamedCode (layout i n j h m q)) (new : ¬ NamedCode (extended i n j h m q))
    (pos : 0 < n.length) (pm : 0 < m.length) (ne : n.length ≠ m.length)
    (cop : (m.length+1).Coprime (n.length+1)) :
    ∃ g ≤ 1, (∀ k ∈ n, k=g) ∧ (∀ k ∈ m, k=g) := by
  obtain ⟨rfl,_,_,_⟩ := normalized_lengthening_margins new first last
  obtain ⟨g,lo,hi,_⟩ := uniform_gaps_of_distinct_counts old pos pm ne cop
  have en : n = List.replicate n.length g := List.eq_replicate_iff.mpr ⟨rfl,lo⟩
  have em : m = List.replicate m.length g := List.eq_replicate_iff.mpr ⟨rfl,hi⟩
  have changeWords : ¬ NamedCode (extended i (List.replicate n.length g) 0 h (List.replicate m.length g) q) :=
    by simpa only [←en,←em] using new
  exact ⟨g,two_counts_gap changeWords first pos pm ne cop,lo,hi⟩

theorem uniform_lengthening_bound {i n j h m q} (first : i=0 ∨ h=0) (last : j=0 ∨ q=0)
    (old : ¬ NamedCode (layout i n j h m q)) (new : ¬ NamedCode (extended i n j h m q))
    (pos : 0 < n.length) (long : n.length < m.length)
    (cop : (m.length+1).Coprime (n.length+1)) :
    ∃ g ≤ 1, (∀ k ∈ n, k=g) ∧ (∀ k ∈ m, k=g) :=
  uniform_lengthening_bound_unordered first last old new pos (by omega) (by omega) cop

end ThreeWordCodes.BinaryGaps
