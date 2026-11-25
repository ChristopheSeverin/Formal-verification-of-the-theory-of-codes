module

public import ThreeWordCodes.BorderShortenings

/-! # The end letters in the border normal form -/

@[expose] public section
namespace ThreeWordCodes.Border

variable {A : Type*}

theorem append_head_of_nonempty {u : Word A} (ne : u≠[]) (v : Word A) :
    (u++v).head?=u.head? := (head_of_prefix ne (List.prefix_append u v)).symm

theorem short_head (p q : Word A) (n : ℕ) (ne : p≠[]) :
    (short p q n).head?=p.head? := append_head_of_nonempty ne _

private theorem first_letter_completion [Fintype A] (x c z : Word A)
    (nx : x≠[]) (nc : c≠[]) (nz : z≠[]) (xc : ¬x <+: c) (cx : ¬c <+: x)
    (xz : x.head?≠z.head?) (cz : c.head?≠z.head?) : Completable (addToken (pair x c) z) := by
  let v := addToken (pair x c) z
  have ne : ∀ i,v i≠[] := by rintro (_|(_|_)) <;> assumption
  have sep : ∀ i j,v i <+: v j → i=j := by
    rintro (_|(_|_)) (_|(_|_)) hp <;> try rfl
    · exact (xz (head_of_prefix nz hp).symm).elim
    · exact (cz (head_of_prefix nz hp).symm).elim
    · exact (xz (head_of_prefix nx hp)).elim
    · exact (xc hp).elim
    · exact (cz (head_of_prefix nc hp)).elim
    · exact (cx hp).elim
  change Completable v
  exact completable_prefix (fun i j eqn => sep i j (by rw [eqn])) ne
    (by rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hp; rw [sep i j hp])

/-- A completion obstruction and a maximal end cut force q to start like z.
If the two other initials agree instead, the middle shortening is prefix. -/
theorem join_starts_like_third [Fintype A] (p q z : Word A) (n i j : ℕ) (nq : q≠[])
    (code : NamedCode (family p q z n i j)) (bad : ¬Completable (family p q z n i j))
    (stop : ¬short p q n <+: q++p) (opposite : (short p q n).head?≠z.head?) :
    q.head?=z.head? := by
  let x := short p q n
  let c := q++p
  have nx : x≠[] := code.entry_ne_nil (some false)
  have nz : z≠[] := code.entry_ne_nil none
  have nc : c≠[] := by simp [c,nq]
  have independent : x++c≠c++x := by
    intro h
    obtain ⟨r,s,t,ex,ec⟩ := (commuting_iff_common_power x c).mp h
    have no := code.noncommuting_entries (by decide : (some false : Option Bool)≠some true)
    change x++(wordPow x (i+1)++c++wordPow x j)≠(wordPow x (i+1)++c++wordPow x j)++x at no
    apply no
    rw [ex,ec,wordPow_mul,wordPow_mul,←wordPow_add,←wordPow_add]
    exact wordPow_comm .. 
  have cmp : ¬ c <+: x := by
    intro cp
    have left : c <+: x++c := cp.trans (List.prefix_append ..)
    rw [show x++c=(p++q)++x from short_shift p q n] at left
    have same := (List.prefix_of_prefix_length_le left (List.prefix_append (p++q) x)
      (by simp [c,Nat.add_comm])).eq_of_length (by simp [c,Nat.add_comm])
    exact independent ((short_shift p q n).trans (congrArg (·++x) same.symm))
  by_contra different
  have other : c.head?≠z.head? := (append_head_of_nonempty nq p).symm ▸ different
  have prefixCode := first_letter_completion x c z nx nc nz stop cmp opposite other
  exact bad (lift_cut .middle p q z n i j code prefixCode)

/-- The two ends of p match x. The two ends of q match z. -/
theorem Form.marked_ends {x y z : Word Bool} (data : Form x y)
    (code : NamedCode (addToken (pair x y) z)) (bad : ¬Completable (addToken (pair x y) z))
    (initial : x.head?≠z.head?) (final : x.reverse.head?≠z.reverse.head?) :
    data.p.head?=x.head? ∧ data.p.reverse.head?=x.reverse.head? ∧
    data.q.head?=z.head? ∧ data.q.reverse.head?=z.reverse.head? := by
  let p := data.p
  let q := data.q
  have eqx : short p q data.n=x := data.short_word.symm
  have en := data.words z
  have named := en.symm ▸ code
  have no := en.symm ▸ bad
  have rx : short p.reverse q.reverse data.n=x.reverse :=
    (short_reverse p q data.n).symm.trans (congrArg List.reverse eqx)
  have eqn := family_reverse p q z data.n data.i data.j
  have stop : ¬short p q data.n <+: q++p := fun h =>
    data.left_stop ((eqx ▸ h).trans (List.prefix_append ..))
  have back : ¬short p.reverse q.reverse data.n <+: q.reverse++p.reverse := by
    intro h
    have cut : x.reverse <+: (p++q).reverse := by simpa [rx] using h
    exact data.right_stop ((List.reverse_prefix.mp cut).trans (List.suffix_append ..))
  have badRev : ¬Completable (family p.reverse q.reverse z.reverse data.n data.j data.i) := by
    intro done
    have rr : Completable (fun k => (family p q z data.n data.i data.j k).reverse) := eqn.symm ▸ done
    exact no (by simpa using rr.reverse)
  exact ⟨(short_head p q data.n data.p_nonempty).symm.trans (congrArg List.head? eqx),
    (short_head p.reverse q.reverse data.n (by simpa using data.p_nonempty)).symm.trans (congrArg List.head? rx),
    join_starts_like_third p q z _ _ _ data.q_nonempty named no stop (eqx.symm ▸ initial),
    join_starts_like_third p.reverse q.reverse z.reverse _ _ _ (by simpa using data.q_nonempty)
      (eqn ▸ named.reverse) badRev back (rx.symm ▸ final)⟩

end ThreeWordCodes.Border
