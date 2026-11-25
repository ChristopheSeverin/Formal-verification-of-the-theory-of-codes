module

public import ThreeWordCodes.BorderReadings

/-! # Branches in readings on words with distinct first letters -/

@[expose] public section
namespace ThreeWordCodes.Border
variable {A I : Type*}

private theorem head_append_nonempty {u : Word A} (hu : u≠[]) (s : Word A) :
    (u++s).head?=u.head? := by cases u <;> simp_all

theorem head_of_prefix {u v : Word A} (hu : u≠[]) (pr : u <+: v) : u.head?=v.head? := by
  obtain ⟨s,rfl⟩ := pr
  exact (head_append_nonempty hu s).symm

/-- At a branch with two different next letters, a cut cannot lie inside a
token. The common part is a complete product of tokens. -/
theorem read_at_branch {g : I → Word A} (nz : ∀ i,g i≠[])
    (marked : Function.Injective (fun i => (g i).head?)) {a b : A} (diff : a≠b)
    (u : Word A) (l r : Word I) (p : u++[a] <+: spell g l) (q : u++[b] <+: spell g r) :
    ∃ w,spell g w=u := by
  induction l generalizing r u with
  | nil => obtain ⟨s,e⟩ := p; simp at e
  | cons i l ih =>
    by_cases eu : u=[]
    · exact ⟨[],eu.symm⟩
    cases r with
    | nil => obtain ⟨s,e⟩ := q; simp at e
    | cons j r =>
      have first (h : I) (rest : Word I) (c : A) (pre : u++[c] <+: spell g (h::rest)) :
          u.head?=(g h).head? :=
        (head_of_prefix eu ((List.prefix_append u [c]).trans pre)).trans (head_append_nonempty (nz h) _)
      have eqn : i=j := marked ((first i l a p).symm.trans (first j r b q))
      subst j
      have baseL : g i <+: spell g (i::l) := List.prefix_append ..
      by_cases small : u.length < (g i).length
      · have both (c : A) (s : Word I) (pre : u++[c] <+: spell g (i::s)) : u++[c] <+: g i :=
          List.prefix_of_prefix_length_le pre (List.prefix_append ..) (by simp; omega)
        have ab := (List.prefix_of_prefix_length_le (both a l p) (both b r q) (by simp)).eq_of_length (by simp)
        exact (diff (List.singleton_inj.mp (List.append_cancel_left ab))).elim
      · obtain ⟨t,ht⟩ := List.prefix_of_prefix_length_le baseL
          ((List.prefix_append u [a]).trans p) (by omega)
        rw [←ht,List.append_assoc] at p q
        obtain ⟨w,reading⟩ := ih t r ((List.prefix_append_right_inj _).mp p)
          ((List.prefix_append_right_inj _).mp q)
        exact ⟨i::w,by rw [spell_cons,reading,ht]⟩

theorem marked_facts (g : I → Word A) (nz : ∀ i,g i≠[])
    (mark : Function.Injective (fun i => (g i).head?)) :
    Function.Injective g ∧ InformationTheory.IsPrefixFree (Set.range g) := by
  refine ⟨fun i j h => mark (congrArg List.head? h),?_⟩
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hp
  exact congrArg g (mark (head_of_prefix (nz i) hp))

/-- A common power supplies a finite reference reading past the cut c. -/
theorem next_after_commuting {c t : Word A} (nt : t≠[]) (comm : c++t=t++c) :
    ∃ h,c++t <+: wordPow t h := by
  obtain ⟨r,m,n,ec,et⟩ := (commuting_iff_common_power c t).mp comm
  have pos : 0<n := by
    by_contra! h
    have e : n=0 := by omega
    exact nt (by rw [et,e,wordPow_zero])
  have enough : m+n ≤ n*(m+1) := by
    rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_le_add_right (Nat.le_mul_of_pos_left m pos) n
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le enough
  exact ⟨m+1,wordPow r d,by rw [ec,et,wordPow_mul,←wordPow_add,←wordPow_add,hd]⟩

end ThreeWordCodes.Border
