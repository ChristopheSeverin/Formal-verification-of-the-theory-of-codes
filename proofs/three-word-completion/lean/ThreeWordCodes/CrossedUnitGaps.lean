module

public import ThreeWordCodes.CrossedDifferences

/-! # Reading a positive gap at the boundary of an alternating token -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)
variable {I : Type*}

/-- When ab is the only token beginning in a, a positive gap that starts at
a token boundary must have length one. The next gap again starts at a boundary. -/
theorem unit_gaps_of_reading {g : I → Word Bool} (nz : ∀ k,g k≠[]) (key : I) (ab : g key=[a,b])
    (only : ∀ j,(g j).head?=some a → j=key) (E : List ℕ) (s : ℕ) (names : Word I)
    (pos : ∀ e∈E,0<e) (pref : gapTail s E <+: spell g names) : ∀ e∈E,e=1 := by
  induction E generalizing names with
  | nil => simp
  | cons d E ih =>
    have pd := pos d (by simp)
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pd)
    obtain ⟨rest,read⟩ := pref
    have first : (gapTail s ((d+1)::E)++rest).head?=some a := by
      rfl
    obtain ⟨tail,rfl⟩ := forced_head nz key (by rw [ab]; exact only) names
      (by intro e; rw [e] at first; contradiction) (by rw [ab]; exact first) read.symm
    have pre : run (d+1)++b::gapTail s E <+: run 1++b::spell g tail := by
      refine ⟨rest,?_⟩
      rw [spell_cons,ab] at read
      exact read
    obtain ⟨one,step⟩ := marked_prefix pre
    exact List.forall_mem_cons.mpr ⟨one,ih tail (fun e h => pos e (List.mem_cons_of_mem _ h)) step⟩

/-- A product equal to b followed by another product must start with Q or
the token Qw, and in either case its initial Q is fully located. -/
theorem body_prefix (q w : Word Bool) (s t : Word (Option Bool))
    (eqn : [b]++spell (pieces [a,b] q (q++w)) s=spell (pieces [a,b] q (q++w)) t) :
    q <+: [b]++spell (pieces [a,b] q (q++w)) s := by
  cases t with
  | nil => contradiction
  | cons k t =>
    rw [eqn,spell_cons]
    rcases k with _|(_|_)
    · exact ⟨w++_,List.append_assoc .. |>.symm⟩
    · exact Bool.noConfusion ((List.cons.inj eqn).1 : true=false)
    · exact List.prefix_append ..

theorem alternating_tail_of_shift (q w : Word Bool) (E : List ℕ) (s : ℕ)
    (form : q=mixed 0 E s) (pos : ∀ e∈E,0<e)
    (shift : ∃ l r,spell (pieces [a,b] q (q++w)) l=[a]++spell (pieces [a,b] q (q++w)) r) :
    E=List.replicate E.length 1 := by
  let g := pieces [a,b] q (q++w)
  have nq : q≠[] := by simp [form,mixed]
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,pieces,addToken,pair,nq]
  have only (k : Option Bool) (e : (g k).head?=some a) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,pieces,addToken,pair,P,mixed,run,a,b]
  obtain ⟨l,r,eqn⟩ := shift
  obtain ⟨t,rfl⟩ := forced_head (w:=[a]++spell g r) nz P only l (by simp) rfl eqn
  have matchB : [b]++spell g t=spell g r := List.cons.inj eqn |>.2
  have pref : q <+: [b]++spell g t := body_prefix q w t r matchB
  have located : mixed 0 E s <+: [b]++spell g t := form ▸ pref
  have tail : gapTail s E <+: spell g t := by
    change [b]++gapTail s E <+: [b]++spell g t at located
    exact (List.prefix_append_right_inj _).mp located
  exact List.eq_replicate_iff.mpr ⟨rfl,unit_gaps_of_reading nz P rfl only E s t pos tail⟩

end ThreeWordCodes.CrossedCase
