module

public import ThreeWordCodes.CrossedSharedTheorem

/-! # Separating a common first name in the intermediate and overlapping rows -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)
variable {A I : Type*}

theorem first_difference {g : I → Word A} (nz : ∀ k,g k≠[]) (amb : ¬NamedCode g) :
    ∃ i j l r,i≠j ∧ spell g (i::l)=spell g (j::r) := by
  change ¬(∀ ⦃s t⦄,spell g s=spell g t → s=t) at amb
  push Not at amb
  obtain ⟨s,t,eqn,ne⟩ := amb
  exact first_mismatched_names nz s t ne eqn

/-- The only first difference in p,q,qw compares q with qw. -/
theorem extra_suffix_equation (p q w : Word A) (np : p≠[]) (nq : q≠[]) (diff : p.head?≠q.head?)
    (amb : ¬NamedCode (pieces p q (q++w))) :
    ∃ s t,spell (pieces p q (q++w)) s=w++spell (pieces p q (q++w)) t := by
  let g := pieces p q (q++w)
  have nz (k : Option Bool) : g k≠[] := by
    rcases k with _|(_|_) <;> simp [g,pieces,addToken,pair,np,nq]
  obtain ⟨i,j,s,t,ij,eqn⟩ := first_difference nz amb
  have start := congrArg List.head? eqn
  simp only [spell_cons,Border.append_head_of_nonempty (nz _)] at start
  have allowed : (i=Q ∧ j=Z) ∨ (i=Z ∧ j=Q) := by
    rcases i with _|(_|_) <;> rcases j with _|(_|_) <;>
      simp_all [g,pieces,addToken,pair,Q,Z,Border.append_head_of_nonempty nq,Ne.symm diff]
  have cancel (u v : Word (Option Bool)) (e : spell g (Q::u)=spell g (Z::v)) : spell g u=w++spell g v := by
    change q++spell g u=(q++w)++spell g v at e
    rw [List.append_assoc] at e; exact List.append_cancel_left e
  rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨s,t,cancel s t eqn⟩
  · exact ⟨t,s,cancel t s eqn.symm⟩

theorem forced_head {g : I → Word A} (nz : ∀ k,g k≠[]) (k : I) (only : ∀ j,(g j).head?=(g k).head? → j=k)
    (names : Word I) {w : Word A} (nw : w≠[]) (initial : w.head?=(g k).head?) (read : spell g names=w) :
    ∃ t,names=k::t := by
  cases names with
  | nil => exact (nw read.symm).elim
  | cons j t =>
    have first : (g j).head?=(g k).head? := (Border.append_head_of_nonempty (nz j) _).symm.trans
      ((congrArg List.head? read).trans initial)
    exact ⟨t,by rw [only j first]⟩

/-- Cancelling Q and the forced token P gives F = a G in the test P,Q,QP a. -/
theorem shifted_products (p q : Word Bool) (np : p≠[]) (nq : q≠[]) (diff : p.head?≠q.head?)
    (amb : ¬NamedCode (pieces p q (q++(p++[a])))) :
    let g := pieces p q (q++(p++[a]))
    ∃ s t,spell g s=[a]++spell g t := by
  intro g
  obtain ⟨l,r,eqn⟩ := extra_suffix_equation p q (p++[a]) np nq diff amb
  change spell g l=(p++[a])++spell g r at eqn
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,pieces,addToken,pair,np,nq]
  have only (k : Option Bool) (h : (g k).head?=(g P).head?) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,pieces,addToken,pair,P,Border.append_head_of_nonempty nq,Ne.symm diff]
  rw [List.append_assoc] at eqn
  obtain ⟨s,rfl⟩ := forced_head nz P only l (by simp [np]) (Border.append_head_of_nonempty np _) eqn
  exact ⟨s,r,List.append_cancel_left eqn⟩

/-- A first-letter shift between two nonempty products changes their
initial a-margins by one. Every token has a marker. -/
theorem margin_shift {g : I → Word Bool} (x y : ℕ)
    (shape : ∀ k,∃ n ls j,(n=x ∨ n=y) ∧ g k=mixed n ls j)
    (s t : Word I) (eqn : spell g s=[a]++spell g t) : x=y+1 ∨ y=x+1 := by
  cases s with
  | nil => contradiction
  | cons k s =>
    obtain ⟨i,ls,j,e,word⟩ := shape k
    cases t with
    | nil =>
      have hit : b∈spell g (k::s) := List.mem_append_left _ (show b∈g k by rw [word]; simp [mixed])
      rw [eqn] at hit; simp [a,b] at hit
    | cons l t =>
      obtain ⟨h,ls',q,e',word'⟩ := shape l
      have margins := congrArg initial eqn
      change initial (g k++spell g s)=initial (g l++spell g t)+1 at margins
      simp only [word,word',mixed,List.append_assoc,List.cons_append,initial_b] at margins
      omega

theorem intermediate_margins (i h s : ℕ) (G E : List ℕ)
    (opposite : (i=0 ∧ 0 < h) ∨ (0 < i ∧ h=0))
    (amb : ¬NamedCode (pieces (mixed i G 0) (mixed h E s) (mixed h E s++mixed i G 0++[a]))) :
    ((i=0 ∧ h=1) ∨ (i=1 ∧ h=0)) ∧ s≤1 := by
  let p := mixed i G 0
  let q := mixed h E s
  let g := pieces p q (q++(p++[a]))
  let L := E++(s+i)::G
  have shape : q++(p++[a])=mixed h L 1 := by rw [←List.append_assoc,show q++p=mixed h L 0 from join_mixed ..]; exact append_pure L h 0 1
  have fixed : ¬NamedCode g := by simpa only [g,p,q,List.append_assoc] using amb
  have np : p≠[] := by simp [p,mixed]
  have nq : q≠[] := by simp [q,mixed]
  have diff : p.head?≠q.head? := by
    rcases opposite with ⟨rfl,pos⟩|⟨pos,rfl⟩
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
      simp [p,q,mixed,run,List.replicate_succ,a,b]
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
      simp [p,q,mixed,run,List.replicate_succ,a,b]
  obtain ⟨l,r,unmatched⟩ := shifted_products p q np nq diff fixed
  have ends := margin_shift (g:=g) i h (by
    rintro (_|(_|_))
    · exact ⟨h,L,1,Or.inr rfl,shape⟩
    · exact ⟨i,G,0,Or.inl rfl,rfl⟩
    · exact ⟨h,E,s,Or.inr rfl,rfl⟩) l r unmatched
  refine ⟨by omega,?_⟩
  by_contra! large
  let f (k : Option Bool) := (g k).reverse
  let margin : Option Bool → ℕ
    | none => 1
    | some false => 0
    | some true => s
  have hi : Function.Injective margin := by
    rintro (_|(_|_)) (_|(_|_)) e <;> simp_all [margin]
    omega
  have initial (k : Option Bool) : ∃ w,f k=run (margin k)++b::w := by
    rcases k with _|(_|_) <;> simp only [f,g,pieces,addToken,pair,shape,p,q,reverse_mixed] <;> exact ⟨_,rfl⟩
  have done := BinaryGaps.distinct_starts f margin initial hi
  exact fixed (by simpa [f] using done.1.reverse)

end ThreeWordCodes.CrossedCase
