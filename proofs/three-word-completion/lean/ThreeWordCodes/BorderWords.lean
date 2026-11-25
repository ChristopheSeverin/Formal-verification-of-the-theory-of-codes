module

public import ThreeWordCodes.PureReduction

/-! # Maximal end powers of a bordered word

The structure theorem uses only cancellation and comparisons of prefixes
and suffixes of a common word. It is valid on any alphabet.
-/

@[expose] public section
namespace ThreeWordCodes.Border
variable {A : Type*}

private theorem strip (x w : Word A) (ne : x≠[]) :
    ∃ n r,w=wordPow x n++r ∧ ¬x <+: r := by
  induction len : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases divides : x <+: w
    · obtain ⟨r,form⟩ := divides
      have shorter := congrArg List.length form
      have pos := List.length_pos_iff.mpr ne
      rw [List.length_append] at shorter
      obtain ⟨j,v,sub,stop⟩ := ih r.length (by omega) r rfl
      exact ⟨j+1,v,by rw [←form,sub,wordPow_succ',List.append_assoc],stop⟩
    · exact ⟨0,w,rfl,divides⟩

theorem left_cut {x y : Word A} (nx : x≠[]) (pr : x <+: y) :
    ∃ i r,y=wordPow x (i+1)++r ∧ ¬x <+: r := by
  obtain ⟨w,eqn⟩ := pr
  obtain ⟨i,r,form,stop⟩ := strip x w nx
  exact ⟨i,r,by rw [←eqn,form,wordPow_succ',List.append_assoc],stop⟩

theorem reverse_pow (w : Word A) (n : ℕ) : (wordPow w n).reverse=wordPow w.reverse n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPow_succ,List.reverse_append,ih,wordPow_succ']

theorem right_cut {x y : Word A} (nx : x≠[]) (sf : x <:+ y) :
    ∃ j t,y=t++wordPow x (j+1) ∧ ¬x <:+ t := by
  obtain ⟨j,t,form,stop⟩ := left_cut (x:=x.reverse) (by simpa using nx) sf.reverse
  exact ⟨j,t.reverse,by simpa [reverse_pow] using congrArg List.reverse form,
    fun h => stop (by simpa using h.reverse)⟩

private theorem suffix_le {u v t : Word A} (p : u <:+ t) (q : v <:+ t) (h : u.length≤v.length) : u <:+ v := by
  rcases List.suffix_or_suffix_of_suffix p q with fit | back
  · exact fit
  · rw [back.eq_of_length_le h]

theorem commute_of_suffix_power {x r : Word A} {j : ℕ} (p : x++r <:+ wordPow x j) :
    x++r=r++x := by
  obtain ⟨u,eqn⟩ := p
  have one : x++r <:+ wordPow x (j+1) := by
    rw [wordPow_succ']; exact ⟨x++u,by rw [List.append_assoc,eqn]⟩
  have two : r++x <:+ wordPow x (j+1) := by
    rw [wordPow_succ,←eqn]; exact ⟨u++x,by simp [List.append_assoc]⟩
  exact (suffix_le one two (by simp [Nat.add_comm])).eq_of_length (by simp [Nat.add_comm])

private theorem commute_padded {x r : Word A} (comm : x++r=r++x) (i : ℕ) :
    x++(wordPow x i++r)=(wordPow x i++r)++x := by
  calc x++(wordPow x i++r)=wordPow x (i+1)++r := by rw [wordPow_succ',List.append_assoc]
       _ = wordPow x i++(x++r) := by rw [wordPow_succ,List.append_assoc]
       _ = _ := by rw [comm,List.append_assoc]

/-- From t v = u t, recover a conjugate pair u=pq, v=qp and an explicit
reading t=p(qp)^n. The piece q is nonempty. -/
theorem solve_conjugacy (u v t : Word A) (nu : u≠[]) (eqn : t++v=u++t) :
    ∃ p q n,u=p++q ∧ v=q++p ∧ t=p++wordPow (q++p) n ∧ q≠[] := by
  induction len : t.length using Nat.strong_induction_on generalizing t with
  | ind n ih =>
    rcases List.append_eq_append_iff.mp eqn with ⟨q,word,other⟩ | ⟨s,word,other⟩
    · by_cases empty : q=[]
      · have ut : u=t := by simpa [empty] using word
        have vt : v=t := by simpa [empty] using other
        exact ⟨[],u,1,by simp,by simp [ut,vt],by simp [ut],nu⟩
      · exact ⟨t,q,0,word,other,by simp,empty⟩
    · have lengths := congrArg List.length word
      simp only [List.length_append] at lengths
      have pos := List.length_pos_iff.mpr nu
      obtain ⟨p,q,n,uf,vf,tf,nq⟩ := ih s.length (by omega) s (other.symm.trans word) rfl
      refine ⟨p,q,n+1,uf,vf,?_,nq⟩
      calc t = u++s := word
           _ = (p++q)++(p++wordPow (q++p) n) := by rw [uf,tf]
           _ = p++wordPow (q++p) (n+1) := by rw [wordPow_succ']; simp [List.append_assoc]

/-- The parameters i and j are the numbers of extra full end blocks after
the first. The two inequalities express maximality of both extracted powers. -/
structure Form (x y : Word A) where
  p : Word A
  q : Word A
  n : ℕ
  i : ℕ
  j : ℕ
  p_nonempty : p≠[]
  q_nonempty : q≠[]
  short_word : x=p++wordPow (q++p) n
  long_word : y=wordPow x (i+1)++(q++p)++wordPow x j
  left_stop : ¬ x <+: (q++p)++wordPow x j
  right_stop : ¬ x <:+ wordPow x i++(p++q)

theorem normal_form {x y : Word A} (nx : x≠[]) (pr : x <+: y) (sf : x <:+ y)
    (different : x++y≠y++x) : Nonempty (Form x y) := by
  obtain ⟨i,r,left,leftStop⟩ := left_cut nx pr
  obtain ⟨j,t,right,rightStop⟩ := right_cut nx sf
  have noR : x++r≠r++x := fun e => different (left.symm ▸ commute_padded e (i+1))
  have rIn : r <:+ y := ⟨_,left.symm⟩
  have powIn : wordPow x (j+1) <:+ y := ⟨t,right.symm⟩
  have front : wordPow x i++(x++r)=y := by rw [←List.append_assoc,←wordPow_succ,left]
  by_cases separate : (wordPow x (j+1)).length≤r.length
  · obtain ⟨q,rForm⟩ := suffix_le powIn rIn separate
    have nq : q≠[] := by
      rintro rfl
      have pure : r=wordPow x (j+1) := by simpa using rForm.symm
      exact noR (by rw [pure,←wordPow_one x]; exact wordPow_comm ..)
    have fit : (q++x)++wordPow x j=r := by rw [List.append_assoc,←wordPow_succ',rForm]
    have tail : t=wordPow x i++(x++q) := by
      apply List.append_cancel_right (bs:=wordPow x (j+1))
      rw [←right,left,←rForm,wordPow_succ x i]; simp [List.append_assoc]
    exact ⟨⟨x,q,0,i,j,nx,nq,by simp,by simp only [left,←fit,List.append_assoc],fit ▸ leftStop,tail ▸ rightStop⟩⟩
  · have overlap := Nat.lt_of_not_ge separate
    have enough : (wordPow x j).length<r.length := by
      by_contra! narrow
      have fits : (x++r).length≤(wordPow x (j+1)).length := by
        rw [wordPow_succ',List.length_append,List.length_append]; omega
      exact noR (commute_of_suffix_power (suffix_le (show x++r <:+ y from ⟨_,front⟩) powIn fits))
    have lastPow : wordPow x j <:+ y := (show wordPow x j <:+ wordPow x (j+1) by rw [wordPow_succ']; exact List.suffix_append ..).trans powIn
    obtain ⟨V,vr⟩ := suffix_le lastPow rIn enough.le
    have e : wordPow x (i+1)++V=t++x := by
      apply List.append_cancel_right (bs:=wordPow x j)
      simpa only [List.append_assoc,vr,←wordPow_succ' x j,←right] using left.symm
    have initial : wordPow x i <+: t++x := ⟨x++V,by rw [←List.append_assoc,←wordPow_succ,e]⟩
    have toT : (wordPow x i).length≤t.length := by
      have ht := congrArg List.length e
      rw [wordPow_succ,List.length_append,List.length_append,List.length_append] at ht
      omega
    obtain ⟨U,ut⟩ := List.prefix_of_prefix_length_le initial (List.prefix_append t x) toT
    have rotate : x++V=U++x := by
      apply List.append_cancel_left (as:=wordPow x i)
      rw [←List.append_assoc,←wordPow_succ,e,←ut,List.append_assoc]
    have nv : V≠[] := by
      rintro rfl
      exact (Nat.ne_of_lt enough) (congrArg List.length (by simpa using vr : wordPow x j=r))
    have nu : U≠[] := by
      intro nil
      have h := congrArg List.length rotate
      simp [nil] at h
      exact nv h
    obtain ⟨p,q,n,uf,vf,xf,nq⟩ := solve_conjugacy U V x nu rotate
    have np : p≠[] := by
      rintro rfl
      have uv : U=V := by simp [uf,vf]
      apply noR
      have comm : x++V=V++x := uv ▸ rotate
      rw [←vr,List.append_assoc,←List.append_assoc x V,comm,List.append_assoc]
      exact congrArg (V++·) (by rw [←wordPow_succ',wordPow_succ])
    have fit : r=(q++p)++wordPow x j := vr.symm.trans (congrArg (·++wordPow x j) vf)
    have put : t=wordPow x i++(p++q) := ut.symm.trans (congrArg (wordPow x i++·) uf)
    exact ⟨⟨p,q,n,i,j,np,nq,xf,by simp only [left,fit,List.append_assoc],fit ▸ leftStop,put ▸ rightStop⟩⟩

end ThreeWordCodes.Border
