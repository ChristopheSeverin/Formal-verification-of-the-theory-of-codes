module

public import ThreeWordCodes.BlockOccurrences

/-! # Runs of a distinguished letter in a list of blocks -/

@[expose] public section
namespace ThreeWordCodes.BlockRuns
variable {T : Type*}

/-- Each pair records a letter different from F and the number of copies of F
immediately following that letter. -/
def after (F : T) (runs : List (T × ℕ)) := runs.flatMap fun p => p.1 :: List.replicate p.2 F

@[simp] theorem after_nil (F : T) : after F [] = [] := rfl
@[simp] theorem after_cons (F : T) (x : T) (n : ℕ) (rs : List (T × ℕ)) :
    after F ((x,n)::rs) = x :: (List.replicate n F ++ after F rs) := rfl
@[simp] theorem after_append (F : T) (rs ts : List (T × ℕ)) :
    after F (rs++ts) = after F rs ++ after F ts := by simp [after]

theorem decompose [DecidableEq T] (F : T) (xs : List T) :
    ∃ n rs, xs=List.replicate n F ++ after F rs ∧ ∀ e∈rs, e.1≠F := by
  induction xs with
  | nil => exact ⟨0,[],rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨n,rs,rfl,valid⟩ := ih
    by_cases eqn : x=F
    · subst x; exact ⟨n+1,rs,rfl,valid⟩
    · exact ⟨0,(x,n)::rs,rfl,by simpa using And.intro eqn valid⟩

/-- If a pattern omits the separating letter, its occurrence is either on
the left with the given initial cut, or wholly on the right. -/
private theorem across {m : T} {P U V pre tail : List T} (nonempty : P≠[]) (miss : m∉P)
    (found : U++m::V = pre++(P++tail)) :
    (∃ r, U=pre++(P++r)) ∨ ∃ init, pre=U++m::init ∧ V=init++(P++tail) := by
  rcases List.append_eq_append_iff.mp found with ⟨v,whereCut,rest⟩ | ⟨v,whereCut,rest⟩
  · cases v with
    | nil =>
      cases P with
      | nil => contradiction
      | cons p ps =>
        have same := (List.cons.inj rest).1
        exact (miss (by simp [same])).elim
    | cons s v =>
      obtain ⟨rfl,body⟩ := List.cons.inj rest
      exact Or.inr ⟨v,whereCut,body⟩
  · have pref : P <+: v := by
      have pr : P <+: v++m::V := ⟨tail,rest⟩
      clear rest whereCut found
      induction v generalizing P with
      | nil =>
        rcases List.prefix_cons_iff.mp pr with rfl | ⟨s,rfl,_⟩
        · contradiction
        · exact (miss (by simp)).elim
      | cons x xs ih =>
        rcases List.prefix_cons_iff.mp pr with rfl | ⟨s,rfl,h⟩
        · exact List.nil_prefix
        · cases s with
          | nil => exact List.cons_prefix_cons.mpr ⟨rfl,List.nil_prefix⟩
          | cons a s =>
            exact List.cons_prefix_cons.mpr ⟨rfl,ih (by simp) (fun hm => miss (List.mem_cons_of_mem x hm)) h⟩
    obtain ⟨r,fit⟩ := pref
    exact Or.inl ⟨r,by rw [whereCut,fit]⟩

private theorem short_runs {F : T} {n : ℕ} (pos : 0<n) (j : ℕ) (rs : List (T × ℕ))
    (small : j<n) (bounded : ∀ e∈rs,e.1≠F ∧ e.2<n) :
    ¬ List.replicate n F <:+: (List.replicate j F ++ after F rs) := by
  induction rs generalizing j with
  | nil =>
    intro occ
    have limit := occ.sublist.length_le
    simp at limit
    omega
  | cons e rs ih =>
    rcases e with ⟨x,k⟩
    rintro ⟨pre,tail,eqn⟩
    have cond := bounded (x,k) (by simp)
    have split := across (P:=List.replicate n F) (U:=List.replicate j F) (m:=x)
      (V:=List.replicate k F++after F rs) (pre:=pre) (tail:=tail)
      (by simp [Nat.ne_of_gt pos]) (by simp [cond.1]) (by simpa only [after_cons,List.append_assoc] using eqn.symm)
    rcases split with ⟨r,inside⟩ | ⟨init,_,within⟩
    · have lengths := congrArg List.length inside
      simp at lengths
      omega
    · exact ih k cond.2 (fun t ht => bounded t (by simp [ht])) ⟨init,tail,by simpa [List.append_assoc] using within.symm⟩

/-- The first run has length n and every following run has fewer than n
copies of F. Thus n consecutive copies can only begin at the first index. -/
theorem initial_run {F : T} {n : ℕ} (pos : 0<n) (rs : List (T × ℕ))
    (bounded : ∀ e∈rs,e.1≠F ∧ e.2<n) (pre tail : List T)
    (found : List.replicate n F ++ after F rs = pre++(List.replicate n F++tail)) : pre=[] := by
  cases rs with
  | nil =>
    have lengths := congrArg List.length found
    simp only [after_nil,List.append_nil,List.length_append,List.length_replicate] at lengths
    exact List.length_eq_zero_iff.mp (by omega)
  | cons e rs =>
    rcases e with ⟨x,k⟩
    have cond := bounded (x,k) (by simp)
    have split := across (P:=List.replicate n F) (U:=List.replicate n F) (m:=x)
      (V:=List.replicate k F++after F rs) (pre:=pre) (tail:=tail)
      (by simp [Nat.ne_of_gt pos]) (by simp [cond.1]) found
    rcases split with ⟨r,inside⟩ | ⟨init,_,within⟩
    · have lengths := congrArg List.length inside
      simp only [List.length_append,List.length_replicate] at lengths
      exact List.length_eq_zero_iff.mp (by omega)
    · exact (short_runs pos k rs cond.2 (fun t ht => bounded t (by simp [ht]))
        ⟨init,tail,by simpa [List.append_assoc] using within.symm⟩).elim

/-- Choose the first noninitial run with length at least n. -/
theorem first_return {F : T} (rs : List (T × ℕ)) (n : ℕ)
    (valid : ∀ e∈rs,e.1≠F) (existsLong : ∃ e∈rs,n≤e.2) :
    ∃ past D k later, rs=past++(D,k)::later ∧ D≠F ∧ n≤k ∧ ∀ e∈past,e.1≠F ∧ e.2<n := by
  induction rs with
  | nil => simp at existsLong
  | cons e rs ih =>
    rcases e with ⟨D,k⟩
    by_cases big : n≤k
    · exact ⟨[],D,k,rs,rfl,valid (D,k) (by simp),big,by simp⟩
    · have later : ∃ e∈rs,n≤e.2 := by
        obtain ⟨e,mem,le⟩ := existsLong
        exact ⟨e,(List.mem_cons.mp mem).resolve_left (by rintro rfl; exact big le),le⟩
      obtain ⟨past,x,j,t,eqn,ne,hi,bound⟩ := ih (fun a ha => valid a (by simp [ha])) later
      exact ⟨(D,k)::past,x,j,t,by rw [eqn]; rfl,ne,hi,by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | p
        · exact ⟨valid (D,k) (by simp),Nat.lt_of_not_ge big⟩
        · exact bound z p⟩

end ThreeWordCodes.BlockRuns
