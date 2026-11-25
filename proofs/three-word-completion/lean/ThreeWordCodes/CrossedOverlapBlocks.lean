module

public import ThreeWordCodes.CrossedOverlapMargins

/-! # Locating the long-gap block next to a forced aba reading -/

@[expose] public section
namespace ThreeWordCodes.CrossedCase
open BinaryGaps
open Border (pieces P Q Z)

/-- Starting just before one a in a product, a run of gaps of length at
least two can be read only by consuming aba once per gap. -/
theorem long_prefix_twos {g : Option Bool → Word Bool} (nz : ∀ k,g k≠[]) (aba : g P=[a,b,a])
    (only : ∀ k,(g k).head?=some a → k=P) (H E : List ℕ) (l : Word (Option Bool))
    (prefixGaps : H <+: E) (large : ∀ e∈H,2≤e) (read : gapTail 0 E <+: [a]++spell g l) : ∀ e∈H,e=2 := by
  induction H generalizing E l with
  | nil => simp
  | cons h H ih =>
    obtain ⟨rest,rfl⟩ := prefixGaps
    have ge := large h (by simp)
    obtain ⟨d,ed⟩ : ∃ d,h=(d+1)+1 := ⟨h-2,by omega⟩
    subst h
    have pre : run (d+1)++b::gapTail 0 (H++rest) <+: spell g l := by
      apply (List.prefix_append_right_inj [a]).mp
      exact read
    obtain ⟨tail,eqn⟩ := pre
    have ha : ((run (d+1)++b::gapTail 0 (H++rest))++tail).head?=some a := rfl
    obtain ⟨l',rfl⟩ := forced_head nz P (by rw [aba]; exact only) l
      (by intro e; rw [e] at ha; contradiction) (by rw [aba]; exact ha) eqn.symm
    have bound : run (d+1)++b::gapTail 0 (H++rest) <+: run 1++b::([a]++spell g l') := by
      refine ⟨tail,?_⟩
      rw [spell_cons,aba] at eqn
      exact eqn
    obtain ⟨val,step⟩ := marked_prefix bound
    exact List.forall_mem_cons.mpr ⟨by omega,ih (H++rest) l' (List.prefix_append ..)
      (fun e mem => large e (List.mem_cons_of_mem _ mem)) step⟩

/-- After the first conflicting pair, cancellation exposes ba immediately
before a product. The next token on the other side contains the entire K. -/
theorem overlap_block_reading (E : List ℕ) (s : ℕ) :
    let K := mixed 0 E 0
    let v := K++run s
    let g := pieces [a,b,a] v (v++[a,b])
    ¬NamedCode g → ∃ l,gapTail 0 E <+: [a]++spell g l := by
  intro K v g amb
  have nv : v≠[] := by simp [v,K,mixed]
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,pieces,pair,addToken,nv]
  have only (k : Option Bool) (eqn : (g k).head?=some a) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,pieces,pair,addToken,P,v,K,mixed,run,a,b]
  obtain ⟨l,r,eqn⟩ := extra_suffix_equation [a,b,a] v [a,b] (by decide) nv (by change some a≠some b; decide) amb
  obtain ⟨l',rfl⟩ := forced_head (g:=g) (w:=[a,b]++spell g r) nz P only l (by simp) rfl eqn
  have shift : spell g r=[a]++spell g l' := ((List.cons.inj (List.cons.inj eqn).2).2).symm
  obtain ⟨r',rfl⟩ := forced_head (g:=g) (w:=[a]++spell g l') nz P only r (by simp) rfl shift
  have matchB : spell g l'=[b,a]++spell g r' := ((List.cons.inj shift).2).symm
  have located : K <+: [b,a]++spell g r' := by
    cases l' with
    | nil => contradiction
    | cons k l =>
      rw [←matchB,spell_cons]; rcases k with _|(_|_)
      · exact ⟨run s++([a,b]++spell g l),by change K++_=(K++run s++[a,b])++_; simp [List.append_assoc]⟩
      · exact Bool.noConfusion ((List.cons.inj matchB).1 : false=true)
      · exact ⟨run s++spell g l,(List.append_assoc ..).symm⟩
  exact ⟨r',(List.prefix_append_right_inj [b]).mp located⟩

theorem bounded_long_block (E : List ℕ) (s : ℕ) (bound : s≤1)
    (bad : ¬NamedCode (pieces [a,b,a] (mixed 0 E 0++run s) ((mixed 0 E 0++run s)++[a,b]))) :
    ∀ H,H <+: E++[1+s] → (∀ x∈H,2≤x) → ∀ x∈H,x≤2 := by
  let K := mixed 0 E 0
  let v := K++run s
  let g := pieces [a,b,a] v (v++[a,b])
  have nz (k : Option Bool) : g k≠[] := by rcases k with _|(_|_) <;> simp [g,pieces,pair,addToken,v,K,mixed]
  have only (k : Option Bool) (hk : (g k).head?=some a) : k=P := by
    rcases k with _|(_|_) <;> simp_all [g,pieces,pair,addToken,P,v,K,mixed,run,a,b]
  obtain ⟨l,read⟩ := overlap_block_reading E s bad
  intro H pref high x mem
  rcases List.prefix_or_prefix_of_prefix pref (List.prefix_append E [1+s]) with h|h
  · exact Nat.le_of_eq (long_prefix_twos (g:=g) nz rfl only H E l h high read x mem)
  · have full := pref.sublist.subset mem
    rcases List.mem_append.mp full with inside|last
    · exact Nat.le_of_eq (long_prefix_twos (g:=g) nz rfl only E E l (List.prefix_refl _)
        (fun y hy => high y (h.sublist.subset hy)) read x inside)
    · have eqn : x=1+s := by simpa using last
      omega

end ThreeWordCodes.CrossedCase
