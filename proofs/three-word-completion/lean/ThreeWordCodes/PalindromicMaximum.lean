module

public import ThreeWordCodes.PalindromicRawCuts
public import ThreeWordCodes.DominatedBlocks

/-! # Choosing a maximum block absent from the preceding gaps -/

@[expose] public section
namespace ThreeWordCodes.Palindromic
open BinaryGaps

theorem Origin.host {m r : ℕ} {cuts : List (List ℕ)} {us : List ℕ} (origin : Origin m cuts r us) :
    ∃ H∈[m]::cuts, ∃ pre z,H=pre++z::us ∧ r≤z := by
  rcases origin with ⟨rfl,le⟩ | ⟨p,hp,pre,z,form,le⟩
  · exact ⟨[m],by simp,[],m,rfl,le⟩
  · exact ⟨p,by simp [hp],pre,z,form,le⟩

theorem Origin.ends_short {m r : ℕ} {cuts : List (List ℕ)} {us : List ℕ} (origin : Origin m cuts r us)
    (last : ∀ p∈cuts,∃ pre n,p=pre++[n] ∧ n≤m) :
    ∃ pref n,r::us=pref++[n] ∧ n≤m := by
  obtain ⟨H,mem,pre,z,form,le⟩ := origin.host
  have endH : ∃ pre n,H=pre++[n] ∧ n≤m := by
    rcases List.mem_cons.mp mem with rfl | hc
    · exact ⟨[],m,rfl,le_rfl⟩
    · exact last H hc
  obtain ⟨old,n,snoc,small⟩ := endH
  induction us using List.reverseRecOn with
  | nil =>
    have same : z=n := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? (form.symm.trans snoc)
    exact ⟨[],r,rfl,by omega⟩
  | append_singleton us t _ =>
    have eqn : (pre++z::us)++[t]=old++[n] := by simpa using form.symm.trans snoc
    obtain rfl : t=n := by simpa only [List.getLast?_concat,Option.some.injEq] using congrArg List.getLast? eqn
    exact ⟨r::us,t,rfl,small⟩

/-- Only one extra leaf is needed when the next block is long and no
coordinatewise larger copy of it occurs in the cut. -/
theorem absent_block_completion (s k l m : ℕ) (U F rest : List ℕ) (z : Word Bool)
    (read : Reading s (U++F++rest) z) (height : l≤m) (short : m≤k+l)
    (low : ∀ n∈U++F++rest,l≤n) (ends : EndsAt m U) (ne : F≠[])
    (long : ∀ n∈F,m<n) (absent : ∀ W,Dominated F W → ¬ W <:+: U)
    (ending : z.getLast?=some b) : Completable (triple s k l z) := by
  let front := F.dropLast
  let g := F.getLast ne
  have snoc : front++[g]=F := List.dropLast_concat_getLast ne
  have whole : U++front++g::rest=U++F++rest := by rw [←snoc]; simp [List.append_assoc]
  have gLong := long g (by rw [←snoc]; simp)
  have leafLast : ∀ p∈[U],∃ pre n,p=pre++[n] ∧ n≤m := by
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    obtain ⟨u,eqn⟩ := ends
    exact ⟨u,m,eqn,le_rfl⟩
  apply raw_selection s k l l m [U] U front g rest z (whole.symm ▸ read) le_rfl height (by omega) (by omega) (by simp)
    (whole.symm ▸ low) (by intro p hp n hn; obtain rfl := List.mem_singleton.mp hp; exact low n (by simp [hn]))
    leafLast (by simp) _ ending
  intro r us origin
  constructor
  · intro early
    obtain ⟨p,n,form,small⟩ := origin.ends_short leafLast
    have hit : n∈front := early.sublist.subset (by simp [form])
    have := long n (by rw [←snoc]; simp [hit])
    omega
  · intro j tail hit le
    obtain ⟨H,mem,old,v,host,bound⟩ := origin.host
    obtain ⟨W,placed,dom⟩ := increased_ends bound le hit
    rw [snoc] at dom
    have infx : W <:+: H := ⟨old,tail,by rw [host,placed]; simp⟩
    rcases List.mem_cons.mp mem with rfl | hu
    · have wn : W≠[] := by intro nil; exact ne (List.forall₂_nil_right_iff.mp (nil ▸ dom))
      have hm : m∈W := by
        obtain ⟨u,us,rfl⟩ := List.exists_cons_of_ne_nil wn
        have elem := infx.sublist.subset (show u∈u::us by simp)
        simp only [List.mem_singleton] at elem
        simp [elem]
      exact Nat.lt_irrefl _ (dom.lower long m hm)
    · obtain rfl := List.mem_singleton.mp hu
      exact absent _ dom infx

theorem first_maximum_completion (s k l m : ℕ) (first F : List ℕ) (bs : List (List ℕ)) (extra : List ℕ) (z : Word Bool)
    (read : Reading s (joinBlocks m (first::bs)++extra) z) (extraLow : ∀ n∈extra,l≤n) (height : l≤m) (short : m≤k+l)
    (ne : F≠[]) (different : first≠F) (occurs : F∈first::bs) (long : ∀ B∈first::bs,∀ n∈B,m<n)
    (top : ∀ B∈first::bs,blockWeight B≤blockWeight F) (ending : z.getLast?=some b) :
    Completable (triple s k l z) := by
  obtain ⟨early,after,split,miss⟩ := split_first F bs ((List.mem_cons.mp occurs).resolve_left (Ne.symm different))
  let past := first::early
  let U := separated m past
  have splitAll : first::bs=past++F::after := by simp [past,split]
  have ff : F <+: joinBlocks m (F::after) := by
    cases after with
    | nil => simp [joinBlocks]
    | cons t ts => exact ⟨m::joinBlocks m (t::ts),by simp [joinBlocks,List.append_assoc]⟩
  obtain ⟨tail,whereF⟩ := ff
  have shape : joinBlocks m (first::bs)=U++F++tail := by
    rw [splitAll,cut_blocks _ _ _ (by simp),←whereF]; simp [U,List.append_assoc]
  have ends : EndsAt m U := by
    have np : past≠[] := by simp [past]
    have cut := List.dropLast_concat_getLast np
    change EndsAt m (separated m past)
    rw [←cut,separated_append,separated_singleton]
    exact ⟨_,(List.append_assoc ..).symm⟩
  have total : joinBlocks m (first::bs)++extra=U++F++(tail++extra) := by rw [shape,List.append_assoc]
  apply absent_block_completion s k l m U F (tail++extra) z (total ▸ read) height short _ ends ne (long F occurs) _ ending
  · intro n hn
    rcases List.mem_append.mp (total.symm ▸ hn : n∈joinBlocks m (first::bs)++extra) with early | late
    · exact height.trans (blocks_lower m _ long n early)
    · exact extraLow n late
  · intro W dom infx
    have inWhole (B : List ℕ) (hb : B∈past) : B∈first::bs := splitAll.symm ▸ List.mem_append_left _ hb
    have atF := (maximum_dominated ne (long F occurs) (fun B hb => top B (inWhole B hb)) dom infx).2
    rcases List.mem_cons.mp atF with eq | here
    · exact different eq.symm
    · exact miss here

end ThreeWordCodes.Palindromic
