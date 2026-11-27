module

public import SmallestNoncompletable.Reductions

/-! # Renaming letters, and two conceptual cases

A letter map which is injective on the letters of `W` transports unique decodability to the
image and reducibility from the image back to `W`. The cases of one long word and of words of
even lengths are reducible without computation. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- The letters occurring in `W`. -/
def Letters (W : Finset (Word A)) : Set A := {x | ∃ w ∈ W, x ∈ w}

section Renaming

variable {W : Finset (Word A)} {ι : A → B} (hι : Set.InjOn ι (Letters W))
include hι

omit [DecidableEq A] [DecidableEq B] in
theorem map_inj {u v : Word A} (hu : ∀ x ∈ u, x ∈ Letters W) (hv : ∀ x ∈ v, x ∈ Letters W)
    (h : u.map ι = v.map ι) : u = v := by
  induction u generalizing v with
  | nil => simpa [eq_comm] using h
  | cons x u ih =>
    cases v with
    | nil => simp at h
    | cons y v =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hι (hu x (by simp)) (hv y (by simp)) h.1,
        ih (fun z hz => hu z (by simp [hz])) (fun z hz => hv z (by simp [hz])) h.2]

omit hι [DecidableEq A] [DecidableEq B] in
theorem letters_of_mem {w : Word A} (hw : w ∈ W) : ∀ x ∈ w, x ∈ Letters W :=
  fun _ hx => ⟨w, hw, hx⟩

omit [DecidableEq A] in
theorem uniquelyDecodable_image (hW : IsUniquelyDecodable (W : Set (Word A))) :
    IsUniquelyDecodable ((W.image (List.map ι) : Finset (Word B)) : Set (Word B)) := by
  intro xs ys hxs hys e
  have pull : ∀ zs : List (Word B), (∀ z ∈ zs, z ∈ ((W.image (List.map ι) : Finset _) : Set _)) →
      ∃ zs' : List (Word A), (∀ z ∈ zs', z ∈ W) ∧ zs'.map (List.map ι) = zs := by
    intro zs hzs
    induction zs with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons z zs ih =>
      obtain ⟨zs', h1, h2⟩ := ih fun y hy => hzs y (by simp [hy])
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp (hzs z (by simp))
      refine ⟨z' :: zs', fun a ha => ?_, by simp [h2]⟩
      rcases List.mem_cons.mp ha with rfl | ha
      exacts [hz', h1 a ha]
  obtain ⟨xs', hx1, rfl⟩ := pull xs hxs
  obtain ⟨ys', hy1, rfl⟩ := pull ys hys
  have hflat : xs'.flatten = ys'.flatten := by
    apply map_inj hι
    · intro x hx
      obtain ⟨w, hw, hxw⟩ := List.mem_flatten.mp hx
      exact ⟨w, hx1 w hw, hxw⟩
    · intro x hx
      obtain ⟨w, hw, hxw⟩ := List.mem_flatten.mp hx
      exact ⟨w, hy1 w hw, hxw⟩
    · simpa [List.map_flatten] using e
  rw [hW xs' ys' hx1 hy1 hflat]

/-- The tree pulled back by a left inverse of the renaming. -/
theorem tree_pullback [Nonempty A] {I' : Finset (Word B)} (hRP : RootedPrefixClosed I')
    (hlet : ∀ p ∈ I', ∀ y ∈ p, ∃ w ∈ W.image (List.map ι), y ∈ w) :
    let κ := Function.invFunOn ι (Letters W)
    let I := I'.image (List.map κ)
    RootedPrefixClosed I ∧ (∀ p ∈ I, ∀ x ∈ p, ∃ w ∈ W, x ∈ w) ∧
      (∀ w node : Word A, (∀ x ∈ w, x ∈ Letters W) → (∀ x ∈ node, x ∈ Letters W) →
        readTree I node w = readTree I' (node.map ι) (w.map ι)) ∧
      ∀ x ∈ Letters W, [x] ∈ I ↔ [ι x] ∈ I' := by
  intro κ I
  have hleft : ∀ x ∈ Letters W, κ (ι x) = x := fun x hx => hι.leftInvOn_invFunOn hx
  -- the letters of `I'` are images
  have himg : ∀ p ∈ I', ∀ y ∈ p, ∃ x ∈ Letters W, ι x = y := by
    intro p hp y hy
    obtain ⟨w', hw', hyw⟩ := hlet p hp y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hyw
    exact ⟨x, ⟨w, hw, hx⟩, rfl⟩
  have hback : ∀ p ∈ I', (p.map κ).map ι = p := by
    intro p hp
    rw [List.map_map]
    conv_rhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro y hy
    obtain ⟨x, hx, rfl⟩ := himg p hp y hy
    simp [Function.comp_apply, hleft x hx]
  have hlettersI : ∀ p ∈ I, ∀ x ∈ p, x ∈ Letters W := by
    intro p hp x hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨x, hx', rfl⟩ := himg p' hp' y hy
    rw [hleft x hx']
    exact hx'
  have hmem : ∀ p : Word A, (∀ x ∈ p, x ∈ Letters W) → (p ∈ I ↔ p.map ι ∈ I') := by
    intro p hp
    constructor
    · intro h
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp h
      rwa [hback p' hp']
    · intro h
      refine Finset.mem_image.mpr ⟨p.map ι, h, ?_⟩
      rw [List.map_map]
      conv_rhs => rw [← List.map_id p]
      exact List.map_congr_left fun x hx => hleft x (hp x hx)
  refine ⟨⟨Finset.mem_image.mpr ⟨[], hRP.root, rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro r p hp hr
    have hpl := hlettersI p hp
    have hrl : ∀ x ∈ r, x ∈ Letters W := fun x hx => hpl x (hr.subset hx)
    rw [hmem r hrl]
    exact hRP.closed ((hmem p hpl).mp hp) (hr.map ι)
  · intro p hp x hx
    obtain ⟨w, hw, hxw⟩ := hlettersI p hp x hx
    exact ⟨w, hw, hxw⟩
  · intro w
    induction w with
    | nil => intro node _ _; simp [readTree]
    | cons x w ih =>
      intro node hw hn
      have hx : x ∈ Letters W := hw x (by simp)
      have hw' : ∀ y ∈ w, y ∈ Letters W := fun y hy => hw y (by simp [hy])
      have hnx : ∀ y ∈ node ++ [x], y ∈ Letters W := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hn y hy
        · rw [List.mem_singleton.mp hy]; exact hx
      simp only [readTree, List.map_cons]
      have e : (node ++ [x] ∈ I) ↔ (node.map ι ++ [ι x] ∈ I') := by
        rw [hmem _ hnx]; simp
      by_cases h : node ++ [x] ∈ I
      · rw [ite_eq_left h, ite_eq_left (e.mp h), ih _ hw' hnx]; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (e.mpr h')), ih _ hw' (by simp)]; rfl
  · intro x hx
    rw [hmem [x] (by simp [hx])]
    rfl

/-- **Reducibility transfers back along an injective renaming.** -/
theorem reducible_of_image (h : Reducible (W.image (List.map ι))) : Reducible W := by
  classical
  have hmapW : ∀ w ∈ W, ∀ x ∈ w, x ∈ Letters W := fun w hw => letters_of_mem hw
  rcases h with h | h | ⟨x', y', hxy, hx, hy, hiso⟩ | ⟨I', hRP, hlet, hread, hwit⟩ |
    ⟨I', hRP, hlet, hread, hwit⟩
  · left
    intro u hu v hv huv
    have hu' := Finset.mem_coe.mp hu
    have hv' := Finset.mem_coe.mp hv
    exact map_inj hι (hmapW u hu') (hmapW v hv')
      (h _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu')) _
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv')) (huv.map ι))
  · right; left
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    have hu' := Finset.mem_coe.mp hu
    have hv' := Finset.mem_coe.mp hv
    have e := h _ ⟨u.map ι, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu'), rfl⟩
      _ ⟨v.map ι, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv'), rfl⟩
      (by rw [← List.map_reverse, ← List.map_reverse]; exact huv.map ι)
    rw [List.reverse_inj] at e
    rw [map_inj hι (hmapW u hu') (hmapW v hv') e]
  · right; right; left
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy
    obtain ⟨x, rfl⟩ : ∃ x, u = [x] := by
      rcases u with _ | ⟨x, _ | ⟨z, u⟩⟩ <;> simp at hux
      exact ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y, v = [y] := by
      rcases v with _ | ⟨y, _ | ⟨z, v⟩⟩ <;> simp at hvy
      exact ⟨y, rfl⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hux hvy
    subst hux hvy
    refine ⟨x, y, fun e => hxy (by rw [e]), hu, hv, ?_⟩
    intro w hw hne hxw
    apply hiso (w.map ι) (Finset.mem_image_of_mem _ hw)
    · intro e
      exact hne (map_inj hι (hmapW w hw) (hmapW _ hu) (by simpa using e))
    · exact List.mem_map_of_mem hxw
  · right; right; right; left
    have hne : Nonempty A := by
      obtain ⟨w', hw', y, hyw, -⟩ := hwit
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨x, -, -⟩ := List.mem_map.mp hyw
      exact ⟨x⟩
    obtain ⟨hRP', hlet', hread', hsing⟩ := tree_pullback hι hRP hlet
    refine ⟨_, hRP', hlet', ?_, ?_⟩
    · intro w hw
      rw [hread' w [] (hmapW w hw) (by simp)]
      exact hread _ (Finset.mem_image_of_mem _ hw)
    · obtain ⟨w', hw', y, hyw, hyI⟩ := hwit
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨x, hxw, rfl⟩ := List.mem_map.mp hyw
      exact ⟨w, hw, x, hxw, (hsing x ⟨w, hw, hxw⟩).mpr hyI⟩
  · right; right; right; right
    have hne : Nonempty A := by
      obtain ⟨w', hw', y, hyw, -⟩ := hwit
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨x, -, -⟩ := List.mem_map.mp hyw
      exact ⟨x⟩
    obtain ⟨hRP', hlet', hread', hsing⟩ := tree_pullback hι hRP hlet
    refine ⟨_, hRP', hlet', ?_, ?_⟩
    · intro w hw
      rw [hread' w.reverse [] (fun x hx => hmapW w hw x (List.mem_reverse.mp hx)) (by simp),
        List.map_reverse]
      exact hread _ (Finset.mem_image_of_mem _ hw)
    · obtain ⟨w', hw', y, hyw, hyI⟩ := hwit
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨x, hxw, rfl⟩ := List.mem_map.mp hyw
      exact ⟨w, hw, x, hxw, (hsing x ⟨w, hw, hxw⟩).mpr hyI⟩

end Renaming

/-! ## One long word -/

/-- A code whose words, except one, are letters, is prefix-free or has a letter which starts
no word. -/
theorem reducible_of_one_long {W : Finset (Word A)} (hW : IsUniquelyDecodable (W : Set (Word A)))
    {w : Word A} (hw : w ∈ W) (hlong : 2 ≤ w.length) (hrest : ∀ v ∈ W, v ≠ w → v.length = 1) :
    Reducible W := by
  classical
  obtain ⟨x₀, w', rfl⟩ : ∃ x₀ w', w = x₀ :: w' := by
    rcases w with _ | ⟨x₀, w'⟩
    · simp at hlong
    · exact ⟨x₀, w', rfl⟩
  by_cases hx₀ : [x₀] ∈ W
  · -- some letter of `w` is not a letter codeword
    by_cases hall : ∀ x ∈ x₀ :: w', [x] ∈ W
    · exfalso
      have hfl : ∀ l : List A, (l.map fun x => [x]).flatten = l := fun l => by
        induction l <;> simp_all
      have := hW [x₀ :: w'] ((x₀ :: w').map fun x => [x]) (by simpa using hw)
        (by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact hall x hx)
        (by rw [hfl]; simp)
      have h1 := congrArg List.length this
      simp only [List.length_nil, List.length_map, List.length_cons] at h1
      simp only [List.length_cons] at hlong
      omega
    · push Not at hall
      obtain ⟨d, hd, hdW⟩ := hall
      refine reducible_of_not_first (x := d) ⟨_, hw, hd⟩ ?_
      intro v hv hvd
      by_cases hvw : v = x₀ :: w'
      · subst hvw
        simp at hvd
        subst hvd
        exact hdW hx₀
      · have := hrest v hv hvw
        obtain ⟨y, rfl⟩ : ∃ y, v = [y] := by
          rcases v with _ | ⟨y, _ | ⟨z, v⟩⟩ <;> simp at this
          exact ⟨y, rfl⟩
        simp at hvd
        subst hvd
        exact hdW hv
  · -- the code is prefix-free
    left
    intro u hu v hv huv
    simp only [Finset.mem_coe] at hu hv
    by_cases hl : u.length = v.length
    · exact huv.eq_of_length hl
    · exfalso
      have hlt : u.length < v.length := lt_of_le_of_ne huv.length_le hl
      have hvw : v = x₀ :: w' := by
        by_contra hne
        have := hrest v hv hne
        have hu0 : u ≠ [] := fun h => hW.epsilon_notMem (h ▸ hu)
        have := List.length_pos_iff.mpr hu0
        omega
      have huw : u ≠ x₀ :: w' := fun h => by rw [h, hvw] at hlt; omega
      have hu1 := hrest u hu huw
      obtain ⟨y, rfl⟩ : ∃ y, u = [y] := by
        rcases u with _ | ⟨y, _ | ⟨z, u⟩⟩ <;> simp at hu1
        exact ⟨y, rfl⟩
      rw [hvw] at huv
      obtain ⟨t, ht⟩ := huv
      simp at ht
      rw [← ht.1] at hx₀
      exact hx₀ hu

/-! ## Words of even length -/

theorem readTree_pairs (L : Finset A) :
    ∀ w : Word A, (∀ x ∈ w, x ∈ L) → Even w.length →
      readTree (insert [] (L.image fun x => [x])) [] w = true
  | [], _, _ => by simp [readTree]
  | [_], _, h => by simp at h
  | x :: y :: w, hw, h => by
    have hx : [] ++ [x] ∈ insert [] (L.image fun x => [x]) := by
      simp [hw x (by simp)]
    have hxy : ¬ ([] ++ [x]) ++ [y] ∈ insert [] (L.image fun x => [x]) := by simp
    rw [readTree, ite_eq_left hx, readTree, ite_eq_right hxy]
    exact readTree_pairs L w (fun z hz => hw z (by simp [hz]))
      (by simpa [Nat.even_add_one] using h)

theorem reducible_of_even {W : Finset (Word A)} (hne : ∃ w ∈ W, w ≠ [])
    (heven : ∀ w ∈ W, Even w.length) : Reducible W := by
  classical
  set L : Finset A := W.biUnion fun w => w.toFinset
  have hL : ∀ w ∈ W, ∀ x ∈ w, x ∈ L := fun w hw x hx =>
    Finset.mem_biUnion.mpr ⟨w, hw, List.mem_toFinset.mpr hx⟩
  right; right; right; left
  refine ⟨insert [] (L.image fun x => [x]), ⟨by simp, ?_⟩, ?_, ?_, ?_⟩
  · intro p w hw hp
    simp only [Finset.mem_insert, Finset.mem_image] at hw ⊢
    rcases hw with rfl | ⟨x, hx, rfl⟩
    · exact Or.inl (List.eq_nil_of_prefix_nil hp)
    · rcases List.prefix_cons_iff.mp hp with h | ⟨t, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, by rw [List.eq_nil_of_prefix_nil h]⟩
  · intro p hp x hx
    simp only [Finset.mem_insert, Finset.mem_image] at hp
    rcases hp with rfl | ⟨y, hy, rfl⟩
    · simp at hx
    · rw [List.mem_singleton.mp hx]
      obtain ⟨w, hw, hyw⟩ := Finset.mem_biUnion.mp hy
      exact ⟨w, hw, List.mem_toFinset.mp hyw⟩
  · intro w hw
    exact readTree_pairs L w (hL w hw) (heven w hw)
  · obtain ⟨w, hw, hwne⟩ := hne
    obtain ⟨x, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
    exact ⟨_, hw, x, by simp, by simp [hL _ hw x (by simp)]⟩

end SmallestNoncompletable
