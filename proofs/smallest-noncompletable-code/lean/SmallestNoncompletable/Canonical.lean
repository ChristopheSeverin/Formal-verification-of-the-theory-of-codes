module

public import SmallestNoncompletable.SearchSound
public import SmallestNoncompletable.Transfer
public import Mathlib.Data.List.Sort

/-! # The canonical form of a code

Sort the long words by length, and rename the letters of their concatenation by first
appearance, the letter codewords and the other letters separately. The result is a two-counter
restricted growth string, so the search covers it. -/

@[expose] public section

namespace SmallestNoncompletable

open ThreeWordCodes InformationTheory Search

theorem Ext.of_append {s : ℕ} : ∀ {u k : ℕ} {a b : List ℕ}, Ext s u k (a ++ b) → Ext s u k a
  | _, _, [], _, _ => trivial
  | u, k, j :: a, b, h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, Ext.of_append h3⟩
    · exact Or.inr ⟨h1, h2, Ext.of_append h3⟩

/-- **Renaming by first appearance.** Letters with `isS` get the next value below `s`, the
other letters the next value from `s` on. -/
theorem rename_exists {A : Type*} [DecidableEq A] (isS : A → Prop) [DecidablePred isS]
    (s : ℕ) (Sfin : Finset A) (hS : ∀ x, isS x → x ∈ Sfin) (hs : Sfin.card = s) :
    ∀ (p : List A) (V : Finset A) (ρ : A → ℕ) (u k : ℕ),
      (∀ x ∈ V, isS x → ρ x < u) → (∀ x ∈ V, ¬ isS x → s ≤ ρ x ∧ ρ x < k) →
      Set.InjOn ρ V → (V.filter isS).card = u → s ≤ k →
      ∃ ρ' : A → ℕ, (∀ x ∈ V, ρ' x = ρ x) ∧ Set.InjOn ρ' ↑(V ∪ p.toFinset) ∧
        (∀ x ∈ V ∪ p.toFinset, isS x → ρ' x < s) ∧
        (∀ x ∈ V ∪ p.toFinset, ¬ isS x → s ≤ ρ' x) ∧ Ext s u k (p.map ρ')
  | [], V, ρ, u, k, h1, h2, hinj, hu, hk => by
    refine ⟨ρ, fun _ _ => rfl, by simpa using hinj, ?_, ?_, trivial⟩
    · intro x hx hxs
      simp only [List.toFinset_nil, Finset.union_empty] at hx
      have := h1 x hx hxs
      have : u ≤ s := hu ▸ hs ▸ Finset.card_le_card (fun y hy => hS y (Finset.mem_filter.mp hy).2)
      omega
    · intro x hx hxs
      simp only [List.toFinset_nil, Finset.union_empty] at hx
      exact (h2 x hx hxs).1
  | x :: p, V, ρ, u, k, h1, h2, hinj, hu, hk => by
    have hus : u ≤ s := hu ▸ hs ▸ Finset.card_le_card (fun y hy => hS y (Finset.mem_filter.mp hy).2)
    by_cases hxV : x ∈ V
    · obtain ⟨ρ', hagree, hinj', hb1, hb2, hext⟩ := rename_exists isS s Sfin hS hs p V ρ u k
        h1 h2 hinj hu hk
      refine ⟨ρ', hagree, ?_, ?_, ?_, ?_⟩
      · have : V ∪ (x :: p).toFinset = V ∪ p.toFinset := by
          ext y; simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
          constructor
          · rintro (h | rfl | h)
            exacts [Or.inl h, Or.inl hxV, Or.inr h]
          · rintro (h | h)
            exacts [Or.inl h, Or.inr (Or.inr h)]
        rw [this]; exact hinj'
      · intro y hy hys
        apply hb1 y _ hys
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hy ⊢
        rcases hy with h | rfl | h
        exacts [Or.inl h, Or.inl hxV, Or.inr h]
      · intro y hy hys
        apply hb2 y _ hys
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hy ⊢
        rcases hy with h | rfl | h
        exacts [Or.inl h, Or.inl hxV, Or.inr h]
      · simp only [List.map_cons]
        by_cases hxs : isS x
        · have := h1 x hxV hxs
          rw [hagree x hxV]
          left
          refine ⟨by omega, by omega, ?_⟩
          rwa [show max u (ρ x + 1) = u by omega]
        · have := h2 x hxV hxs
          rw [hagree x hxV]
          right
          refine ⟨this.1, by omega, ?_⟩
          rwa [show max k (ρ x + 1) = k by omega]
    · -- a new letter gets the next value of its kind
      have hupd : ∀ (v : ℕ), ∀ y ∈ V, Function.update ρ x v y = ρ y := fun v y hy =>
        Function.update_of_ne (by rintro rfl; exact hxV hy) _ _
      have hinjnew : ∀ v : ℕ, (∀ y ∈ V, ρ y ≠ v) → Set.InjOn (Function.update ρ x v) ↑(insert x V) := by
        intro v hv y hy z hz e
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hy hz
        rcases hy with rfl | hy <;> rcases hz with rfl | hz
        · rfl
        · rw [Function.update_self, hupd v z hz] at e
          exact absurd e.symm (hv z hz)
        · rw [Function.update_self, hupd v y hy] at e
          exact absurd e (hv y hy)
        · rw [hupd v y hy, hupd v z hz] at e
          exact hinj hy hz e
      have hU : insert x V ∪ p.toFinset = V ∪ (x :: p).toFinset := by
        ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      by_cases hxs : isS x
      · have hcard : ((insert x V).filter isS).card = u + 1 := by
          rw [Finset.filter_insert, ite_eq_left hxs, Finset.card_insert_of_notMem
            (fun h => hxV (Finset.mem_filter.mp h).1), hu]
        have hlt : u < s := by
          have := Finset.card_le_card (show (insert x V).filter isS ⊆ Sfin from
            fun y hy => hS y (Finset.mem_filter.mp hy).2)
          omega
        obtain ⟨ρ', hagree, hinj', hb1, hb2, hext⟩ := rename_exists isS s Sfin hS hs p (insert x V)
          (Function.update ρ x u) (u + 1) k
          (by
            intro y hy hys
            rcases Finset.mem_insert.mp hy with rfl | hy
            · simp
            · rw [hupd u y hy]; have := h1 y hy hys; omega)
          (by
            intro y hy hys
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact absurd hxs hys
            · rw [hupd u y hy]; exact h2 y hy hys)
          (hinjnew u (by
            intro y hy e
            by_cases hys : isS y
            · have := h1 y hy hys; omega
            · have := h2 y hy hys; omega))
          hcard hk
        refine ⟨ρ', fun y hy => ?_, by rw [← hU]; exact hinj', fun y hy => hb1 y (hU ▸ hy),
          fun y hy => hb2 y (hU ▸ hy), ?_⟩
        · rw [hagree y (Finset.mem_insert_of_mem hy), hupd u y hy]
        · simp only [List.map_cons]
          have hx : ρ' x = u := by rw [hagree x (Finset.mem_insert_self _ _)]; simp
          rw [hx]
          left
          refine ⟨hlt, le_rfl, ?_⟩
          rwa [show max u (u + 1) = u + 1 by omega]
      · obtain ⟨ρ', hagree, hinj', hb1, hb2, hext⟩ := rename_exists isS s Sfin hS hs p (insert x V)
          (Function.update ρ x k) u (k + 1)
          (by
            intro y hy hys
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact absurd hys hxs
            · rw [hupd k y hy]; exact h1 y hy hys)
          (by
            intro y hy hys
            rcases Finset.mem_insert.mp hy with rfl | hy
            · simp; omega
            · rw [hupd k y hy]; have := h2 y hy hys; omega)
          (hinjnew k (by
            intro y hy e
            by_cases hys : isS y
            · have := h1 y hy hys; omega
            · have := h2 y hy hys; omega))
          (by rw [Finset.filter_insert, ite_eq_right hxs]; exact hu) (by omega)
        refine ⟨ρ', fun y hy => ?_, by rw [← hU]; exact hinj', fun y hy => hb1 y (hU ▸ hy),
          fun y hy => hb2 y (hU ▸ hy), ?_⟩
        · rw [hagree y (Finset.mem_insert_of_mem hy), hupd k y hy]
        · simp only [List.map_cons]
          have hx : ρ' x = k := by rw [hagree x (Finset.mem_insert_self _ _)]; simp
          rw [hx]
          right
          refine ⟨hk, le_rfl, ?_⟩
          rwa [show max k (k + 1) = k + 1 by omega]

end SmallestNoncompletable
