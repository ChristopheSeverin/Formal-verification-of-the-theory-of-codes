module

public import NonfreeBinaryFactor.Factorization
public import NonfreeBinaryFactor.Nonfreeness

/-! # A nonfree factor of the binary free monoid -/

@[expose] public section
namespace NonfreeBinaryFactor

universe u

/-- There is a nonfree submonoid M of {a,b}* such that each binary word
has a unique expression (ab)^i b^j m a^k (aabb)^l with m in M. -/
theorem exists_nonfree_factor :
    ∃ M : Submonoid (FreeMonoid Bool),
      (∀ X : Type u, ¬ Nonempty (M ≃* FreeMonoid X)) ∧
      ∀ w : FreeMonoid Bool, ∃! d : ℕ × ℕ × M × ℕ × ℕ, assemble M d = w :=
  ⟨middleSubmonoid, middle_not_free, assemble_bijective.existsUnique⟩

end NonfreeBinaryFactor
