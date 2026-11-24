import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Composition of polynomial projections

Following two variable-or-constant substitutions gives another substitution of
the same kind. For families, the source length is obtained by composing the two
polynomially bounded index functions.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ τ υ : Type*}

/-- Follow a variable of the intermediate polynomial through the second projection. -/
def Projection.comp (ψ : Projection R τ υ) (φ : Projection R σ τ) : Projection R σ υ :=
  fun i => (φ i).elim ψ Sum.inr

theorem Projection.hom_comp [CommSemiring R] (ψ : Projection R τ υ) (φ : Projection R σ τ) :
    (ψ.comp φ).hom = ψ.hom.comp φ.hom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [Projection.hom]
  · intro i
    cases hi : φ i <;> simp [Projection.comp, Projection.hom, hi]

/-- A p-projection of a p-projection is a p-projection. -/
theorem PProjects.trans {F : Type*} [Field F] {X Y Z : ℕ → Type}
    {p : Family F X} {q : Family F Y} {s : Family F Z}
    (hpq : PProjects p q) (hqs : PProjects q s) : PProjects p s := by
  obtain ⟨r, hr, hφ⟩ := hpq
  obtain ⟨t, ht, hψ⟩ := hqs
  refine ⟨fun n => t (r n), ht.comp hr, fun n => ?_⟩
  obtain ⟨φ, heqφ⟩ := hφ n
  obtain ⟨ψ, heqψ⟩ := hψ (r n)
  exact ⟨φ.comp ψ, by rw [Projection.hom_comp, RingHom.comp_apply, heqψ, heqφ]⟩

end VPVNP
end Computability
end OAI
