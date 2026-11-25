import OAI.Hierarchy.DegreeBorder
import OAI.Hierarchy.ModelMap

namespace OAI
/-! # Exact formula and ABP families in their degree-component border models -/

namespace Hierarchy

variable {F : Type*} {σ : Type} [Field F] {d s : ℕ} {f : MvPolynomial σ F}

/-- Extending all scalar leaves preserves the gate count of the formula. -/
theorem HasFormula.degreeBorderAtMost (h : HasFormula s f) : DegreeBorderAtMost HasFormula d s f :=
  degreeBorderAtMost_of_exact_map (hasFormula_map (algebraMap F (AlgebraicClosure F)) h)

/-- Extending the scalar coefficients of every affine edge preserves vertices and edges. -/
theorem HasABP.degreeBorderAtMost [Fintype σ] (h : HasABP s f) : DegreeBorderAtMost HasABP d s f :=
  degreeBorderAtMost_of_exact_map (hasABP_map (algebraMap F (AlgebraicClosure F)) h)

variable {ι : ℕ → Type} [∀ n, Fintype (ι n)] {p : Computability.VPVNP.Family F ι}

/-- The same polynomial formula-size bound works for every sequence of projected degrees. -/
theorem isVF_hasPolynomialBorder (h : IsVF p) (degree : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, Computability.VPVNP.PolynomiallyBounded s ∧
      ∀ n, DegreeBorderAtMost HasFormula (degree n) (s n) (p n) := by
  obtain ⟨_, family, output, bounded⟩ := h
  exact ⟨_, bounded, fun n => HasFormula.degreeBorderAtMost ⟨family n, output n, le_rfl⟩⟩

/-- The same polynomial branching-program size bound works for every sequence of degrees. -/
theorem isVBP_hasPolynomialBorder (h : IsVBP p) (degree : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, Computability.VPVNP.PolynomiallyBounded s ∧
      ∀ n, DegreeBorderAtMost HasABP (degree n) (s n) (p n) := by
  obtain ⟨_, family, output, bounded⟩ := h
  exact ⟨_, bounded, fun n => HasABP.degreeBorderAtMost ⟨family n, output n, le_rfl⟩⟩

end Hierarchy

end OAI
