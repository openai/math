import OAI.Hierarchy.FormulaParameters
import OAI.Hierarchy.ABPParameters

namespace OAI
/-! # Extending arithmetic formulas and branching programs along a field homomorphism -/

namespace Hierarchy
noncomputable section
variable {F : Type*} {K : Type*} {σ : Type} [Field F] [Field K] (φ : F →+* K)

/-- Replace each scalar leaf by its image in the target field. -/
abbrev Formula.map (f : Formula F σ) : Formula K σ := f.relabel φ

@[simp] theorem Formula.cost_map (f : Formula F σ) : (f.map φ).cost = f.cost :=
  f.cost_relabel φ

@[simp] theorem Formula.polynomial_map (f : Formula F σ) :
    (f.map φ).polynomial = MvPolynomial.map φ f.polynomial := by
  simpa [Formula.map] using (Formula.specialize_relabel (id : F → F) φ f).symm

theorem hasFormula_map {s : ℕ} {p : MvPolynomial σ F} (h : HasFormula s p) :
    HasFormula s (MvPolynomial.map φ p) := by
  obtain ⟨f, rfl, size⟩ := h
  exact ⟨f.map φ, f.polynomial_map φ, by simpa using size⟩

/-- Replace every coefficient in the edge labels without changing the graph. -/
abbrev ABP.map (g : ABP F σ) : ABP K σ := g.relabel φ

@[simp] theorem ABP.size_map (g : ABP F σ) : (g.map φ).size = g.size :=
  g.size_relabel φ

@[simp] theorem ABP.polynomial_map [Fintype σ] (g : ABP F σ) :
    (g.map φ).polynomial = MvPolynomial.map φ g.polynomial := by
  simpa [ABP.map] using (ABP.specialize_relabel (id : F → F) φ g).symm

theorem hasABP_map [Fintype σ] {s : ℕ} {p : MvPolynomial σ F} (h : HasABP s p) :
    HasABP s (MvPolynomial.map φ p) := by
  obtain ⟨g, rfl, size⟩ := h
  exact ⟨g.map φ, g.polynomial_map φ, by simpa using size⟩


end
end Hierarchy

end OAI
