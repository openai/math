import OAI.Hierarchy.Models

namespace OAI
/-! # Variable-or-scalar projections of arithmetic formulas -/

namespace Hierarchy

variable {F : Type*} {σ τ : Type}

namespace Formula

/-- Substitute a variable or scalar at every input leaf, retaining every binary gate. -/
def project (φ : Computability.VPVNP.Projection F σ τ) : Formula F σ → Formula F τ
  | .constant c => .constant c
  | .input i => (φ i).elim .input .constant
  | .add f g => .add (project φ f) (project φ g)
  | .sub f g => .sub (project φ f) (project φ g)
  | .mul f g => .mul (project φ f) (project φ g)

@[simp] theorem cost_project (φ : Computability.VPVNP.Projection F σ τ) (f : Formula F σ) :
    (f.project φ).cost = f.cost := by
  induction f with
  | input i => cases h : φ i <;> simp [project, h, MatrixMultiplication.Arithmetic.Expression.cost]
  | _ => simp_all [project, MatrixMultiplication.Arithmetic.Expression.cost]

@[simp] theorem polynomial_project [Field F] (φ : Computability.VPVNP.Projection F σ τ) (f : Formula F σ) :
    (f.project φ).polynomial = φ.hom f.polynomial := by
  induction f with
  | input i => cases h : φ i <;> simp [project, polynomial,
      LinearAlgebra.SpectralBooks.expressionPolynomial, Computability.VPVNP.Projection.hom, h]
  | constant c => simp [project, polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial,
      Computability.VPVNP.Projection.hom]
  | _ => simp_all [project, polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]

end Formula

theorem HasFormula.project [Field F] {s : ℕ} {p : MvPolynomial σ F} (h : HasFormula s p)
    (φ : Computability.VPVNP.Projection F σ τ) : HasFormula s (φ.hom p) := by
  obtain ⟨f, rfl, hs⟩ := h
  exact ⟨f.project φ, f.polynomial_project φ, by simpa using hs⟩

end Hierarchy

end OAI
