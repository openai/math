import OAI.Hierarchy.Models
import OAI.Hierarchy.Interpolation
import Mathlib.Algebra.MvPolynomial.CommRing

namespace OAI
/-! # A quadratic formula for any homogeneous component -/

namespace Hierarchy
open MvPolynomial
open MatrixMultiplication.Arithmetic
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {σ : Type}

namespace Formula

/-- Replace each occurrence of a variable by the product of a scalar and that variable. -/
def dilate (t : F) : Formula F σ → Formula F σ
  | .constant c => .constant c
  | .input i => .mul (.constant t) (.input i)
  | .add f g => .add (dilate t f) (dilate t g)
  | .sub f g => .sub (dilate t f) (dilate t g)
  | .mul f g => .mul (dilate t f) (dilate t g)

theorem polynomial_dilate (t : F) (f : Formula F σ) :
    (f.dilate t).polynomial = aeval (fun i => C t * X i) f.polynomial := by
  induction f <;>
    simp_all [dilate, Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]

omit [Field F] in
theorem cost_dilate (t : F) (f : Formula F σ) : (f.dilate t).cost ≤ 2*f.cost+1 := by
  induction f <;> simp_all only [dilate, Expression.cost] <;> omega

theorem totalDegree_le_cost (f : Formula F σ) : f.polynomial.totalDegree ≤ f.cost+1 := by
  induction f with
  | constant => simp [Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial, Expression.cost]
  | input => simp [Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial, Expression.cost]
  | add f g hf hg =>
    exact (totalDegree_add (Formula.polynomial f) (Formula.polynomial g)).trans (by change _ ≤ f.cost+g.cost+1+1; omega)
  | sub f g hf hg =>
    exact (totalDegree_sub (Formula.polynomial f) (Formula.polynomial g)).trans (by change _ ≤ f.cost+g.cost+1+1; omega)
  | mul f g hf hg =>
    exact (totalDegree_mul (Formula.polynomial f) (Formula.polynomial g)).trans (by change _ ≤ f.cost+g.cost+1+1; omega)

end Formula

private theorem sum_formulas {ι : Type*} (S : Finset ι) (P : ι → MvPolynomial σ F) (b : ℕ)
    (h : ∀ t ∈ S, HasFormula b (P t)) : HasFormula (S.card*(b+1)) (∑ t ∈ S, P t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨.constant 0, by simp [Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial], by simp [Expression.cost]⟩
  | @insert a S ha ih =>
    obtain ⟨f, fval, fcost⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨g, gval, gcost⟩ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    refine ⟨.add f g, ?_, ?_⟩
    · rw [Finset.sum_insert ha]
      exact congrArg₂ (·+·) fval gval
    · rw [Finset.card_insert_of_notMem ha, Nat.add_mul, one_mul]
      change f.cost+g.cost+1 ≤ _
      omega

theorem HasFormula.homogeneousComponent [Infinite F] {s : ℕ} {p : MvPolynomial σ F}
    (h : HasFormula s p) (d : ℕ) :
    HasFormula ((s+2)*(2*s+3)) (MvPolynomial.homogeneousComponent d p) := by
  classical
  obtain ⟨f, rfl, small⟩ := h
  obtain ⟨S, c, hcard, heq⟩ :=
    homogeneousComponent_interpolation f.polynomial d (s+1) (f.totalDegree_le_cost.trans (by omega))
  rw [heq, show s+2 = S.card by omega]
  apply sum_formulas S _ (2*s+2)
  intro t _
  refine ⟨.mul (.constant (c t)) (f.dilate t), ?_, ?_⟩
  · exact congrArg (C (c t) * ·) (f.polynomial_dilate t)
  · change 0+(f.dilate t).cost+1 ≤ 2*s+2
    have := f.cost_dilate t
    omega


end
end Hierarchy

end OAI
