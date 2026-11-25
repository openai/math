import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Nullstellensatz

/-! # Scalar extension for closures of polynomially parametrized sets

The parameter spaces and even the set of shapes may be infinite. Polynomial identities in
the parameters extend from an infinite ground field, and linear functionals on the extension
field detect whether a polynomial with extension-field coefficients vanishes at a ground point.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open MvPolynomial

variable {K : Type*} [Field K] {ι Shape : Type*} {P : Shape → Type*}

/-- The union, over all shapes, of the images of the polynomial maps given by `coords`,
evaluated at points with coordinates in `L`. -/
def polynomialFamilyImage (L : Type*) [Field L] [Algebra K L]
    (coords : (s : Shape) → ι → MvPolynomial (P s) K) : Set (ι → L) :=
  {y | ∃ (s : Shape) (a : P s → L), (fun i ↦ aeval a (coords s i)) = y}

private theorem aeval_ground {L τ : Type*} [Field L] [Algebra K L]
    (a : τ → K) (p : MvPolynomial τ K) :
    aeval (algebraMap K L ∘ a) p = algebraMap K L (aeval a p) :=
  (eval₂_comp _ _ _).symm

private theorem eval_projectedCoeffs {L : Type*} [Field L] [Algebra K L]
    (φ : Module.Dual K L) (p : MvPolynomial ι L) (x : ι → K) :
    eval x (∑ m ∈ p.support, monomial m (φ (p.coeff m))) =
      φ (eval (algebraMap K L ∘ x) p) := by
  classical
  rw [map_sum, eval_eq (algebraMap K L ∘ x), map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial]
  let t := ∏ i ∈ m.support, x i ^ m i
  have h : ∏ i ∈ m.support, (algebraMap K L ∘ x) i ^ m i = algebraMap K L t := by
    simp [t]
  rw [h, mul_comm (p.coeff m), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm t]
  rfl

/-- An affine point over an infinite field lies in the closure of the polynomial family
if and only if its scalar extension does. -/
theorem mem_polynomialFamilyClosure_baseChange_iff (L : Type*) [Field L] [Algebra K L]
    [Infinite K] (coords : (s : Shape) → ι → MvPolynomial (P s) K) (x : ι → K) :
    algebraMap K L ∘ x ∈ zeroLocus L (vanishingIdeal L (polynomialFamilyImage L coords)) ↔
      x ∈ zeroLocus K (vanishingIdeal K (polynomialFamilyImage K coords)) := by
  constructor
  · intro hx p hp
    have hident (s : Shape) : bind₁ (coords s) p = 0 := by
      apply MvPolynomial.funext
      intro a
      change aeval a _ = aeval a _
      rw [map_zero, aeval_bind₁]
      exact hp _ ⟨s, a, rfl⟩
    have hmem : map (algebraMap K L) p ∈ vanishingIdeal L (polynomialFamilyImage L coords) := by
      rintro _ ⟨s, a, rfl⟩
      change eval _ (map _ _) = 0
      rw [eval_map]
      change aeval (fun i ↦ aeval a (coords s i)) p = 0
      rw [← aeval_bind₁, hident, map_zero]
    apply (algebraMap K L).injective
    rw [map_zero, ← aeval_ground]
    exact (eval_map _ _ _).symm.trans (hx _ hmem)
  · intro hx p hp
    apply (Module.forall_dual_apply_eq_zero_iff K _).mp
    intro φ
    change φ (eval (algebraMap K L ∘ x) p) = 0
    rw [← eval_projectedCoeffs]
    apply hx
    rintro _ ⟨s, a, rfl⟩
    change eval _ _ = 0
    rw [eval_projectedCoeffs]
    have heval : eval (algebraMap K L ∘ (fun i ↦ aeval a (coords s i))) p = 0 := by
      apply hp
      exact ⟨s, algebraMap K L ∘ a, _root_.funext fun i ↦ aeval_ground a (coords s i)⟩
    rw [heval, map_zero]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
