import OAI.Computability.BorderVNP.ResiduePinsEval
import OAI.Computability.BorderVNP.ResidueLaurent
import Mathlib.Algebra.Module.ZMod

/-!
# The matrix eigenvector identity at a Laurent branch

The functional in Lemma 10.1 takes absolute trace of the residue after multiplying
by the test differential. The local input to the matrix construction is exactly
the curve-coordinate Cartier identity (10.2) and the bound on the poles of the tests.
The regularity requirement is on the complete polynomial sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open Residue ResidueBox Module Matrix
open scoped Matrix BigOperators Classical

variable {σ ι β E κ : Type*} [Field E] [Field κ] [Fintype σ] [Fintype ι] [Fintype β]
variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) κ]
variable (φ : E →+* LaurentSeries κ) (x : σ → LaurentSeries κ) (t : (LaurentSeries κ)ˣ)
variable (η₀ : LaurentSeries κ)

/-- Absolute trace of residue as an additive map on the branch. -/
noncomputable def traceResidueHom : LaurentSeries κ →+ ZMod p :=
  (Algebra.trace (ZMod p) κ).toAddMonoidHom.comp (HahnSeries.coeff.addMonoidHom (-1))

/-- The prime-field functional on the Laurent arrays used as finite tests. -/
noncomputable def testFunctional : Laurent σ E →ₗ[ZMod p] ZMod p :=
  ((traceResidueHom p).comp ((AddMonoidHom.mulRight η₀).comp (evaluate φ x t))).toZModLinearMap p

/-- Definition of the pin functional in the branch coordinate. -/
theorem testFunctional_apply (f : Laurent σ E) :
    testFunctional p φ x t η₀ f = tracedRes p (evaluate φ x t f * η₀) := rfl

variable [CharP κ p] [PerfectRing κ p]

/-- Compatibility (10.2) at one Frobenius power for the actual mixed coordinate algebra. -/
def CartierCompatibility (u : ℕ) (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) : Prop :=
  ∀ f : Mixed σ E,
    evaluate φ x t (extract (p ^ u) (pow_pos (Fact.out : p.Prime).pos u) root
      (mixedToLaurent f * equationProduct (p ^ u) g)) * η₀ =
      cartier p u (mixedEval φ x t f * η₀)

omit [Algebra (ZMod p) E] [Algebra (ZMod p) κ] in
private theorem compatibility_of_supported (u : ℕ) (g : ι → MvPolynomial (Option σ) E)
    (root : E →+* E) (h : CartierCompatibility p φ x t η₀ u g root)
    (f : Laurent σ E) (hf : chartSupported f) :
    evaluate φ x t (extract (p ^ u) (pow_pos (Fact.out : p.Prime).pos u) root
      (f * equationProduct (p ^ u) g)) * η₀ =
      cartier p u (evaluate φ x t f * η₀) := by
  have h' := h (restrictChart f)
  rwa [embed_restrictChart f hf] at h'

/-- The rows of (10.3) act on the traced residue pin as multiplication by the residue of
the complete regular polynomial, proving the eigenvector calculation of (10.1). -/
theorem eigenvector (B : Basis β (ZMod p) E) (L u : ℕ) (hq : 2 ≤ p ^ u)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E)
    (hCartier : CartierCompatibility p φ x t η₀ u g root)
    (A : Laurent σ E) (z : ZMod p)
    (hμ : ∀ μ ∈ A.coeff.support, μ none = 0 ∧ ∀ i, 0 ≤ μ (some i) ∧ μ (some i) ≤ L)
    (hregular : 0 ≤ (evaluate φ x t A).order)
    (hvalue : (evaluate φ x t A).coeff 0 = algebraMap (ZMod p) κ z)
    (hpole : ∀ i : Index β σ (radius L (∑ j, (g j).totalDegree)),
      -((p ^ u : ℕ) : ℤ) ≤ (evaluate φ x t (test B i) * η₀).order) :
    let H := radius L (∑ j, (g j).totalDegree)
    let Ω := pin B H (testFunctional p φ x t η₀)
    (∑ μ ∈ A.coeff.support, weights B H (p ^ u) (by omega) g root μ (A.coeff μ)) *ᵥ Ω =
      z • Ω := by
  let H := radius L (∑ j, (g j).totalDegree)
  let ℓ := testFunctional p φ x t η₀
  funext i
  let η := evaluate φ x t (test B i) * η₀
  have hi : chartSupported (test B i) :=
    chartSupported_single i.2.val (B i.1) fun j => (i.2.property.2 j).1
  have row (μ : Exponent σ) (hmem : μ ∈ A.coeff.support) :
      (weights B H (p ^ u) (by omega) g root μ (A.coeff μ) *ᵥ pin B H ℓ) i =
        traceResidueHom p (evaluate φ x t (.single μ (A.coeff μ)) * cartier p u η) := by
    obtain ⟨ht, hpos⟩ := hμ μ hmem
    rw [weights_mul_pin B L (p ^ u) hq g root (A.coeff μ) μ ht hpos ℓ]
    change tracedRes p (evaluate φ x t (AddMonoidAlgebra.single μ (A.coeff μ) *
      extract (p ^ u) (by omega) root (test B i * equationProduct (p ^ u) g)) * η₀) = _
    have hTest : chartSupported (extract (p ^ u) (by omega) root
        (test B i * equationProduct (p ^ u) g)) :=
      chartSupported_extracted_test L _ hq g root (B i.1) i.2.val i.2.property
    rw [evaluate_mul φ x t _ _ (chartSupported_single μ (A.coeff μ) (fun j => (hpos j).1))
      hTest, mul_assoc,
      compatibility_of_supported p φ x t η₀ u g root hCartier (test B i) hi]
    rfl
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  calc
    _ = ∑ μ ∈ A.coeff.support, traceResidueHom p
        (evaluate φ x t (.single μ (A.coeff μ)) * cartier p u η) :=
      Finset.sum_congr rfl row
    _ = tracedRes p (evaluate φ x t A * cartier p u η) := by
      rw [← map_sum, ← Finset.sum_mul, ← map_sum]
      exact congrArg (fun f => traceResidueHom p (evaluate φ x t f * cartier p u η))
        (AddMonoidAlgebra.sum_coeff_single A)
    _ = _ := tracedRes_mul_cartier_of_regular p u _ η z hvalue hregular (hpole i)

/-- A trace-one polynomial test, of any initial degree, implies that a coordinate of
the fixed finite pin vector is nonzero. Only this proof chooses a larger Frobenius power. -/
theorem nonzero_of_trace_one (B : Basis β (ZMod p) E) (L : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (root : ℕ → (E →+* E))
    (hCartier : ∀ u > 0, CartierCompatibility p φ x t η₀ u g (root u))
    (f : Mixed σ E) (hf : tracedRes p (mixedEval φ x t f * η₀) = 1) :
    ∃ i, pin B (radius L (∑ j, (g j).totalDegree)) (testFunctional p φ x t η₀) i ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨u, hu, hbox⟩ := exists_large_extraction hp L g (mixedToLaurent f) (chartSupported_embed f)
  let f' := extract (p ^ u) (pow_pos (Fact.out : p.Prime).pos u) (root u)
    (mixedToLaurent f * equationProduct (p ^ u) g)
  apply exists_nonzero_pin B _ _ f' (hbox (root u))
  rw [testFunctional_apply, show evaluate φ x t f' * η₀ = cartier p u (mixedEval φ x t f * η₀)
    from hCartier u hu f, tracedRes_cartier, hf]
  exact one_ne_zero

end ResiduePins

end BorderVNP
end Computability
end OAI
