import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientsPacking
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyBasis

/-! # Ordered power coordinates for dyadic-list packing and jet circuits -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Polynomial Module

noncomputable section

variable {η : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ}
    (T : DyadicCoefficientTower D L)

local notation "e" => listCyclotomicDegree GaussianRationals D.pool B
local notation "φ" => algebraMap (protectedRationals L) (protectedGaussian L)
local notation "η₀" => protectedGaussianI L

private def arrayEquiv (r : ℕ) : JetArray (protectedGaussian L) e r ≃ₗ[protectedGaussian L]
    JetQuotient T.modulus r :=
  LinearEquiv.ofBijective (jetQuotientLinear T.modulus e r)
    (jetQuotientValue_bijective T.monic T.degree_eq degree_pos)

/-- The packing indices give the coefficient-generator power first and the jet power second. -/
def packedBasis (r : ℕ) :
    Basis (Fin e × Fin r) (protectedGaussian L) (JetQuotient T.modulus r) :=
  (Basis.ofEquivFun (T.arrayEquiv r).symm).reindex (Equiv.prodComm _ _)

/-- Every packed basis vector is the corresponding monomial in the two generators. -/
theorem packedBasis_apply (r : ℕ) (j : Fin e × Fin r) :
    T.packedBasis r j =
      algebraMap T.Order (JetQuotient T.modulus r) (AdjoinRoot.root T.modulus)^j.1.val *
        AdjoinRoot.root (X^r)^j.2.val := by
  rw [packedBasis, Basis.reindex_apply, Basis.coe_ofEquivFun]
  change jetQuotientValue T.modulus (Pi.single (j.2,j.1) 1) = _
  rw [jetQuotientValue_eq_sum, Finset.sum_eq_single (j.2,j.1)]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/-- Quadratic coordinates in encoder order and power coordinates in packing order
represent the same jet precisely when they agree after interchanging the two power indices. -/
theorem jetOperandValue_eq_iff {r : ℕ}
    (x : (Fin r × Fin e) × Fin 2 → protectedRationals L) (z : JetQuotient T.modulus r) :
    jetOperandValue φ η₀ T.modulus x = z ↔ ∀ i : Fin e × Fin r,
      QuadraticDescent.decode φ η₀ (fun j => x ((j.1.2,j.1.1),j.2)) i =
        (T.packedBasis r).repr z i := by
  let a := quadraticJetArray φ η₀ (fun i : Fin r × Fin e => x (i,0)) (fun i => x (i,1))
  have hrepr (i : Fin e × Fin r) : (T.packedBasis r).repr z i = (T.arrayEquiv r).symm z (i.2,i.1) := by
    simp [packedBasis, Basis.repr_reindex, Prod.swap]
  simp only [hrepr]
  change T.arrayEquiv r a = z ↔ ∀ i : Fin e × Fin r, a (i.2,i.1) = (T.arrayEquiv r).symm z (i.2,i.1)
  rw [← LinearEquiv.eq_symm_apply]
  constructor
  · intro h i
    exact congrFun h (i.2,i.1)
  · intro h
    funext i
    exact h (i.2,i.1)

/-- Fixed multiplication on the jet operand coordinates at arbitrary allowed height. -/
theorem operand_matrix_envelope {r s : ℕ} (hr : 0 < r) (hs : 2*e*r ≤ s)
    (z : JetQuotient T.modulus r) :
    let b := jetOperandBasis (R := protectedRationals L) η₀ (protectedGaussian_coordinates L) T.monic T.degree_eq degree_pos r
    FiniteFourier.RealizableAtMost (K := protectedRationals L) (fun d u => b.repr (z * b u) d) ⌊40*(e : ℝ)*r*convolutionEnvelope s⌋₊ :=
  JetCircuitsOver.operandMatrix_envelope η₀ (protectedGaussian_coordinates L) T.monic T.degree_eq degree_pos (T.jets hr) hr hs z

end
end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
