import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.AtTwoJetMatrixReindex
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoJetCoordinates
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMonomial
import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs

/-! # Descent of a synchronized word on the Eisenstein jet at two -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

/-- Each slot uses one fixed jet multiplication per address and one integral shear
on each of its base coordinates. The height may be either endpoint's precision. -/
theorem layerWord_atTwoJetMatrixCircuit {M h s d : ℕ} {β C : ℝ}
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I (IntegralJet M h)}
    (hw : LayerWord d A) (hM : 0 < M) (hh : 0 < h) (hc : 2*M.totient*h ≤ s)
    (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    JetMatrixCircuit (algebraMap TwoLocalBase TwoLocalQuadratic) (AdjoinRoot.root (cyclotomic 3 TwoLocalBase))
      (cyclotomic M TwoLocalQuadratic) M.totient h A
      (d * ((Fintype.card I : ℝ)*(40*M.totient*h*convolutionEnvelope s) +
        (2*M.totient*h)*(C*(Fintype.card I : ℝ)*(1+Real.logb 2 (Fintype.card I))^β))) := by
  let : Nontrivial TwoLocalQuadratic :=
    (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic 3 TwoLocalBase)).mpr
      (degree_cyclotomic_pos 3 _ (by decide))
  exact hw.jetMatrixCircuit (atTwoJetCircuitsOver hM hh) atTwoCoefficientEncoding_bijective
    (cyclotomic.monic _ _) (natDegree_cyclotomic _ _) (Nat.totient_pos.mpr hM) hh hc
    (ht.shearTensorBound TwoLocalBase) hβ hC

/-- Descend a word with thirteen workspace registers per data register, then
discard the workspace. The gate count uses the full synchronized width. -/
theorem occupiedWord_atTwoJetMatrixCircuit {M h s d : ℕ} {β C : ℝ}
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I (IntegralJet M h)}
    (hw : OccupiedWord (Fin (Fintype.card I*13)) d A) (hM : 0 < M) (hh : 0 < h)
    (hc : 2*M.totient*h ≤ s) (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    JetMatrixCircuit (algebraMap TwoLocalBase TwoLocalQuadratic) (AdjoinRoot.root (cyclotomic 3 TwoLocalBase))
      (cyclotomic M TwoLocalQuadratic) M.totient h A
      (d * ((14*Fintype.card I : ℝ)*(40*M.totient*h*convolutionEnvelope s) +
        (2*M.totient*h)*(C*(14*Fintype.card I)*(1+Real.logb 2 (14*Fintype.card I))^β))) := by
  have hV : Fintype.card (I ⊕ Fin (Fintype.card I*13)) = 14*Fintype.card I := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [hV, Nat.cast_mul, Nat.cast_ofNat] using
    (layerWord_atTwoJetMatrixCircuit hw hM hh hc ht hβ hC).eliminateWorkspace

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
