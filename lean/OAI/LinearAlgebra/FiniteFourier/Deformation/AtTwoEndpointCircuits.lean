import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationStages
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoBlockProduct

/-! # Base-ring input and output circuits for one integral deformation block

Both copies of the input run the same transport, translation and evaluation circuit.
The output runs interpolation, translation and transport. Each direction pays for two
matrix words and one translation per address.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.BlockProductTransforms

open Polynomial Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {I : Type} [Fintype I] [DecidableEq I]
variable {φ : R →+* S} {η : S} {M : S[X]} {e r H : ℕ}
variable (T : BlockProductTransforms (AdjoinRoot M) I r H) (m : I → ℕ)
    (ζ : I → (JetQuotient M H)ˣ)

/-- The concrete base-ring implementation of the common short-to-long input map. -/
theorem input_stage {a b : ℝ} (hr : 0 < r) {cutoff : ℕ} (hc : 2*r ≤ cutoff)
    (hA : JetMatrixCircuit φ η M e r
      (transportGrid m T.inputOffset T.inputSlope (fun i => (T.transportScale i)⁻¹)) a)
    (hB : JetMatrixCircuit φ η M e H (evaluationGrid m T.quadraticNodes
      (fun i => scaledNodes (m i) (T.binomialScale i) (ζ i))) b) :
    JetStage φ η M e r H (T.input m ζ)
      (a + (Fintype.card (Address m) : ℝ) * (8*e*r*(1+Real.logb 2 r)*convolutionEnvelope cutoff) + b) :=
  ((JetStage.of_matrix hA).comp (jetStage_inputShift φ η M e r H hr hc)).comp (JetStage.of_matrix hB)

/-- The concrete long-to-short output circuit acting on the pointwise products. -/
theorem output_stage {a b : ℝ} (hH : 0 < H) {cutoff : ℕ} (hc : 2*H ≤ cutoff)
    (hA : JetMatrixCircuit φ η M e H (interpolationGrid m T.quadraticNodes
      (fun i => scaledNodes (m i) (T.binomialScale i) (ζ i))) a)
    (hB : JetMatrixCircuit φ η M e r (transportGrid m T.outputOffset T.outputSlope
      T.transportScale) b) :
    JetStage φ η M e H r (T.output m ζ)
      (a + (Fintype.card (Address m) : ℝ) * (8*e*H*(1+Real.logb 2 H)*convolutionEnvelope cutoff) + b) :=
  ((JetStage.of_matrix hA).comp (jetStage_outputShift φ η M e H r hH hc)).comp (JetStage.of_matrix hB)

end Deformation.BlockProductTransforms

end FiniteFourier
end LinearAlgebra
end OAI
