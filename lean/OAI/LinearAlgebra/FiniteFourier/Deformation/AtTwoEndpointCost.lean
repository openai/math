import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointCircuits
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointOccupied
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointJetWord

/-! # Base gate counts for the two-local endpoint circuits -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Matrix

/-- Price a synchronized word on `w` addresses with `2*e*h` ground coordinates each. -/
noncomputable def atTwoWordCost (e h w cutoff d : ℕ) (β C : ℝ) : ℝ :=
  d*((w : ℝ)*(40*e*h*convolutionEnvelope cutoff) +
    (2*e*h)*(C*w*(1+Real.logb 2 w)^β))

local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic
local notation "φ₂" => algebraMap TwoLocalBase TwoLocalQuadratic
local notation "ω₂" => AdjoinRoot.root (cyclotomic 3 TwoLocalBase)

variable {σ : Type} [Fintype σ] [DecidableEq σ] {M r H D cutoff : ℕ} {β C : ℝ}

/-- The exact costs of both directions, in base gates, of the integral block deformation.
The two directions charge the Taylor circuit at its own source height. -/
theorem BlockProductTransforms.atTwo_stages (T : BlockProductTransforms (O₂ M) σ r H)
    (m : σ → ℕ) (ζ : σ → (IntegralJet M H)ˣ)
    (hM : 0 < M) (hr : 0 < r) (hH : 0 < H)
    (hcr : 2*M.totient*r ≤ cutoff) (hcH : 2*M.totient*H ≤ cutoff)
    (hm : ∀ i, 0 < m i)
    (hu : ∀ i, Pairwise fun j k => IsUnit (T.quadraticNodes i j - T.quadraticNodes i k))
    (hF : ∀ i, OccupiedWord (Fin (13*m i)) D (dftMatrix (m i) (ζ i : IntegralJet M H)))
    (hF' : ∀ i, OccupiedWord (Fin (13*m i)) D (dftMatrix (m i) (ζ i : IntegralJet M H))⁻¹)
    (hshear : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    let w := Fintype.card (Address m)
    let short := atTwoWordCost M.totient r w cutoff 37 β C
    let long := atTwoWordCost M.totient H (14*w) cutoff (243*D+37) β C
    JetStage φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient r H (T.input m ζ)
        (short + w*(8*(M.totient : ℝ)*r*(1+Real.logb 2 r)*convolutionEnvelope cutoff) + long) ∧
      JetStage φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient H r (T.output m ζ)
        (long + w*(8*(M.totient : ℝ)*H*(1+Real.logb 2 H)*convolutionEnvelope cutoff) + short) := by
  let := integralJet_semilocal M r
  let := integralJet_semilocal M H
  have he := Nat.totient_pos.mpr hM
  have h2 : 2 ≤ 2*M.totient := by omega
  have htr (x : σ → IntegralJet M r) (y w : σ → (IntegralJet M r)ˣ) :=
    layerWord_atTwoJetMatrixCircuit (layerWord_transportGrid (integralJet_unit_split M r) m x y w)
      hM hr hcr hshear hβ hC
  have hE := occupiedWord_atTwoJetMatrixCircuit (occupiedWord_evaluationGrid
    (integralJet_unit_split M H) m T.quadraticNodes T.binomialScale ζ hm hu hF)
    hM hH hcH hshear hβ hC
  have hI := occupiedWord_atTwoJetMatrixCircuit (occupiedWord_interpolationGrid
    (integralJet_unit_split M H) m T.quadraticNodes T.binomialScale ζ hm hu hF')
    hM hH hcH hshear hβ hC
  constructor
  · simpa only [atTwoWordCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      T.input_stage m ζ hr ((Nat.mul_le_mul_right r h2).trans hcr)
        (htr _ _ _) hE
  · simpa only [atTwoWordCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      T.output_stage m ζ hH ((Nat.mul_le_mul_right H h2).trans hcH)
        hI (htr _ _ _)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
