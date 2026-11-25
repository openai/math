import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointCost
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoAxisJetWords

/-! # Two-local circuits for the actual prime-sector product

The two coordinate circuits use the same split and transport nodes that give
the sector multiplication law. Ternary padding supplies their axis transforms
up to the common width bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial
open scoped Classical

local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic
local notation "φ₂" => algebraMap TwoLocalBase TwoLocalQuadratic
local notation "ω₂" => AdjoinRoot.root (cyclotomic 3 TwoLocalBase)

variable {σ : Type} [Fintype σ] {M : ℕ} {p : σ → ℕ} [∀ i, Fact (p i).Prime]
  {hM : Odd M} {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}
  (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))

/-- Both base-ring stage bounds and the exact sector product hold for one
choice of common input map and linear output map, on any subset of axes. -/
theorem atTwo_sector_stages {β C : ℝ} (r B cutoff : ℕ) (hr : 0 < r) (S : Finset σ)
    (hwidth : ∀ i, (p i-1)/2 ≤ B) (h3 : ∀ j, 3^j ≤ 8*B → 3^j ∣ M)
    (hcH : 2*M.totient*(2*r+2*Fintype.card σ) ≤ cutoff)
    (hshear : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    let H := 2*r + 2*Fintype.card σ
    let φ := algebraMap (O₂ M) (IntegralJet M r)
    let m := fun i : S => (p i.val-1)/2
    let ζ := fun i : S => (a i.val).jetRoot H
    let w := Fintype.card (Address m)
    let D := 6400*(1+Nat.clog 2 (2+B))
    let short := atTwoWordCost M.totient r w cutoff 37 β C
    let long := atTwoWordCost M.totient H (14*w) cutoff (243*D+37) β C
    ∃ T : BlockProductTransforms (O₂ M) S r H,
      (∀ x y, T.output m ζ (T.input m ζ x * T.input m ζ y) =
        multiply (ConvolutionGrid.coeff fun i : S => primeAxisActiveCoeff (m := m i)
          (φ (((p i.val + 1)/4 : ℕ) : O₂ M)) (φ ((a i.val).beta : O₂ M))) x y) ∧
      JetStage φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient r H (T.input m ζ)
        (short + w*(8*(M.totient : ℝ)*r*(1+Real.logb 2 r)*convolutionEnvelope cutoff) + long) ∧
      JetStage φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient H r (T.output m ζ)
        (long + w*(8*(M.totient : ℝ)*H*(1+Real.logb 2 H)*convolutionEnvelope cutoff) + short) := by
  intro H φ m ζ w D short long
  obtain ⟨T, hu, hproduct⟩ := exists_atTwoSectorTransforms a r hr S
  have hwords (i : S) := (a i.val).jetRoot_words H B (hwidth i.val) h3
  have hm (i : S) : 0 < m i := by
    have := h7 i.val
    dsimp [m]
    omega
  have hrH : r ≤ H := by dsimp [H]; omega
  refine ⟨T, hproduct, ?_⟩
  exact T.atTwo_stages m ζ hM.pos hr (hr.trans_le hrH)
    ((Nat.mul_le_mul_left (2*M.totient) hrH).trans hcH) hcH hm hu
    (fun i => (hwords i).1) (fun i => (hwords i).2) hshear hβ hC

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
