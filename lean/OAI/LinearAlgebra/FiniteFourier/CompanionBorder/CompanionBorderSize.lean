import OAI.Computability.BorderVNP.ModelGroundImage
import OAI.Computability.BorderVNP.SignedFamily
import OAI.LinearAlgebra.FiniteFourier.CompanionBorder.CompanionBorderCircuit
import OAI.LinearAlgebra.SpectralBooks.TreeGridCompression

/-! # The companion degree-component lower bound on the Fourier circuit model

The two models use the same monomial coordinates. Translating a spectral
register into a circuit with the same output and gate count includes its
coefficient vector in the companion image. On an infinite field the
companion's ground-field and geometric minima coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace CompanionBorder

open OAI.LinearAlgebra.SpectralBooks Filter MvPolynomial

variable {F σ : Type*} [Field F]

/-- Every degree-component vector from a spectral circuit occurs at the same
gate budget in the companion circuit image. -/
theorem circuitCoefficientVectors_subset (d s : ℕ) :
    circuitCoefficientVectors F σ d s ⊆ OAI.Computability.BorderVNP.circuitImage F σ d s := by
  rintro v ⟨r, p, i, hi, hv⟩
  obtain ⟨c, hc⟩ := exists_circuit_register p i
  exact ⟨p.cost, hi, c, (congrArg (OAI.Computability.BorderVNP.coeffVector d) hc).trans hv⟩

/-- A vanishing equation for companion circuits also vanishes on every
spectral register of that size over the algebraic closure. -/
theorem borderApprox_of_spectral {d s : ℕ} {f : MvPolynomial σ F}
    (h : DegreeBorderSizeAtMost d s f) : OAI.Computability.BorderVNP.BorderApprox d s f := by
  exact OAI.Computability.BorderVNP.imageClosure_mono
    (circuitCoefficientVectors_subset (F := AlgebraicClosure F) (σ := σ) d s) h

/-- The minimum companion size is a lower bound for the spectral size. -/
theorem borderSize_le_degreeBorderSize (d : ℕ) (f : MvPolynomial σ F) :
    OAI.Computability.BorderVNP.borderSize d f ≤ degreeBorderSize d f :=
  OAI.Computability.BorderVNP.borderSize_le_iff.mpr
    (borderApprox_of_spectral ((degreeBorderSize_le_iff d _ f).mp le_rfl))

/-- An infinite ground field includes the algebraic closures of the rational
field and of every prime field used for characteristic transfer. -/
theorem degreeLower_of_groundLower [Infinite F] {d : ℕ} {f : MvPolynomial σ F} {b : ℝ}
    (lower : b ≤ OAI.Computability.BorderVNP.groundBorderSize d f) : DegreeBorderSizeAtLeast d b f := by
  have bound : OAI.Computability.BorderVNP.groundBorderSize d f ≤ degreeBorderSize d f :=
    (OAI.Computability.BorderVNP.borderSize_eq_groundBorderSize d f).symm.le.trans (borderSize_le_degreeBorderSize d f)
  exact lower.trans (by exact_mod_cast bound)

/-- Every sufficiently large length in the fixed ground-field stretch
remains valid with the same exponent for the spectral model. -/
theorem pstar_degree_lower [Infinite F] {ε : ℝ}
    (lower : ∀ᶠ n : ℕ in atTop, (2:ℝ)^((n:ℝ)^ε) ≤ OAI.Computability.BorderVNP.groundBorderSize n
      (map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n))) :
    ∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^ε))
      (map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)) :=
  lower.mono fun _ hn => degreeLower_of_groundLower hn

/-- A choice-table presentation of the companion polynomial passes its
stretch estimate to the bipartite subcubic grids of the Fourier tree argument. -/
theorem nonTree_of_pstar_ground {F : Type} [Field F] [Infinite F]
    (presentation : IndependentSetGraph.HasPolynomialChoicePresentation (σ := fun n => Fin n × Bool) F
      (fun n => map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)))
    {ε : ℝ} (positive : 0 < ε)
    (lower : ∀ᶠ n : ℕ in atTop, (2:ℝ)^((n:ℝ)^ε) ≤ OAI.Computability.BorderVNP.groundBorderSize n
      (map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n))) : HasNonTreeWireMetric F := by
  obtain ⟨δ, hδ, hard⟩ := IndependentSetGraph.hardSubcubicGrids_of_choicePresentation
    (F := F) (σ := fun n => Fin n × Bool)
    (fun n => map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)) presentation positive
    (pstar_degree_lower (F := F) (ε := ε) lower)
  exact hasNonTreeWireMetric_of_hardSubcubicGrids (F := F) (δ := δ) hδ hard

end CompanionBorder

end

end FiniteFourier
end LinearAlgebra
end OAI
