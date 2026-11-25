import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationStages

/-! # The common dyadic block encoder and decoder

Each Fourier matrix acts at long precision. Its circuit is composed with the
two fixed diagonal scalings and the one Taylor circuit on each input/output path.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Matrix

variable {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ] [DecidableEq σ]
variable {φ : R →+* S} {η : S} {M : S[X]} {e r H cutoff : ℕ}

/-- Coordinate charge for the two endpoint scalings and one shift on each of `W`
monomials. The shift starts at precision `n` and its target has precision `N`. -/
noncomputable def endpointCost (W e n N cutoff : ℕ) : ℝ :=
  W * (40*e*n + 40*e*N + 8*e*n*(1+Real.logb 2 n)) * convolutionEnvelope cutoff

theorem transformInput_stage (m : σ → ℕ) (u : σ → (JetQuotient M r)ˣ)
    (v : σ → (JetQuotient M H)ˣ) (ζ : ∀ i, Fin (m i) → AdjoinRoot M)
    (jr : JetCircuitsOver φ η M e r) (jH : JetCircuitsOver φ η M e H)
    (basis : Function.Bijective (fun x : Fin 2 → R => φ (x 0) + η * φ (x 1)))
    (hM : M.Monic) (hd : M.natDegree = e) (he : 0 < e) (hr : 0 < r) (hH : 0 < H)
    (hcr : 2*e*r ≤ cutoff) (hcH : 2*e*H ≤ cutoff) {C : ℝ}
    (fourier : JetMatrixCircuit φ η M e H
      ((evaluation m ζ).map (algebraMap (AdjoinRoot M) (JetQuotient M H))) C) :
    JetStage φ η M e r H (transformInput m u v ζ)
      (C + endpointCost (Fintype.card (Address m)) e r H cutoff) := by
  have sc := scale_stage m (fun i => (u i)⁻¹) jr basis hM hd he hr hcr
  have shift := jetStage_inputShift (I := Address m) φ η M e r H hr
    ((show 2*r ≤ 2*e*r by gcongr; omega).trans hcr)
  have sc' := scale_stage m v jH basis hM hd he hH hcH
  have h := ((sc.comp shift).comp sc').comp (JetStage.of_matrix fourier)
  convert h using 1
  · funext x
    rfl
  · unfold endpointCost
    ring

theorem transformOutput_stage (m : σ → ℕ) (u : σ → (JetQuotient M r)ˣ)
    (v : σ → (JetQuotient M H)ˣ) (ζ : ∀ i, Fin (m i) → AdjoinRoot M)
    (jr : JetCircuitsOver φ η M e r) (jH : JetCircuitsOver φ η M e H)
    (basis : Function.Bijective (fun x : Fin 2 → R => φ (x 0) + η * φ (x 1)))
    (hM : M.Monic) (hd : M.natDegree = e) (he : 0 < e) (hr : 0 < r) (hH : 0 < H)
    (hcr : 2*e*r ≤ cutoff) (hcH : 2*e*H ≤ cutoff) {C : ℝ}
    (fourier : JetMatrixCircuit φ η M e H
      ((interpolation m ζ).map (algebraMap (AdjoinRoot M) (JetQuotient M H))) C) :
    JetStage φ η M e H r (transformOutput m u v ζ)
      (C + endpointCost (Fintype.card (Address m)) e H r cutoff) := by
  have sc := scale_stage m (fun i => (v i)⁻¹) jH basis hM hd he hH hcH
  have shift := jetStage_outputShift (I := Address m) φ η M e H r hH
    ((show 2*H ≤ 2*e*H by gcongr; omega).trans hcH)
  have sc' := scale_stage m u jr basis hM hd he hr hcr
  have h := (((JetStage.of_matrix fourier).comp sc).comp shift).comp sc'
  convert h using 1
  · funext x
    rfl
  · unfold endpointCost
    ring

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
