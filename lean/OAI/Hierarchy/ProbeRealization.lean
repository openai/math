import OAI.Hierarchy.ProbeFlattening
import OAI.Hierarchy.ProbeLocalReplacement
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.Theorem

namespace OAI
/-! # Local Euclidean frames directly for an exact finite normalized spectral test -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor HyperbolicObstruction
noncomputable section

variable {F I : Type*} [Field F] [Fintype I] {k S : ℕ} [Nonempty (Fin S)]

/-- A single normalized spectrum realization satisfying the port constraints of a
labeled ball simultaneously recovers the centers and every signed far-end height. -/
theorem normalized_flattening (base : I) (no : ¬HasSpectralFlat F (k+1))
    (K : ℝ) (join : I → I → Prop) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ (φ : Probe.Spectrum F S) (scale R : ℝ) (cent : I → Fin S)
      (port : I → Fin k → Bool → Fin S),
      let d := rawWireDistance φ scale
      0 ≤ scale → 0<R → (N:ℝ)≤R →
      (∀ i j, d (port i j false) (port i j true)=2*R) →
      (∀ i j, d (port i j false) (cent i)≤R) →
      (∀ i j, d (cent i) (port i j true)≤R) →
      (∀ i i', d (cent i) (cent i')≤K) →
      (∀ i i' j s, d (port i j s) (port i' j s)≤K) →
      (∀ i j l, j≠l → ∀ s t, d (port i j s) (port i l t)≤Real.sqrt 2*R+1) →
      (∀ i i', join i i' → d (cent i) (cent i')=0) →
      ∃ z : I → Coordinates k, (∀ i i', join i i' → z i=z i') ∧
        (∀ i i', |d (cent i) (cent i')-dist (z i) (z i')|<ε) ∧
        ∀ i i' j s, let sign : ℝ := if s then 1 else -1
          |max (d (cent i) (port i' j s)-R) 0-max (sign*(z i' j-z i j)) 0|<ε := by
  obtain ⟨N,hN⟩ := exact_pattern_flattening (K:=K) (join:=join) base no hε
  refine ⟨N,?_⟩
  intro φ scale R cent port
  dsimp only
  intro hc hr wide diam left right center near cross joined
  obtain ⟨X,metric,P,p,_,geo,distances,_⟩ := SpectralPlacementPrices.realize_finite_point_geodesic φ scale hc
  let C := P.catZero geo
  obtain ⟨A,zero,negative,positive⟩ := column_of_ports C hr (fun i => p (cent i))
    (fun i j => p (port i j false)) (fun i j => p (port i j true))
    (fun i j => (distances ..).trans (diam i j))
    (fun i j => (distances ..).trans_le (left i j)) (fun i j => (distances ..).trans_le (right i j))
  have ends (i : I) (j : Fin k) (s : ℝ) :
      A.axis i j (ColumnSegments.endTime R s) = p (port i j (decide (0 ≤ s))) := by
    by_cases hs : 0 ≤ s
    · simpa [ColumnSegments.endTime,hs] using positive i j
    · simpa [ColumnSegments.endTime,hs] using negative i j
  let W : ExactPattern F I k K join := {
    carrier := X
    prices := P
    cat := C
    radius := R
    positive := hr
    segment := A
    center_le := fun i i' => by rw [zero,distances]; exact center _ _
    ends_le := fun i i' j s => by rw [ends,ends,distances]; exact near ..
    corner := fun i j l jl s t => by rw [ends,ends,distances]; exact cross i j l jl _ _
    joined := fun i i' h => dist_eq_zero.mp (by rw [zero,distances]; exact joined _ _ h)
  }
  obtain ⟨z,jz,centz,endz⟩ := hN W wide
  refine ⟨z,jz,?_,?_⟩
  · intro i i'
    have h := centz i i'
    change |dist (A.center i) (A.center i')-dist (z i) (z i')|<ε at h
    simpa only [zero,distances] using h
  · intro i i' j s
    have h := endz i i' j s
    change |max (dist (A.center i) (A.axis i' j ((if s then (1:ℝ) else -1)*R))-R) 0 -
      max ((if s then (1:ℝ) else -1)*(z i' j-z i j)) 0|<ε at h
    cases s
    · simpa only [Bool.false_eq_true,ite_false,neg_one_mul,negative,zero,distances] using h
    · simpa only [ite_true,one_mul,positive,zero,distances] using h

end
end Hierarchy.AdaptiveProbe

end OAI
