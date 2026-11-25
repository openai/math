import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointColumnPairs
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointPrograms
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointTransport
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleTransfer

/-! # Free-rectangle factorization in the physical row coordinates

Fix a free rectangle and a nonzero query power. Each label uses a pair of
auxiliary slices, independent of the selected query. Every transfer across
the rectangle factors between these fixed endpoint transforms through a
scaled permutation of the single physical row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
set_option synthInstance.maxSize 2048
section
open Module
open scoped Classical

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
variable {E : Type} [AddCommGroup E] [Module (ZMod ℓ) E] [FiniteDimensional (ZMod ℓ) E]
variable {U J : Type} [Fintype J] [Fintype U]

private def endpointPairDot {n : ℕ} (x y : PrimeCommonPair ℓ f n) : ZMod ℓ :=
  ∑ c, ∑ k, (x.1 c k * y.1 c k + x.2 c k * y.2 c k)

set_option maxHeartbeats 1000000 in
/-- The two pairs of slice charts need only agree on their physical summation
spaces. The representatives and bases on the two sides may differ. -/
theorem primeEndpoint_factor (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ) (D : ℕ)
    (B : LinearMap.BilinForm (ZMod ℓ) E) (hB : B.Nondegenerate) (hSym : B.IsSymm)
    (H : Submodule (ZMod ℓ) E)
    {v₁ v₂ w₁ w₂ : E ≃ₗ[ZMod ℓ] (ZMod ℓ) × (U → ZMod ℓ)}
    (X₁ : AuxiliarySlice v₁ H) (X₂ : AuxiliarySlice v₂ H)
    (Z₁ : AuxiliarySlice w₁ (H.orthogonalBilin B)) (Z₂ : AuxiliarySlice w₂ (H.orthogonalBilin B))
    [Fintype X₁.C] [Fintype X₂.C] [Fintype Z₁.C] [Fintype Z₂.C]
    (hv : ∀ x y, B x y = (v₁ x).1 * (v₂ y).1 + ∑ u, (v₁ x).2 u * (v₂ y).2 u)
    (hw : ∀ x y, B x y = (w₁ x).1 * (w₂ y).1 + ∑ u, (w₁ x).2 u * (w₂ y).2 u)
    (j : J) :
    ∃ mid, RealizableAtMost mid 0 ∧
      (primeCommonKernel (C := Fin f) hζ B a D).submatrix
        (primeCommonQueryChart j (primeCommonLabelMap w₁) (primeCommonLabelMap w₂))
        (primeCommonQueryChart j (primeCommonLabelMap v₁) (primeCommonLabelMap v₂)) =
      primeTargetEndpoint (f := f) (J := J) hζ a Z₁ Z₂ * mid *
        primeSourceEndpoint (f := f) (J := J) hζ a X₁ X₂ := by
  classical
  let P := H.orthogonalBilin B
  let xv := endpointLabelFinChart (C := Fin f) (J := J) X₁ X₂
  let zw := endpointLabelFinChart (C := Fin f) (J := J) Z₁ Z₂
  let cv := primeCommonQueryChart (C := Fin f) j (primeCommonLabelMap v₁) (primeCommonLabelMap v₂)
  let cw := primeCommonQueryChart (C := Fin f) j (primeCommonLabelMap w₁) (primeCommonLabelMap w₂)
  let X := cv ∘ xv
  let Z := cw ∘ zw
  let bH := (finBasis (ZMod ℓ) H).equivFun
  let bP := (finBasis (ZMod ℓ) P).equivFun
  obtain ⟨s,t,r,hs,ht,hc⟩ := exists_endpointLabelCross (f := f) B hB hSym H X₁ X₂ Z₁ Z₂ j
  have hf := primeCommonKernel_free_factor hζ B a D X Z s t
    (fun q h => endpointPairDot h q) (fun p μ => endpointPairDot μ p) r
    (endpointLabelCoordinateAux X₁ X₂ bH) (endpointLabelCoordinateAux Z₁ Z₂ bP)
    (fun v => endpointLabelDistExponent j v.1) (fun v => endpointLabelDistExponent j v.1)
    (fun i => (hs i.2).symm) (fun o => (ht o.2).symm)
    (endpointLabelCoordinateChart_self X₁ X₂ bH j B hv)
    (endpointLabelCoordinateChart_self Z₁ Z₂ bP j B hw) hc
  let e := (↑(a⁻¹) : ZMod ℓ)
  let weight := fun (o : PrimeCommonPair ℓ f (finrank (ZMod ℓ) P) ×
      EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) Z₁.C Z₂.C) =>
    let u := s.symm (o.1, (t o.2).2)
    (⅟(ℓ : K)) ^ (Fintype.card (Fin f) * D) * digitPhase hζ
      (e * (r u o.2 - endpointLabelDistExponent j u.1 - endpointLabelDistExponent j o.2.1))
  let mid := endpointBridge s t weight
  refine ⟨Matrix.reindex zw xv mid, (endpointBridge_realizable s t weight).reindex zw xv, ?_⟩
  apply endpointFactor_reindex xv zw
  extract_lets e₁ F₁ G₁ w₁ A₁ C₁ at hf
  convert! hf using 1
  congr! 3
  ext i j
  by_cases he : i = j
  · subst i
    simp only [Matrix.diagonal_apply_eq]
    rfl
  · simp [he]

namespace BitRoutingGeometry

variable {L b m : ℕ} (G : BitRoutingGeometry ℓ L b)
/-- Across every pair of incident labels of a free rectangle, the j-th query
can reuse the same physical source and destination transforms. -/
theorem free_endpoint_factor (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (R : BitRectangle L b) (hd : ¬ℓ ∣ bitCutDistance R.1)
    {v w : BitLabel L b} (hv : v ∈ bitSources R) (hw : w ∈ bitTargets R) (j : Fin m) :
    ∃ mid, RealizableAtMost mid 0 ∧ G.transfer hζ f a j w v =
      primeTargetEndpoint (f := f) (J := Fin m) hζ a (G.targetSlice R hw false) (G.targetSlice R hw true) *
        mid * primeSourceEndpoint (f := f) (J := Fin m) hζ a
          (G.sourceSlice R hd hv false) (G.sourceSlice R hd hv true) := by
  have aux := primeEndpoint_factor (U := Fin (G.D-1)) (f := f) (J := Fin m)
    (v₁ := G.halfChart v false) (v₂ := G.halfChart v true)
    (w₁ := G.halfChart w false) (w₂ := G.halfChart w true)
    hζ a G.D G.form G.nondegenerate G.symm (G.targetSpan R)
    (G.sourceSlice R hd hv false) (G.sourceSlice R hd hv true) (G.targetSlice R hw false)
    (G.targetSlice R hw true) (G.labelCharts v).pair (G.labelCharts w).pair j
  obtain ⟨mid, hc, he⟩ := aux
  refine ⟨mid, hc, ?_⟩
  rw [transfer, queryChart, queryChart]
  simp only [halfChart, Bool.false_eq_true, ite_false, ite_true] at he
  rw [he]
  ext o i
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr ?_ ?_
  · ext k
    simp
  · intro k _
    apply congrArg (· * _)
    apply Finset.sum_congr ?_ ?_
    · ext l
      simp
    · intro l _
      rfl

end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
