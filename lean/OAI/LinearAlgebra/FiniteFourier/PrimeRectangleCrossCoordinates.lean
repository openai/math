import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointBridgeCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleGeometry

/-! # The cross pairing at two local rectangle endpoints

The coordinates summed by the two endpoints use a fixed basis of the target
span and a fixed basis of its annihilator. Each residual indexes a frequency
of the opposite summation space. The remaining pairing involves only the two
coset representatives.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Module Matrix

variable {K E A A' : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
  {e : E ≃ₗ[K] K × A} {e' : E ≃ₗ[K] K × A'}

/-- A label slice in the fixed Fourier coordinates of its summation subspace. -/
def AuxiliarySlice.finChart {H : Submodule K E} (X : AuxiliarySlice e H) :
    E ≃ₗ[K] (Fin (finrank K H) → K) × (K × X.C) :=
  X.chart.symm.trans ((finBasis K H).equivFun.prodCongr (LinearEquiv.refl K _))

theorem AuxiliarySlice.finChart_residual_zero {H : Submodule K E} (X : AuxiliarySlice e H) (x : E) :
    (X.finChart x).2 = 0 ↔ x ∈ H := by
  change (X.chart.symm x).2 = 0 ↔ x ∈ H
  constructor
  · intro hz
    have hh : X.chart ((X.chart.symm x).1,0) = x := by
      rw [← hz]; exact X.chart.apply_symm_apply x
    rw [← hh, X.chart_zero]
    exact Subtype.coe_prop _
  · intro hx
    have he := X.chart_zero (⟨x,hx⟩ : H)
    exact congrArg Prod.snd (X.chart.symm_apply_eq.mpr he.symm)

private theorem AuxiliarySlice.finChart_symm_basis {H : Submodule K E} (X : AuxiliarySlice e H)
    (h : H) (s : K × X.C) :
    X.finChart.symm ((finBasis K H).equivFun h,s) = X.chart (h,s) := by
  simp [AuxiliarySlice.finChart]

/-- Exact cross decomposition for arbitrary local slices, including a
degenerate target span. Both frequency permutations are linear. -/
theorem exists_endpointSliceCrossCoordinates (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hs : B.IsSymm) (H : Submodule K E)
    (X : AuxiliarySlice e H) (Z : AuxiliarySlice e' (H.orthogonalBilin B)) :
    ∃ (bS : (K × X.C) ≃ₗ[K] (Fin (finrank K (H.orthogonalBilin B)) → K))
      (bT : (K × Z.C) ≃ₗ[K] (Fin (finrank K H) → K)), ∀ h s p t,
      B (X.chart (h,s)) (Z.chart (p,t)) =
        (finBasis K H).equivFun h ⬝ᵥ bT t + bS s ⬝ᵥ (finBasis K (H.orthogonalBilin B)).equivFun p +
          B (X.chart (0,s)) (Z.chart (0,t)) := by
  obtain ⟨c,u,v,_,hu,hv,hpair⟩ := exists_primeEndpointDualCharts B hB hs H
  have hcv (y : E) : y ∈ H.orthogonalBilin B ↔
      ((v.trans (LinearEquiv.prodComm K _ _)) y).2 = 0 := hv y
  have hc : finrank K (H.orthogonalBilin B) = c := by
    simpa using (endpointAxisEquiv _ (H.orthogonalBilin B) hcv).finrank_eq
  subst c
  obtain ⟨bS,bT,hcross⟩ := exists_endpointBridgeCoordinates B u v X.finChart Z.finChart
    (fun x => (X.finChart_residual_zero x).trans (hu x))
    (fun x => (Z.finChart_residual_zero x).trans (hv x)) hpair
  refine ⟨bS,bT,fun h s p t => ?_⟩
  have eq := hcross ((finBasis K H).equivFun h) s ((finBasis K (H.orthogonalBilin B)).equivFun p) t
  have hx := X.finChart_symm_basis 0 s
  have hz := Z.finChart_symm_basis 0 t
  simp only [map_zero] at hx hz
  simpa only [AuxiliarySlice.finChart_symm_basis, hx, hz] using eq

/-- Coordinate dot product relative to the fixed finite basis of a space. -/
def endpointBasisDot (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (x y : V) : K :=
  (finBasis K V).equivFun x ⬝ᵥ (finBasis K V).equivFun y

/-- The same Fourier coordinates, indexed by the summation subspaces
themselves. This is the index convention of the full local endpoint arrays. -/
theorem exists_endpointSliceCross (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hs : B.IsSymm) (H : Submodule K E)
    (X : AuxiliarySlice e H) (Z : AuxiliarySlice e' (H.orthogonalBilin B)) :
    ∃ (bS : (K × X.C) ≃ₗ[K] H.orthogonalBilin B) (bT : (K × Z.C) ≃ₗ[K] H), ∀ h s p t,
      B (X.chart (h,s)) (Z.chart (p,t)) =
        endpointBasisDot K H h (bT t) + endpointBasisDot K (H.orthogonalBilin B) (bS s) p +
          B (X.chart (0,s)) (Z.chart (0,t)) := by
  obtain ⟨bS,bT,eq⟩ := exists_endpointSliceCrossCoordinates B hB hs H X Z
  refine ⟨bS.trans (finBasis K (H.orthogonalBilin B)).equivFun.symm,
    bT.trans (finBasis K H).equivFun.symm, fun h s p t => ?_⟩
  simpa only [endpointBasisDot, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    using eq h s p t

namespace BitRoutingGeometry

variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)

/-- Each ordered pair of halves on a free bit rectangle admits the specified
frequency coordinates and residual phase. -/
theorem exists_rectangleCrossCoordinates (R : BitRectangle L b) (hd : ¬ℓ ∣ bitCutDistance R.1)
    {v w : BitLabel L b} (hv : v ∈ bitSources R) (hw : w ∈ bitTargets R) (i k : Bool) :
    let H := G.targetSpan R
    let P := H.orthogonalBilin G.form
    let X := G.sourceSlice R hd hv i
    let Z := G.targetSlice R hw k
    ∃ (bS : (ZMod ℓ × X.C) ≃ₗ[ZMod ℓ] (Fin (finrank (ZMod ℓ) P) → ZMod ℓ))
      (bT : (ZMod ℓ × Z.C) ≃ₗ[ZMod ℓ] (Fin (finrank (ZMod ℓ) H) → ZMod ℓ)), ∀ h s p t,
      G.form (X.chart (h,s)) (Z.chart (p,t)) =
        (finBasis (ZMod ℓ) H).equivFun h ⬝ᵥ bT t +
          bS s ⬝ᵥ (finBasis (ZMod ℓ) P).equivFun p +
          G.form (X.chart (0,s)) (Z.chart (0,t)) :=
  exists_endpointSliceCrossCoordinates G.form G.nondegenerate G.symm (G.targetSpan R)
    (G.sourceSlice R hd hv i) (G.targetSlice R hw k)

end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
