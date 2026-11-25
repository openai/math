import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointFactor
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointLabelCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleCrossCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCostPhase

/-! # Cross frequencies in both halves and all columns of a work row

The first input half pairs with the second output half, and the second input
half with the first output half. Each quotient therefore parametrizes the
opposite half's frequency. The unused distinguished slots pass through both
permutations in the same order.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Module Matrix

/-- Ordinary coordinates surviving a label's local auxiliary transform. -/
abbrev EndpointLabelResidualIndex (C J L R₁ R₂ : Type*) :=
  EndpointDigitPairs C J L × ((C → R₁) × (C → R₂))

private def endpointCrossResidual {C J L R₁ R₂ V : Type*}
    (j : J) (a : L × R₁ ≃ V) (b : L × R₂ ≃ V) :
    EndpointLabelResidualIndex C J L R₁ R₂ ≃
      ((C → V) × (C → V)) × ((C × {k : J // k ≠ j} → L) × (C × {k : J // k ≠ j} → L)) :=
  (endpointLabelResidual j).trans ((((Equiv.piCongrRight (fun _ : C => a)).prodCongr
    (Equiv.piCongrRight (fun _ : C => b))).trans (Equiv.prodComm _ _)).prodCongr (Equiv.refl _))

variable {ℓ f : ℕ} [Fact ℓ.Prime] {E U J : Type*} [AddCommGroup E] [Module (ZMod ℓ) E]
  [FiniteDimensional (ZMod ℓ) E]
  {v₁ v₂ w₁ w₂ : E ≃ₗ[ZMod ℓ] (ZMod ℓ) × (U → ZMod ℓ)}

/-- The source and destination residual addresses bijectively encode opposite
endpoint frequencies and a common spectator. The complete cross pairing is
the sum of the two endpoint Fourier phases and a phase on representatives. -/
theorem exists_endpointLabelCross
    (B : LinearMap.BilinForm (ZMod ℓ) E) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (H : Submodule (ZMod ℓ) E) (X₁ : AuxiliarySlice v₁ H) (X₂ : AuxiliarySlice v₂ H)
    (Z₁ : AuxiliarySlice w₁ (H.orthogonalBilin B)) (Z₂ : AuxiliarySlice w₂ (H.orthogonalBilin B))
    (j : J) :
    ∃ (s : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) X₁.C X₂.C ≃
        PrimeCommonPair ℓ f (finrank (ZMod ℓ) (H.orthogonalBilin B)) × PrimeCommonSpectators (Fin f) j ℓ)
      (t : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) Z₁.C Z₂.C ≃
        PrimeCommonPair ℓ f (finrank (ZMod ℓ) H) × PrimeCommonSpectators (Fin f) j ℓ)
      (r : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) X₁.C X₂.C →
        EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) Z₁.C Z₂.C → ZMod ℓ),
      (∀ v, (s v).2 = (endpointLabelResidual j v).2) ∧
      (∀ v, (t v).2 = (endpointLabelResidual j v).2) ∧ ∀ i o,
      endpointCrossPair B
        (primeCommonQueryChart j (primeCommonLabelMap v₁) (primeCommonLabelMap v₂)
          (endpointLabelFinChart X₁ X₂ i)).1
        (primeCommonQueryChart j (primeCommonLabelMap w₁) (primeCommonLabelMap w₂)
          (endpointLabelFinChart Z₁ Z₂ o)).1 =
        (∑ c, ∑ k, (i.1.1 c k * (t o.2).1.1 c k + i.1.2 c k * (t o.2).1.2 c k)) +
        (∑ c, ∑ k, ((s i.2).1.1 c k * o.1.1 c k + (s i.2).1.2 c k * o.1.2 c k)) +
        r i.2 o.2 := by
  obtain ⟨bS₁,bT₂,h₁₂⟩ := exists_endpointSliceCrossCoordinates B hB hs H X₁ Z₂
  obtain ⟨bS₂,bT₁,h₂₁⟩ := exists_endpointSliceCrossCoordinates B hB hs H X₂ Z₁
  let residual (s : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) X₁.C X₂.C)
      (t : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) Z₁.C Z₂.C) :=
    ∑ c : Fin f,
      (B (X₁.chart (0,(endpointLabelResidual j s).1.1 c)) (Z₂.chart (0,(endpointLabelResidual j t).1.2 c)) +
       B (X₂.chart (0,(endpointLabelResidual j s).1.2 c)) (Z₁.chart (0,(endpointLabelResidual j t).1.1 c)))
  refine ⟨endpointCrossResidual j bS₁.toEquiv bS₂.toEquiv,
    endpointCrossResidual j bT₁.toEquiv bT₂.toEquiv, residual, fun _ => rfl, fun _ => rfl, ?_⟩
  rintro ⟨h,s⟩ ⟨p,t⟩
  let u := (endpointLabelResidual j s).1
  let v := (endpointLabelResidual j t).1
  let bH := (finBasis (ZMod ℓ) H).equivFun
  let bP := (finBasis (ZMod ℓ) (H.orthogonalBilin B)).equivFun
  change (∑ c, (B (X₁.chart (bH.symm (h.1 c), u.1 c)) (Z₂.chart (bP.symm (p.2 c), v.2 c)) +
      B (Z₁.chart (bP.symm (p.1 c), v.1 c)) (X₂.chart (bH.symm (h.2 c), u.2 c)))) =
    (∑ c, ∑ k, (h.1 c k * bT₂ (v.2 c) k + h.2 c k * bT₁ (v.1 c) k)) +
    (∑ c, ∑ k, (bS₂ (u.2 c) k * p.1 c k + bS₁ (u.1 c) k * p.2 c k)) +
    (∑ c, (B (X₁.chart (0,u.1 c)) (Z₂.chart (0,v.2 c)) + B (X₂.chart (0,u.2 c)) (Z₁.chart (0,v.1 c))))
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [hs.eq (Z₁.chart _) (X₂.chart _), h₁₂, h₂₁]
  simp only [bH, bP, LinearEquiv.apply_symm_apply, Finset.sum_add_distrib, dotProduct]
  abel

end

end

end FiniteFourier
end LinearAlgebra
end OAI
