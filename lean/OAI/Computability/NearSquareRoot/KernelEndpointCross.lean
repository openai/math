import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointColumnPairs
import Mathlib.Algebra.Module.ZMod

/-! # Additive frequency and label coordinates of a free rectangle

The residual permutations supplied by the two cross pairings preserve
addition. This makes their intervening bridge a binary linear reindexing,
with a single output sign. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEndpointCross
noncomputable section

open OAI.LinearAlgebra.FiniteFourier Module Matrix

/-- An additive isomorphism of exponent-ℓ modules is linear over ZMod ℓ. -/
def linear {ℓ : ℕ} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module (ZMod ℓ) X] [Module (ZMod ℓ) Y] (e : X ≃+ Y) : X ≃ₗ[ZMod ℓ] Y where
  toAddEquiv := e
  map_smul' := ZMod.map_smul e

def endpointLabelAddChart {ℓ : ℕ} [Fact ℓ.Prime] {C J U E : Type*}
    [AddCommGroup E] [Module (ZMod ℓ) E] [FiniteDimensional (ZMod ℓ) E]
    {v w : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ)} {H : Submodule (ZMod ℓ) E}
    (X : AuxiliarySlice v H) (Y : AuxiliarySlice w H) :
    (EndpointDigitPairs C (Fin (finrank (ZMod ℓ) H)) (ZMod ℓ) ×
        EndpointLabelResidualIndex C J (ZMod ℓ) X.C Y.C) ≃+
      ((C × (J ⊕ U) → ZMod ℓ) × (C × (J ⊕ U) → ZMod ℓ)) where
  toEquiv := endpointLabelFinChart X Y
  map_add' x y := by
    let b := (finBasis (ZMod ℓ) H).equivFun
    let d := endpointAuxPairedAddChart (C := C) X.split.toAddEquiv Y.split.toAddEquiv
    let e := endpointAuxAddChart (J := J) d
    let g : EndpointDigitPairs C (Fin (finrank (ZMod ℓ) H)) (ZMod ℓ) → (C → H) × (C → H) :=
      fun v => ((fun c => b.symm (v.1 c)), fun c => b.symm (v.2 c))
    have hg : g (x.1 + y.1) = g x.1 + g y.1 := by
      apply Prod.ext <;> funext c <;> apply map_add
    change endpointCurryRows.symm (e (g (x.1 + y.1), x.2 + y.2)) = _
    rw [hg, show (g x.1 + g y.1, x.2+y.2) = (g x.1,x.2)+(g y.1,y.2) by rfl, map_add]
    rfl

def crossResidual {C J L R₁ R₂ V : Type*}
    [AddCommGroup L] [AddCommGroup R₁] [AddCommGroup R₂] [AddCommGroup V]
    (j : J) (a : L × R₁ ≃+ V) (b : L × R₂ ≃+ V) :
    EndpointLabelResidualIndex C J L R₁ R₂ ≃+
      ((C → V) × (C → V)) × ((C × {k : J // k ≠ j} → L) × (C × {k : J // k ≠ j} → L)) where
  toEquiv := (endpointLabelResidual j).trans
    ((((Equiv.piCongrRight (fun _ : C => a.toEquiv)).prodCongr
      (Equiv.piCongrRight (fun _ : C => b.toEquiv))).trans (Equiv.prodComm _ _)).prodCongr (Equiv.refl _))
  map_add' x y := by
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · funext c
      exact map_add b (x.1.2 c j,x.2.2 c) (y.1.2 c j,y.2.2 c)
    · funext c
      exact map_add a (x.1.1 c j,x.2.1 c) (y.1.1 c j,y.2.1 c)

def bridgeAdd {H P S T U : Type*}
    [AddCommGroup H] [AddCommGroup P] [AddCommGroup S] [AddCommGroup T] [AddCommGroup U]
    (s : S ≃+ P × U) (t : T ≃+ H × U) : P × T ≃+ H × S where
  toEquiv := endpointBridgeEquiv s.toEquiv t.toEquiv
  map_add' x y := by
    apply Prod.ext
    · change (t (x.2+y.2)).1 = (t x.2).1 + (t y.2).1
      rw [map_add t]; rfl
    · change s.symm (x.1 + y.1, (t (x.2 + y.2)).2) = _
      rw [map_add t]
      exact map_add s.symm (x.1,(t x.2).2) (y.1,(t y.2).2)

variable {ℓ f : ℕ} [Fact ℓ.Prime] {E U J : Type*} [AddCommGroup E] [Module (ZMod ℓ) E]
  [FiniteDimensional (ZMod ℓ) E]
  {v₁ v₂ w₁ w₂ : E ≃ₗ[ZMod ℓ] (ZMod ℓ) × (U → ZMod ℓ)}

/-- The source and destination residual addresses bijectively encode opposite
endpoint frequencies and a common spectator. The complete cross pairing is
the sum of the two endpoint Fourier phases and a phase on representatives. -/
theorem exists_endpointLabelCross_add
    (B : LinearMap.BilinForm (ZMod ℓ) E) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (H : Submodule (ZMod ℓ) E) (X₁ : AuxiliarySlice v₁ H) (X₂ : AuxiliarySlice v₂ H)
    (Z₁ : AuxiliarySlice w₁ (H.orthogonalBilin B)) (Z₂ : AuxiliarySlice w₂ (H.orthogonalBilin B))
    (j : J) :
    ∃ (s : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) X₁.C X₂.C ≃+
        PrimeCommonPair ℓ f (finrank (ZMod ℓ) (H.orthogonalBilin B)) × PrimeCommonSpectators (Fin f) j ℓ)
      (t : EndpointLabelResidualIndex (Fin f) J (ZMod ℓ) Z₁.C Z₂.C ≃+
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
  refine ⟨crossResidual j bS₁.toAddEquiv bS₂.toAddEquiv,
    crossResidual j bT₁.toAddEquiv bT₂.toAddEquiv, residual, fun _ => rfl, fun _ => rfl, ?_⟩
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
end KernelEndpointCross

end NearSquareRoot
end Computability
end OAI
