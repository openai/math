import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointLabel
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Digit-basis coordinates for the whole label endpoint -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {ℓ : ℕ} [Fact ℓ.Prime] {C J I U E : Type*} [AddCommGroup E] [Module (ZMod ℓ) E]
variable {p q : E ≃ₗ[ZMod ℓ] (ZMod ℓ) × (U → ZMod ℓ)} {H : Submodule (ZMod ℓ) E}
variable (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) (b : H ≃ₗ[ZMod ℓ] (I → ZMod ℓ))

/-- A chart for a single physical vector expressed in the digit basis of H.
The distinguished scalar belongs to the residual component. -/
def endpointLabelColumnChart : E ≃ₗ[ZMod ℓ] (I → ZMod ℓ) × (ZMod ℓ × P.C) :=
  P.chart.symm.trans (b.prodCongr (LinearEquiv.refl _ _))

theorem endpointLabelColumnChart_symm_apply (v : I → ZMod ℓ) (r : ZMod ℓ × P.C) :
    (endpointLabelColumnChart P b).symm (v,r) = P.chart (b.symm v,r) := rfl

/-- The zero-residual slice is the physical subspace itself. -/
theorem endpointLabelColumnChart_zero_iff (x : E) :
    ((endpointLabelColumnChart P b) x).2 = 0 ↔ x ∈ H := by
  change (P.chart.symm x).2 = 0 ↔ x ∈ H
  constructor
  · intro h
    obtain ⟨⟨u,r⟩, rfl⟩ := P.chart.surjective x
    simp only [P.chart.symm_apply_apply] at h
    subst r
    rw [P.chart_zero]
    exact u.property
  · intro hx
    let u : H := ⟨x,hx⟩
    have he : P.chart (u,0) = x := P.chart_zero _
    rw [← he, P.chart.symm_apply_apply]

/-- Pair of H-vectors at each column expressed in ordinary digit coordinates. -/
def endpointLabelBasisRows :
    EndpointDigitPairs C I (ZMod ℓ) ≃ ((C → H) × (C → H)) :=
  let e := Equiv.piCongrRight (fun _ : C => b.symm.toEquiv)
  e.prodCongr e

/-- The full array chart with digit coordinates for the summed vector. -/
def endpointLabelCoordinateChart :
    (EndpointDigitPairs C I (ZMod ℓ) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) ≃
      ((C × (J ⊕ U) → ZMod ℓ) × (C × (J ⊕ U) → ZMod ℓ)) :=
  ((endpointLabelBasisRows b).prodCongr (Equiv.refl _)).trans (endpointLabelFiberChart P Q)

/-- Using the standard finite basis yields exactly `finrank H` transformed
axes in each half and column. -/
def endpointLabelFinChart [FiniteDimensional (ZMod ℓ) E] :=
  endpointLabelCoordinateChart (C := C) (J := J) P Q (Module.finBasis (ZMod ℓ) H).equivFun

/-- Single-column coordinate charts describe the physical input at every
column. The spectators are only a projection of the residual. -/
theorem endpointLabelCoordinateChart_common (j : J) (h : EndpointDigitPairs C I (ZMod ℓ))
    (s : EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C))) :
    primeCommonQueryChart j (primeCommonLabelMap p) (primeCommonLabelMap q)
        (endpointLabelCoordinateChart P Q b (h,s)) =
      ((fun c => (endpointLabelColumnChart P b).symm (h.1 c, (endpointLabelResidual j s).1.1 c),
        fun c => (endpointLabelColumnChart Q b).symm (h.2 c, (endpointLabelResidual j s).1.2 c)),
        (endpointLabelResidual j s).2) := rfl

variable [Fintype C] [Fintype U]

/-- The j-independent chirp in the ordinary digit coordinates of the summed
vectors. -/
def endpointLabelCoordinateAux
    (i : EndpointDigitPairs C I (ZMod ℓ) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) : ZMod ℓ :=
  endpointLabelAuxExponent P Q (endpointLabelBasisRows b i.1, i.2)

/-- Self-pairing of the physical vectors separated into the shared auxiliary
phase and the query-dependent residual phase. -/
theorem endpointLabelCoordinateChart_self (j : J) (B : LinearMap.BilinForm (ZMod ℓ) E)
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ i, (p x).2 i * (q y).2 i)
    (i : EndpointDigitPairs C I (ZMod ℓ) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) :
    let z := primeCommonQueryChart j (primeCommonLabelMap p) (primeCommonLabelMap q)
      (endpointLabelCoordinateChart P Q b i)
    (∑ c, B (z.1.1 c) (z.1.2 c)) =
      endpointLabelCoordinateAux P Q b i + endpointLabelDistExponent j i.2.1 :=
  endpointLabelFiberChart_self P Q j B hpq (endpointLabelBasisRows b i.1,i.2)

/-- The full array contains exactly one scalar per tuple of the two halves
of all `m+u` slots in each of the `f` columns. -/
theorem endpointLabelRow_card (ℓ f m u : ℕ) [NeZero ℓ] :
    Fintype.card ((Fin f × (Fin m ⊕ Fin u) → ZMod ℓ) ×
      (Fin f × (Fin m ⊕ Fin u) → ZMod ℓ)) = ℓ ^ (2 * (m + u) * f) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card]
  rw [← pow_add]
  congr 1
  ring

end

end FiniteFourier
end LinearAlgebra
end OAI
