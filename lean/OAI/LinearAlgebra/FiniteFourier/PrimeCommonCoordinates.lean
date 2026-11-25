import OAI.LinearAlgebra.FiniteFourier.PrimeCommonKernel
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonSplit

/-! # Label charts and query coordinates

The same pair of charts is used for a label at every distinguished slot.
The active and spectator slots are separated by permutations; no arithmetic
over the coefficient ring is required.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {ℓ : ℕ} {C J U E : Type*} [AddCommGroup E] [Module (ZMod ℓ) E]

/-- Separate the distinguished and auxiliary components in an active vector. -/
def primeCommonLabelComponents :
    (Unit ⊕ U → ZMod ℓ) ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ) :=
  (LinearEquiv.sumPiEquivProdPi _ _ _ (fun _ => ZMod ℓ)).trans
    ((LinearEquiv.piUnique _ (fun _ : Unit => ZMod ℓ)).prodCongr (LinearEquiv.refl _ _))

/-- A label basis identifies the active local slots with the common space. -/
def primeCommonLabelMap (p : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ)) :
    (Unit ⊕ U → ZMod ℓ) ≃ₗ[ZMod ℓ] E := primeCommonLabelComponents.trans p.symm

/-- Paired auxiliary bases and the norm-one distinguished direction preserve
the digit dot product under the two label identifications. -/
theorem primeCommonLabelMap_pair [Fintype U]
    (B : E →ₗ[ZMod ℓ] E →ₗ[ZMod ℓ] ZMod ℓ)
    (p q : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ))
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ u, (p x).2 u * (q y).2 u)
    (x y : Unit ⊕ U → ZMod ℓ) :
    B (primeCommonLabelMap p x) (primeCommonLabelMap q y) = dotProduct x y := by
  rw [hpq]
  simp only [primeCommonLabelMap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change x (.inl ()) * y (.inl ()) + ∑ u, x (.inr u) * y (.inr u) = ∑ i, x i * y i
  simp [Fintype.sum_sum_type]

/-- Both spectator tuples, indexed by the distinguished slots other than `j`. -/
abbrev PrimeCommonSpectators (C : Type*) {J : Type*} (j : J) (ℓ : ℕ) :=
  (C × {k : J // k ≠ j} → ZMod ℓ) × (C × {k : J // k ≠ j} → ZMod ℓ)

/-- Pack both input halves into the active pair of vectors in every column
and the unused addresses. -/
def primeCommonQueryPack (j : J) :
    ((C × (J ⊕ U) → ZMod ℓ) × (C × (J ⊕ U) → ZMod ℓ)) ≃
      PrimeCommonAddress C (Unit ⊕ U → ZMod ℓ) (PrimeCommonSpectators C j ℓ) :=
  let e := ((primeQuerySlotEquiv j).symm.arrowCongr (Equiv.refl (ZMod ℓ))).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans ((Equiv.curry _ _ _).prodCongr (Equiv.refl _)))
  (e.prodCongr e).trans (Equiv.prodProdProdComm _ _ _ _)

/-- `S_{v,j}` and `T_{v,j}` use the same coordinate permutation on ordinary
inputs and outputs. Only the choice of active slot depends on `j`. -/
def primeCommonQueryChart (j : J) (p q : (Unit ⊕ U → ZMod ℓ) ≃ₗ[ZMod ℓ] E) :
    ((C × (J ⊕ U) → ZMod ℓ) × (C × (J ⊕ U) → ZMod ℓ)) ≃
      PrimeCommonAddress C E (PrimeCommonSpectators C j ℓ) :=
  (primeCommonQueryPack j).trans (primeCommonChart p q)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
