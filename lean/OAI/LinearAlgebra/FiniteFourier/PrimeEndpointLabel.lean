import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointAuxiliary
import OAI.LinearAlgebra.FiniteFourier.PrimeAuxiliarySlice
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCoordinates

/-! # The full local endpoint of a routing label

The chart used before the partial transform is fixed at the label. Separating
the distinguished digit in its residual changes only the middle permutation.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {C J U L H R R₁ R₂ E : Type*}

/-- Read one distinguished coordinate per column, retaining all other columns
and coordinates in the spectator address of the ordinary common query. -/
def endpointDistinguishedSelection (j : J) :
    (C → J → L) ≃ (C → L) × (C × {k : J // k ≠ j} → L) := by
  classical
  exact
    { toFun := fun x => (fun c => x c j, fun v => x v.1 v.2)
      invFun := fun x c k => if h : k = j then x.1 c else x.2 (c, ⟨k,h⟩)
      left_inv := by intro x; funext c k; by_cases hk : k = j <;> simp [hk]
      right_inv := by
        intro x
        apply Prod.ext
        · funext c; simp
        · funext v; simp [v.2.property] }

/-- Split the residual of a local endpoint into active quotient coordinates
and the same spectators used in `primeCommonQueryChart`. -/
def endpointLabelResidual (j : J) :
    EndpointDigitPairs C J L × ((C → R₁) × (C → R₂)) ≃
      ((C → L × R₁) × (C → L × R₂)) ×
      ((C × {k : J // k ≠ j} → L) × (C × {k : J // k ≠ j} → L)) :=
  let e := endpointDistinguishedSelection (C := C) (L := L) j
  { toFun := fun x => ((fun c => ((e x.1.1).1 c, x.2.1 c), fun c => ((e x.1.2).1 c, x.2.2 c)),
      (e x.1.1).2, (e x.1.2).2)
    invFun := fun y => ((e.symm (fun c => (y.1.1 c).1, y.2.1), e.symm (fun c => (y.1.2 c).1, y.2.2)),
      fun c => (y.1.1 c).2, fun c => (y.1.2 c).2)
    left_inv := by intro x; simp
    right_inv := by intro y; simp }

/-- The query paper uses ordinary arrays with uncurried slot addresses. -/
def endpointCurryRows {I : Type*} :
    ((C × I → L) × (C × I → L)) ≃ EndpointDigitPairs C I L :=
  (Equiv.curry C I L).prodCongr (Equiv.curry C I L)

section Label

variable {ℓ : ℕ} [Fact ℓ.Prime] [AddCommGroup E] [Module (ZMod ℓ) E]
variable {p q : E ≃ₗ[ZMod ℓ] (ZMod ℓ) × (U → ZMod ℓ)} {H : Submodule (ZMod ℓ) E}
variable (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H)

/-- The j-independent input array chart along both copies of H in all columns.
For a destination use its perpendicular summation space in place of H. -/
def endpointLabelFiberChart :
    (((C → H) × (C → H)) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) ≃
      ((C × (J ⊕ U) → ZMod ℓ) × (C × (J ⊕ U) → ZMod ℓ)) :=
  let e := endpointAuxPairedAddChart P.split.toAddEquiv Q.split.toAddEquiv
  (endpointAuxAddChart e).toEquiv.trans endpointCurryRows.symm

/-- In common coordinates, the local chart uses the paired auxiliary slices
in each column. Its spectator projection is exactly that of the separated
residual. -/
theorem endpointLabelFiberChart_common (j : J)
    (h : (C → H) × (C → H))
    (s : EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C))) :
    primeCommonQueryChart j (primeCommonLabelMap p) (primeCommonLabelMap q)
        (endpointLabelFiberChart P Q (h,s)) =
      ((fun c => P.chart (h.1 c, (endpointLabelResidual j s).1.1 c),
        fun c => Q.chart (h.2 c, (endpointLabelResidual j s).1.2 c)),
        (endpointLabelResidual j s).2) := rfl

variable [Fintype C] [Fintype U]

/-- The auxiliary part of the chirp in local endpoint coordinates. -/
def endpointLabelAuxExponent
    (i : ((C → H) × (C → H)) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) : ZMod ℓ :=
  ∑ c, ∑ u, P.split (i.1.1 c, i.2.2.1 c) u * Q.split (i.1.2 c, i.2.2.2 c) u

/-- The distinguished part of the chirp depends only on the residual. -/
def endpointLabelDistExponent (j : J) (d : EndpointDigitPairs C J (ZMod ℓ)) : ZMod ℓ :=
  ∑ c, d.1 c j * d.2 c j

/-- The self-pairing in common coordinates splits into a j-independent local
chirp and a distinguished chirp which can be placed in the bridge. -/
theorem endpointLabelFiberChart_self (j : J) (B : LinearMap.BilinForm (ZMod ℓ) E)
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ i, (p x).2 i * (q y).2 i)
    (i : ((C → H) × (C → H)) ×
      (EndpointDigitPairs C J (ZMod ℓ) × ((C → P.C) × (C → Q.C)))) :
    let z := primeCommonQueryChart j (primeCommonLabelMap p) (primeCommonLabelMap q)
      (endpointLabelFiberChart P Q i)
    (∑ c, B (z.1.1 c) (z.1.2 c)) =
      endpointLabelAuxExponent P Q i + endpointLabelDistExponent j i.2.1 := by
  rcases i with ⟨h,s⟩
  change (∑ c, B (p.symm (s.1.1 c j, P.split (h.1 c, s.2.1 c)))
    (q.symm (s.1.2 c j, Q.split (h.2 c, s.2.2 c)))) = _
  simp only [hpq, LinearEquiv.apply_symm_apply, Finset.sum_add_distrib]
  exact add_comm _ _

end Label
end

end FiniteFourier
end LinearAlgebra
end OAI
