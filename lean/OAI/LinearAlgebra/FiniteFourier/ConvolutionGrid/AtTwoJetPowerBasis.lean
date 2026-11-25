import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyCoordinates
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyLift

/-! # Power coordinates of a truncated monogenic jet algebra -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Module Polynomial

noncomputable section

variable {S : Type*} [CommRing S] {m : S[X]} {e : ℕ}
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (r : ℕ)

private def jetArrayEquiv : JetArray S e r ≃ₗ[S] JetQuotient m r :=
  LinearEquiv.ofBijective (jetQuotientLinear m e r) (jetQuotientValue_bijective hm hd he)

/-- Index the power basis by coefficient degree followed by jet degree. -/
def jetPowerBasis : Basis (Fin e × Fin r) S (JetQuotient m r) :=
  (Basis.ofEquivFun (jetArrayEquiv hm hd he r).symm).reindex (Equiv.prodComm _ _)

/-- Packing a jet array preserves its coefficients in the transposed order. -/
theorem jetPowerBasis_repr_value (x : JetArray S e r) (j : Fin e × Fin r) :
    (jetPowerBasis hm hd he r).repr (jetQuotientValue m x) j = x (j.2, j.1) := by
  change (jetPowerBasis hm hd he r).repr (jetArrayEquiv hm hd he r x) j = _
  simp [jetPowerBasis, Basis.repr_reindex, Prod.swap]

/-- Synthesis in power coordinates packs the transposed coefficient array. -/
theorem jetPowerBasis_decode (x : Fin e × Fin r → S) :
    (jetPowerBasis hm hd he r).equivFun.symm x =
      jetQuotientValue m (fun j => x (j.2, j.1)) := by
  apply (jetPowerBasis hm hd he r).equivFun.injective
  ext j
  simpa only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply] using
    (jetPowerBasis_repr_value hm hd he r (fun i => x (i.2, i.1)) j).symm

/-- Each basis vector is a coefficient-generator power times a jet-variable power. -/
theorem jetPowerBasis_apply (j : Fin e × Fin r) :
    jetPowerBasis hm hd he r j =
      algebraMap (AdjoinRoot m) (JetQuotient m r) (AdjoinRoot.root m)^j.1.val *
        AdjoinRoot.root (X^r)^j.2.val := by
  rw [jetPowerBasis, Basis.reindex_apply, Basis.coe_ofEquivFun]
  change jetQuotientValue m (Pi.single (j.2,j.1) 1) = _
  rw [jetQuotientValue_eq_sum, Finset.sum_eq_single (j.2,j.1)]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

end
end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
