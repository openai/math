import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! # Paired coordinates adapted to a subspace

Split the primal space along a complement to the chosen subspace. In the dual
coordinates the annihilator is the second coordinate block, and the perfect
pairing becomes the sum of the two coordinate dot products.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module

/-- Coordinate charts for both endpoints of a nondegenerate symmetric pairing. -/
theorem exists_primeEndpointDualCharts {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hSym : B.IsSymm) (H : Submodule K E) :
    ∃ (c : ℕ) (e e' : E ≃ₗ[K] (Fin (finrank K H) → K) × (Fin c → K)),
      finrank K H + c = finrank K E ∧
      (∀ x, x ∈ H ↔ (e x).2 = 0) ∧
      (∀ s, (∀ x ∈ H, B x s = 0) ↔ (e' s).1 = 0) ∧
      ∀ x s, B x s = (∑ i, (e x).1 i * (e' s).1 i) +
        ∑ j, (e x).2 j * (e' s).2 j := by
  classical
  obtain ⟨C, hc⟩ := H.exists_isCompl
  let v := H.prodEquivOfIsCompl C hc
  let bH := Module.finBasis K H
  let bC := Module.finBasis K C
  let b := (bH.prod bC).map v
  let e := v.symm.trans (bH.equivFun.prodCongr bC.equivFun)
  let e' := ((B.toDual hB).trans b.dualBasis.equivFun).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ K K)
  have hm (x : E) : x ∈ H ↔ (e x).2 = 0 := by
    change x ∈ H ↔ bC.equivFun (v.symm x).2 = 0
    rw [map_eq_zero_iff _ bC.equivFun.injective]
    exact (H.prodEquivOfIsCompl_symm_apply_snd_eq_zero C hc).symm
  have hp (x s : E) : B x s = (∑ i, (e x).1 i * (e' s).1 i) +
      ∑ j, (e x).2 j * (e' s).2 j := by
    have hv := congrArg (B s) (b.sum_repr x)
    rw [map_sum, Fintype.sum_sum_type] at hv
    simp only [map_smul, smul_eq_mul] at hv
    rw [hSym.eq]
    convert hv.symm using 1
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
    · change b.repr x (Sum.inl i) * b.dualBasis.equivFun (B.toDual hB s) (Sum.inl i) = _
      rw [b.dualBasis_equivFun]
      rfl
    · change b.repr x (Sum.inr i) * b.dualBasis.equivFun (B.toDual hB s) (Sum.inr i) = _
      rw [b.dualBasis_equivFun]
      rfl
  refine ⟨finrank K C, e, e', Submodule.finrank_add_eq_of_isCompl hc, hm, ?_, hp⟩
  intro s
  constructor
  · intro hs
    funext i
    let x := e.symm (Pi.single i 1, 0)
    have hx : e x = (Pi.single i 1, 0) := e.apply_symm_apply _
    have h := hs x ((hm x).mpr (by rw [hx]))
    rw [hp, hx] at h
    simpa [Pi.single_apply, ite_mul] using h
  · intro hs x hx
    rw [hp, hs, (hm x).mp hx]
    simp

end FiniteFourier
end LinearAlgebra
end OAI
