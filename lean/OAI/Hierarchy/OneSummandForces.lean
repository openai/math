import OAI.Hierarchy.ForceLegBound
import OAI.Hierarchy.ForceSelection
import OAI.Hierarchy.ForceCutRank

namespace OAI
/-! # Approximate forces and simultaneous rank bounds on an actual summand -/

namespace Hierarchy.HomogeneousFlat

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators InnerProductSpace

variable {F : Type*} [Field F] {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    {A : I → Type} [∀ i, Fintype (A i)] {J : Type*} [Fintype J] {d : ℕ}

/-- The original summand and its balanced forces are chosen once. The same
choice works for all cuts of the original legs. An antipodal product of wires
can supply the hypothesis that the target price equals total leg capacity. -/
theorem one_summand_forces (P : HomogeneousFlat F d) (x : I → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ = 1)
    {S : Set (J → (∀ i, A i) → F)} {t : (∀ i, A i) → F}
    (cl : t ∈ affineZariskiClosure ((fun Y => ∑ j, Y j) '' S)) (ht : t ≠ 0)
    (price : P.prices.price (ForceSelection.raw t) x = ∑ i, Real.logb 2 (Fintype.card (A i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y ∈ S, ∃ j, Y j ≠ 0 ∧ ∃ g : I → EuclideanSpace ℝ (Fin d),
      (∑ i, g i) = 0 ∧
      (∀ y, (∑ i, ⟪g i,y i⟫_ℝ) ≤ P.prices.price (ForceSelection.raw (Y j)) y) ∧
      (∑ i, ‖g i - Real.logb 2 (Fintype.card (A i)) • x i‖) ≤
        Real.sqrt (2 * (∑ i, Real.logb 2 (Fintype.card (A i))) *
          (ε + P.prices.price (Raw.diagonal I F (Fin 2)) x * Real.logb 2 (Fintype.card J))) ∧
      ∀ U : Finset I, ‖∑ i ∈ U, g i‖ ≤ Real.logb 2 (ABPFirstCut.flatten U (Y j)).rank := by
  classical
  obtain ⟨Y,hY,j,hj,near⟩ := ForceSelection.exists_summand P.prices x cl ht hε
  rw [price] at near
  obtain ⟨g,bal,support,err⟩ := P.near_price_forces (ForceSelection.raw (Y j)) x
    (ε + P.prices.price (Raw.diagonal I F (Fin 2)) x * Real.logb 2 (Fintype.card J)) hx
    (by simpa only [← sub_sub] using near.le)
  exact ⟨Y,hY,j,hj,g,bal,support,err,P.force_cut_rank (ForceSelection.raw (Y j)) hj g support⟩

end Hierarchy.HomogeneousFlat

end OAI
