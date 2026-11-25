import OAI.Hierarchy.OneSummandForces
import OAI.Hierarchy.ABPFirstCutRegroup

namespace OAI
/-! # A large prescribed cut load forces a rank lower bound on a border sum -/

namespace Hierarchy.HomogeneousFlat

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators InnerProductSpace
open ABPFirstCut

variable {F : Type*} [Field F] {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    {A : I → Type} [∀ i, Fintype (A i)] {J : Type} [Fintype J] {d : ℕ}

/-- First-hit decompositions may use a different low-rank cut in every term.
A single geometric lower bound valid on all these possible cuts is enough. -/
theorem hard_load_le_of_rankSumsOn (P : HomogeneousFlat F d)
    (x : I → EuclideanSpace ℝ (Fin d)) (hx : ∀ i, ‖x i‖ = 1)
    (cuts : J → Finset I) {s : ℕ} {t : (∀ i, A i) → F}
    (cl : t ∈ affineZariskiClosure (rankSumsOn cuts s)) (ht : t ≠ 0)
    (price : P.prices.price (ForceSelection.raw t) x = ∑ i, Real.logb 2 (Fintype.card (A i)))
    (load : ℝ) (hard : ∀ j, load ≤ ‖∑ i ∈ cuts j, Real.logb 2 (Fintype.card (A i)) • x i‖)
    {ε : ℝ} (hε : 0 < ε) :
    load ≤ Real.logb 2 (s+2 : ℕ) + Real.sqrt (2 * (∑ i, Real.logb 2 (Fintype.card (A i))) *
      (ε + P.prices.price (Raw.diagonal I F (Fin 2)) x * Real.logb 2 (Fintype.card J))) := by
  classical
  let S : Set (J → (∀ i, A i) → F) := { Y | ∀ j, (flatten (cuts j) (Y j)).rank ≤ s }
  have included : rankSumsOn cuts s ⊆ (fun Y => ∑ j, Y j) '' S := by
    rintro z ⟨Y,hY,h⟩
    exact ⟨Y,h,funext (fun a => by simpa [Finset.sum_apply] using (hY a).symm)⟩
  obtain ⟨Y,hY,j,_,g,_,_,err,hcut⟩ := P.one_summand_forces x hx (S := S)
    (fun p hp => cl p (fun z hz => hp z (included hz))) ht price hε
  have hrank : (flatten (cuts j) (Y j)).rank ≤ s := hY j
  have hlog : Real.logb 2 ((flatten (cuts j) (Y j)).rank) ≤ Real.logb 2 (s+2 : ℕ) := by
    cases h : (flatten (cuts j) (Y j)).rank with
    | zero => simp only [Nat.cast_zero,Real.logb_zero]; apply Real.logb_nonneg (by norm_num); exact_mod_cast (show 1 ≤ s+2 by omega)
    | succ n =>
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      exact_mod_cast (show n+1 ≤ s+2 by omega)
  exact (hard j).trans (ForceApproximation.cut_load_le (Finset.subset_univ _) _ x g _ _ err
    ((hcut (cuts j)).trans hlog))

end Hierarchy.HomogeneousFlat

end OAI
