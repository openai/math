import OAI.Hierarchy.SupportingForces
import OAI.Hierarchy.ForceApproximation

namespace OAI
/-! # Individual leg capacities and stability at near-optimal price -/

namespace Hierarchy.HomogeneousFlat

open scoped InnerProductSpace BigOperators
open LinearAlgebra.SpectralBooks
variable {F : Type*} [Field F] {d : ℕ} (P : HomogeneousFlat F d)
variable {I : Type} [Fintype I]

omit [Field F] [Fintype I] in
/-- Each finite leg has a nonnegative logarithmic capacity, including empty legs. -/
theorem legCapacity_nonneg (T : SiteTensor.Raw.{0} I F) (i : I) :
    0 ≤ Real.logb 2 (Fintype.card (T.Leg i)) := by
  cases h : Fintype.card (T.Leg i) with
  | zero => simp
  | succ n => apply Real.logb_nonneg (by norm_num); exact_mod_cast Nat.succ_pos n

/-- The single-leg force bound follows directly from transport of the price. -/
theorem force_le_legCapacity (T : SiteTensor.Raw.{0} I F) (g : I → (EuclideanSpace ℝ (Fin d)))
    (dom : ∀ y : I → (EuclideanSpace ℝ (Fin d)), (∑ j, ⟪g j,y j⟫_ℝ) ≤ P.prices.price T y) (i : I) :
    ‖g i‖ ≤ Real.logb 2 (Fintype.card (T.Leg i)) := by
  classical
  let y (j : I) : (EuclideanSpace ℝ (Fin d)) := if j=i then g i else 0
  have hleft : (∑ j, ⟪g j,y j⟫_ℝ) = ‖g i‖ ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [y]
    · intro j _ hj; simp [y,hj]
    · simp
  have hright : (∑ j, dist (y j) 0 * Real.logb 2 (Fintype.card (T.Leg j))) =
      ‖g i‖ * Real.logb 2 (Fintype.card (T.Leg i)) := by
    rw [Finset.sum_eq_single i]
    · simp [y]
    · intro j _ hj; simp [y,hj]
    · simp
  have transport := P.prices.transport T y (fun _ => 0)
  rw [P.prices.collapsed,hright] at transport
  have lower := dom y
  rw [hleft] at lower
  have sq : ‖g i‖ ^ 2 ≤ ‖g i‖ * Real.logb 2 (Fintype.card (T.Leg i)) :=
    lower.trans ((le_abs_self _).trans (by simpa [Real.dist_eq] using transport))
  rcases (norm_nonneg (g i)).eq_or_lt with hz|h
  · rw [← hz]; exact legCapacity_nonneg T i
  · rw [pow_two] at sq
    exact (mul_le_mul_iff_right₀ h).mp sq

/-- Every near-maximal summand has one tuple of balanced forces simultaneously
approximating the prescribed terminal loads. -/
theorem near_price_forces (T : SiteTensor.Raw.{0} I F) (x : I → (EuclideanSpace ℝ (Fin d))) (loss : ℝ)
    (hx : ∀ i, ‖x i‖ = 1)
    (near : (∑ i, Real.logb 2 (Fintype.card (T.Leg i))) - loss ≤ P.prices.price T x) :
    ∃ g : I → (EuclideanSpace ℝ (Fin d)), (∑ i, g i) = 0 ∧
      (∀ y, (∑ i, ⟪g i,y i⟫_ℝ) ≤ P.prices.price T y) ∧
      ∑ i, ‖g i - Real.logb 2 (Fintype.card (T.Leg i)) • x i‖ ≤
        Real.sqrt (2 * (∑ i, Real.logb 2 (Fintype.card (T.Leg i))) * loss) := by
  obtain ⟨g,eq,dom,bal⟩ := P.supporting_forces T x
  refine ⟨g,bal,dom,ForceApproximation.sum_norm_sub_le Finset.univ _ x g loss
    (fun i _ => legCapacity_nonneg T i) (fun i _ => hx i)
    (fun i _ => P.force_le_legCapacity T g dom i) ?_⟩
  exact near.trans eq.ge


end Hierarchy.HomogeneousFlat

end OAI
