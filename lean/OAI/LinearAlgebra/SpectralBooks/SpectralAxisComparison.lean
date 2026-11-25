import OAI.LinearAlgebra.SpectralBooks.CrossingWireClass
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatRigidity
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal

/-!
# The missing-flat witness for a normalized spectral point

The finite point is a semiring homomorphism monotone for actual tensor restriction.
The CAT(0) extension retains every old tensor price. Its distance on a binary
wire is consequently the logarithm of the original homomorphism's value, and
the price of the entire crossing is the sum of its diameter distances.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section
namespace Crossing

open SiteTensor HyperbolicObstruction

variable {F X : Type*} [Field F] [MetricSpace X]

private theorem diagonal_coeff_ne_zero {I : Type} [Fintype I] [Nonempty I] :
    (Raw.diagonal I F (Fin 2)).coeff ≠ 0 := by
  intro h
  let i : I := Classical.choice inferInstance
  have hh := congrFun h (fun _ => (0 : Fin 2))
  change (Raw.diagonal I F (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : F) at hh
  rw [Raw.diagonal_coeff_at i] at hh
  simp at hh

/-- The wire distance in a price-preserving extension agrees with the
original normalized point's log price on the two sites. -/
theorem dist_eq_wire_price {I : Type} [Fintype I] [Nonempty I]
    (φ : normalizedSpectrum (fun a b : TensorClass.{0} I F => a ≤ b))
    (P : SpectralPlacementPrices F X) (y : I → X)
    (hold : ∀ T : Raw.{0} I F, T.coeff ≠ 0 → P.price T y = Real.logb 2 (φ.val (ofRaw T) : ℝ))
    (e : Wire I) :
    dist (y e.left) (y e.right) = Real.logb 2
      (φ.val (ofRaw (({e with width := 1} : Wire I).raw F)) : ℝ) := by
  let σ : Fin 2 → I := ![e.left, e.right]
  let B := Raw.diagonal (Fin 2) F (Fin 2)
  calc
    dist (y e.left) (y e.right) = P.price B (y ∘ σ) := by
      simpa only [σ, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, B] using (P.wire (y ∘ σ)).symm
    _ = P.price (B.group σ) y := P.group B σ y
    _ = Real.logb 2 (φ.val (ofRaw (B.group σ)) : ℝ) :=
      hold _ ((B.group_ne_zero_iff _).2 diagonal_coeff_ne_zero)
    _ = _ := by rw [Wire.ofRaw_binary_eq_group_diagonal]

/-- The strict spectral inequality used in the missing-flat branch,
specialized to the actual tensor semiring on the marked Euclidean sites.
The realization hypothesis is precisely the extension of this finite
point into a CAT(0) space while retaining its old prices. -/
theorem exists_strict_wire_of_missing_flat {D : ℕ} (hD : 0 < D)
    (φ : normalizedSpectrum (fun a b : TensorClass.{0} (AxisSite D) F => a ≤ b))
    (P : SpectralPlacementPrices F X) (hcat : CATZero X) (y : AxisSite D → X)
    (hold : ∀ T : Raw.{0} (AxisSite D) F, T.coeff ≠ 0 →
      P.price T y = Real.logb 2 (φ.val (ofRaw T) : ℝ))
    (hmissing : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin D)))) :
    ∃ e : AxisPair D, Real.logb 2 (φ.val (ofRaw (crossingRaw F D 1)) : ℝ) <
      (2 * D / axisLength e) * Real.logb 2 (φ.val (ofRaw ((axisWire e 1).raw F)) : ℝ) := by
  have hdiag : 0 < P.price (Raw.diagonal _ F (Fin 2)) y := by
    rw [hold _ diagonal_coeff_ne_zero, ofRaw_diagonal_fin_eq_natCast]
    change 0 < Real.logb 2 ((normalizedSpectrum.toRingHom φ) (2 : TensorClass.{0} (AxisSite D) F) : ℝ)
    norm_num [map_ofNat, Real.logb_self_eq_one]
  obtain ⟨e, he⟩ := exists_pair_of_no_spectral_flat P hcat hD y hdiag hmissing
  refine ⟨e, ?_⟩
  rw [logb_crossingRaw_one_eq_sum]
  have hsum : diameterSum y =
      ∑ i, Real.logb 2 (φ.val (ofRaw ((diameterWire i 1).raw F)) : ℝ) :=
    Finset.sum_congr rfl fun i _ => dist_eq_wire_price φ P y hold (diameterWire i 1)
  rw [hsum] at he
  exact he.trans_eq (congrArg ((2 * (D : ℝ) / axisLength e) * ·)
    (dist_eq_wire_price φ P y hold (axisWire e 1)))

end Crossing
end

end

end SpectralBooks
end LinearAlgebra
end OAI
