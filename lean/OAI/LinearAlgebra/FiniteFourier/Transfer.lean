import OAI.LinearAlgebra.FiniteFourier.SlotMatrix
import OAI.LinearAlgebra.FiniteFourier.Geometry
import OAI.LinearAlgebra.FiniteFourier.TransferParameters
import OAI.LinearAlgebra.FiniteFourier.Feedback.WalkCount
import OAI.LinearAlgebra.FiniteFourier.FeedbackWeightedTransfer
import OAI.LinearAlgebra.FiniteFourier.FeedbackStateCompression
import OAI.LinearAlgebra.FiniteFourier.FeedbackBorder

/-!
# Comparing the delay coefficients with a thin Fourier rectangle

The binary walk estimate applies to the *original* delayed circuit, even when the state basis
used for rank compression is dense. Each slot of its matrix has an output row and an input column.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open scoped Classical

variable {K I O : Type*} [Field K]

/-- Apply the rectangle support estimate after grouping powered output and input indices. The
hypotheses concern only the two degenerate-rectangle evaluations and subadditivity in positions. -/
theorem Feedback.weighted_walk_of_rectangle_rows {s : ℕ} (F : Feedback K I O s)
    [Fintype I] [Fintype O] {m u : ℝ} (hm : Real.logb 2 (Fintype.card O) = m)
    (hu : 1 ≤ u) (hparams : ThinBounds m u) (ν : TensorValue K (O × I))
    (P : (j : ℕ) → PhasePrice (Matrix (Fin j → O) (Fin j → I) K))
    (value : ∀ j a, ν.price j a = rectangleValue (P j) (slotMatrix a) (thinS m u) (thinC m u))
    (addPos : ∀ j M x y, P j M (x+y) ≤ P j M x + P j M y)
    (rankEnd : ∀ j M, M ≠ 0 → rectanglePrice (P j) M 0 (2*thinC m u) ≤
      2*thinC m u * Real.logb 2 (Fintype.card (Fin j → O)))
    (supportEnd : ∀ j M, M ≠ 0 → rectanglePrice (P j) M (2*thinS m u) 0 =
      2*thinS m u * Real.logb 2 (∑ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card : ℕ)) :
    ∀ j i : ℕ, thinWeight m u ^ i *
      ν.price j (powerCoeff (Function.uncurry F.delaySeries) j i) ≤ thinJ m u ^ j := by
  intro j i
  let a := powerCoeff (fun p : O × I ↦ F.delaySeries p.1 p.2) j i
  change thinWeight m u ^ i * ν.price j a ≤ _
  by_cases hM : slotMatrix a = 0
  · rw [slotMatrix_eq_zero_iff.mp hM, ν.zero, mul_zero]
    exact pow_nonneg (thinJ_pos m u).le _
  · rw [value]
    have hpos : 0 < rectangleValue (P j) (slotMatrix a) (thinS m u) (thinC m u) := by
      simp only [rectangleValue, ite_eq_right hM]
      positivity
    apply weighted_walk_le hu hparams hpos
    have hrow := rectangleValue_row_bound (s := thinS m u) (c := thinC m u) hM
      hparams.s_pos (by linarith only [hparams.c_half]) (d := 2 ^ i) (fun row ↦ F.card_outputSupport i j row)
      (addPos j _) (rankEnd j _ hM) (supportEnd j _ hM)
    simpa [thinDelta, Fintype.card_fun, hm, Real.logb_pow] using hrow

theorem rank_pos_of_matrix_ne_zero [Fintype I] [Fintype O] {M : Matrix O I K}
    (h : M ≠ 0) : 0 < M.rank := by
  by_contra! hz
  have hbot := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz :
    Module.finrank K (LinearMap.range M.mulVecLin) = 0)
  have hlin := LinearMap.range_eq_bot.mp hbot
  apply h
  classical
  ext o i
  have he : M.mulVecLin (Pi.single i 1) = 0 := by rw [hlin]; rfl
  simpa using congrFun he o

/-- At one slot, the rank bound at half the rectangle width supplies the same value `J` as
 the bound on weighted walks. -/
theorem rectangleValue_le_thinJ_of_rank [Fintype I] [Fintype O] {m u : ℝ}
    (hu : 1 ≤ u) (hparams : ThinBounds m u) (P : PhasePrice (Matrix O I K)) (M : Matrix O I K)
    (hr : (M.rank : ℝ) ≤ thinRankFraction u * (2 : ℝ) ^ m)
    (addPos : ∀ x y, P M (x+y) ≤ P M x + P M y)
    (common : ∀ x : Fin 4 → Plane, P M x ≤ m/2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖))
    (rankEnd : M ≠ 0 → rectanglePrice P M 0 1 = Real.logb 2 M.rank) :
    rectangleValue P M (thinS m u) (thinC m u) ≤ thinJ m u := by
  by_cases hM : M = 0
  · simpa only [rectangleValue, hM, ite_true] using (thinJ_pos m u).le
  · have hpos : 0 < rectangleValue P M (thinS m u) (thinC m u) := by
      simp only [rectangleValue, ite_eq_right hM]
      positivity
    apply small_rank_le hu hparams hpos (by exact_mod_cast rank_pos_of_matrix_ne_zero hM) hr
    have he := rectangleValue_rank_bound (s := thinS m u) (c := thinC m u) (t := 1/2)
      (logRank := Real.logb 2 M.rank) hM hparams.s_pos (by linarith only [hparams.c_half])
      ⟨by norm_num, hparams.c_half⟩ addPos common (by simpa using rankEnd hM)
    simpa [thinDelta] using he

/-- The weighted walk and low-rank estimates bound the value of every small regular feedback
computation. Compression supplies the polynomial and its correction over the rational function
field; both estimates concern the original matrix coordinates. -/
theorem Feedback.value_le_of_walk_and_rank [Infinite K] [Fintype O] [Fintype I] {s : ℕ}
    (F : Feedback K I O s) (hF : F.Regular) {m u : ℝ} (hparams : ThinBounds m u)
    (budget : 2 * (s : ℝ) / thinBlock m u ≤ thinRankFraction u * (2 : ℝ) ^ m)
    (ν : TensorValue K (O × I))
    (walk : ∀ j i : ℕ, thinWeight m u ^ i *
      ν.price j (powerCoeff (Function.uncurry F.delaySeries) j i) ≤ thinJ m u ^ j)
    (rank : ∀ M : Matrix O I K, (M.rank : ℝ) ≤ thinRankFraction u * (2 : ℝ) ^ m →
      ν.price 1 (slotPower (Function.uncurry M) 1) ≤ thinJ m u) :
    ν.price 1 (slotPower (Function.uncurry F.matrix) 1) ≤ 5 * (2 : ℝ)^(-u) * thinFourierValue m u := by
  let b := thinBlock m u
  have hb : 0 < b := thinBlock_pos hparams
  obtain ⟨B, Q, hB, _, hQ, hR⟩ := F.state_compression hF b hb
  let r := (F.residual B Q).rank
  have hshare : (r : ℝ) ≤ 2 * s / b := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hb)).mpr
    have h : (r : ℝ) * b ≤ s := by exact_mod_cast hR
    linarith only [h, Nat.cast_nonneg (α := ℝ) s]
  have hcap (M : Matrix O I K) (hM : M.rank ≤ r) :=
    rank M (((Nat.cast_le (α := ℝ)).mpr hM).trans (hshare.trans budget))
  have h := F.weightedTransfer hF ν B Q (2*b) r hB hQ le_rfl (thinWeight_pos m u)
    (thinWeight_le_one hparams) (thinJ_pos m u).le (thinJ_pos m u).le 1
    (fun j i _ ↦ by simpa using walk j i) hcap
  apply small_computation_value_le hparams (d := 2*b) le_rfl
  rw [Real.rpow_neg (thinWeight_pos m u).le, Real.rpow_natCast]
  simpa only [inv_pow] using h

/-- An estimate that holds on exact systems passes to their geometric border if its sublevel
is cut out by polynomials. This also allows different graph topologies to occur in one closure. -/
theorem GeometricBorderAtMost.value_le {M : Matrix O I K} {S : ℕ} (h : GeometricBorderAtMost M S)
    (v : Matrix O I (AlgebraicClosure K) → ℝ) {B : ℝ}
    (closed : ∃ polys : Set (MvPolynomial (O × I) (AlgebraicClosure K)), ∀ A,
      v A ≤ B ↔ ∀ p ∈ polys, MvPolynomial.eval (fun q : O × I ↦ A q.1 q.2) p = 0)
    (exactBound : ∀ A, FeedbackAtMost A S → v A ≤ B) : v (M.map (algebraMap K _)) ≤ B := by
  obtain ⟨polys, hpolys⟩ := closed
  apply (hpolys _).mpr
  intro p hp
  exact h p (fun A hA ↦ (hpolys A).mp (exactBound A hA) p hp)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
