import OAI.LinearAlgebra.FiniteFourier.BatchedTwoMinors

/-! # The joint robust lower estimate for every bounded range of orders

One row and two distinct coordinates per block suffice here. The constants
can depend on the cutoff used to start the large-order spectral argument.
They are uniform in the batch size, field, groups, and circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
universe u v

theorem batchFourier_bounded_orders (N : ℕ) (hN : 2 ≤ N) :
    ∃ c β η : ℝ, 0 < c ∧ 0 < β ∧ 0 < η ∧
    ∀ {J n : ℕ} (K : Type v) [Field K] (B : Fin J → FourierBlock.{u,v} K n),
      2 ≤ n → n ≤ N → ∀ s : ℕ,
      let h : ℝ := J * (n : ℝ)
      let l := Real.sqrt (Real.logb 2 n)
      JointErrorBorderAtMost (batchMatrix B) s (β*h) (η*h*(2:ℝ)^(l/8)) →
      c*h*l ≤ s := by
  let L := Real.sqrt (Real.logb 2 N)
  let A := (2 : ℝ) ^ (L / 8)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := Real.sqrt_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast hN))
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨1 / (4 * N * L), 1 / (16 * N), 1 / (16 * N * A),
    by positivity, by positivity, by positivity, ?_⟩
  intro J n K _ B hn hnN s
  dsimp only
  intro h
  let l := Real.sqrt (Real.logb 2 n)
  have hn' : (n : ℝ) ≤ N := Nat.cast_le.mpr hnN
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hl : l ≤ L := Real.sqrt_le_sqrt ((Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hnp hNp).mpr hn')
  have hpow : (2 : ℝ) ^ (l/8) ≤ A :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by gcongr)
  have mass : (J : ℝ) * n ≤ J * N := by gcongr
  have rankCap : (1 / (16 * (N : ℝ))) * (J * (n : ℝ)) ≤ J / 16 := by
    calc
      _ ≤ (1 / (16 * (N : ℝ))) * (J * N) := by gcongr
      _ = _ := by field_simp
  have sparseCap : (1 / (16 * (N : ℝ) * A)) * (J * (n : ℝ)) * (2:ℝ)^(l/8) ≤ J / 16 := by
    calc
      _ ≤ (1 / (16 * (N : ℝ) * A)) * (J * N) * A := by gcongr
      _ = _ := by field_simp
  have two := batchFourier_two_minors B hn h
  change (J : ℝ) ≤ 2 * (s + (1 / (16 * (N : ℝ))) * (J * n) +
    (1 / (16 * (N : ℝ) * A)) * (J * n) * (2:ℝ)^(l/8)) at two
  change (1 / (4 * (N : ℝ) * L)) * (J * (n : ℝ)) * l ≤ s
  calc
    _ ≤ (1 / (4 * (N : ℝ) * L)) * (J * N) * L := by gcongr
    _ = J / 4 := by field_simp
    _ ≤ _ := by linarith

end FiniteFourier
end LinearAlgebra
end OAI
