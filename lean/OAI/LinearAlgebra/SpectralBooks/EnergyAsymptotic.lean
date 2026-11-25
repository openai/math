import OAI.LinearAlgebra.SpectralBooks.EnergyStates
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Passing from tilted state counts to the energy asymptotic

At energy `X²` the optimal upper bound uses inverse temperature `√A/X`.
The lower bounds at temperatures `√A/(qX)` approach that upper bound as
`q` increases to one.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped Topology

private theorem exists_tilt_near_one {s c : ℝ} (hc : c < 2 * s) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ c < s * q + s * q ^ 3 := by
  have ht : Tendsto (fun q : ℝ ↦ s * q + s * q ^ 3) (𝓝[<] 1) (𝓝 (2 * s)) := by
    have h : Continuous (fun q : ℝ ↦ s * q + s * q ^ 3) := by fun_prop
    simpa [two_mul] using h.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio 1))
  have hp : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q := nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one)
  have hlt : ∀ᶠ q : ℝ in 𝓝[<] 1, q < 1 := self_mem_nhdsWithin
  exact (hp.and (hlt.and (ht.eventually (eventually_gt_nhds hc)))).exists

/-- A log partition function with `F(k/X)/X → A/k` and the tilted lower bound
determines the growth of the cumulative number of fermionic states. -/
theorem tendsto_log_fermionCount_div_sqrt_of_partition {A : ℝ} (hA : 0 < A)
    (hF : ∀ k : ℝ, 0 < k → Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X)
      atTop (𝓝 (A / k)))
    (hlower : ∀ q : ℝ, 0 < q → q < 1 → ∀ᶠ X : ℝ in atTop,
      fermionLogPartition ((√A / q) / X) + (√A * q ^ 3) * X - log 2 ≤
        log (fermionCount (X ^ 2))) :
    Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 (2 * √A)) := by
  have hs : 0 < √A := sqrt_pos.mpr hA
  have hsq := sq_sqrt hA.le
  have hX : ∀ᶠ X : ℝ in atTop, 0 < X := eventually_gt_atTop 0
  have hscaled : Tendsto (fun X : ℝ ↦ log (fermionCount (X ^ 2)) / X) atTop (𝓝 (2 * √A)) := by
    apply tendsto_order.mpr
    constructor
    · intro c hc
      obtain ⟨q, hq, hq1, hqc⟩ := exists_tilt_near_one hc
      have hquot : A / (√A / q) = √A * q := by field_simp; nlinarith
      have hzero : Tendsto (fun X : ℝ ↦ log 2 / X) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ht := ((hF (√A / q) (div_pos hs hq)).add_const (√A * q ^ 3)).sub hzero
      rw [hquot, sub_zero] at ht
      filter_upwards [ht.eventually (eventually_gt_nhds hqc), hlower q hq hq1, hX] with X h₁ h₂ hpos
      apply lt_of_lt_of_le h₁
      calc
        fermionLogPartition ((√A / q) / X) / X + √A * q ^ 3 - log 2 / X =
            (fermionLogPartition ((√A / q) / X) + (√A * q ^ 3) * X - log 2) / X := by
              field_simp
        _ ≤ _ := div_le_div_of_nonneg_right h₂ hpos.le
    · intro c hc
      have ht := (hF (√A) hs).const_add (√A)
      have heq : √A + A / √A = 2 * √A := by field_simp; nlinarith
      rw [heq] at ht
      filter_upwards [ht.eventually (eventually_lt_nhds hc), hX] with X hbound hpos
      apply lt_of_le_of_lt _ hbound
      have hcount : 0 < (fermionCount (X ^ 2) : ℝ) := by
        exact_mod_cast fermionCount_pos (sq_nonneg X)
      have hlog := (log_le_log hcount (fermionCount_le_exp (div_pos hs hpos) (X ^ 2)))
      rw [log_exp] at hlog
      calc
        log (fermionCount (X ^ 2)) / X ≤
            ((√A / X) * X ^ 2 + fermionLogPartition (√A / X)) / X :=
              div_le_div_of_nonneg_right hlog hpos.le
        _ = √A + fermionLogPartition (√A / X) / X := by field_simp
  apply (hscaled.comp Real.tendsto_sqrt_atTop).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp [Function.comp_apply, sq_sqrt hH]

/-- Base-two logarithm form of the cumulative count asymptotic. -/
theorem tendsto_logb_fermionCount_div_sqrt_of_log {L : ℝ}
    (h : Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 L)) :
    Tendsto (fun H : ℝ ↦ logb 2 (fermionCount H) / √H) atTop (𝓝 (L / log 2)) := by
  simpa only [logb, div_right_comm (log _) (log 2)] using h.div_const (log 2)

end SpectralBooks
end LinearAlgebra
end OAI
