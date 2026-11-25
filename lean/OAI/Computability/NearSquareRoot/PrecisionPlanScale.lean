import OAI.Computability.NearSquareRoot.PrecisionPlanNode
import OAI.Computability.NearSquareRoot.PhysicalWalshGridScaleNorm

/-! # Numerical safety of the recursive plan's dyadic scale instruction

The positive-level header enumerates exactly the physical lane. Its decoded
norm controls every accumulator reaching the scale instruction. The same gain
bounds the ideal output and the propagated input error.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication KernelPass PhysicalWalsh PhysicalWalshGrid

theorem scale_numericalStep {a W q : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (child : Fin (a+1) → Shape → IdealRow → IdealRow) (s : Shape) (hl : 0 < s.level)
    (frac : ℕ) (cap δ : ℝ) (hδ : 0 ≤ δ) (room : cap*2^frac < 2^s.w)
    (fault : Real.sqrt (laneCount a W s) * ((2:ℝ)/2^frac) ≤ δ)
    (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient) :
    NumericalStep (nodeOps hW plan) (idealOps a W child) (nodeGuards hW plan) s
      (laneSize a W s) (laneGap a W frac s) (.scale q test table)
      ((KernelScaleNorm.gain table : ℝ) + 1) cap δ := by
  intro x y B e hB he hcap bank
  let slot : Fin (laneCount a W s) → ℕ := Fin.val
  let v := atWidth (laneCount a W s) (y 0)
  let g : ℝ := KernelScaleNorm.gain table
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have cover : ∀ z ∈ (coords a W).rows s, ∃ j, slot j = z := by
    intro z hz
    rw [coords_rows s hl] at hz
    exact ⟨⟨z, List.mem_range.mp hz⟩, rfl⟩
  have hy : ‖v‖ ≤ B := (bank 0).1
  have hdiff : ‖decodeRow (coords a W) Shape.w frac s slot (x 0) - v‖ ≤ e := (bank 0).2
  have hx : ‖decodeRow (coords a W) Shape.w frac s slot (x 0)‖ ≤ B + e := by
    have h := norm_le_norm_sub_add (decodeRow (coords a W) Shape.w frac s slot (x 0)) v
    linarith
  change (g+1) * (B+e+δ) ≤ cap at hcap
  have fit : g*(B+e)*2^frac < 2^s.w := by
    have hgcap : g*(B+e) ≤ cap := by nlinarith [mul_nonneg hg hδ]
    exact (mul_le_mul_of_nonneg_right hgcap (by positivity)).trans_lt room
  refine ⟨scaleFits_of_row (coords a W) Shape.w test table frac s slot cover (x 0) (B+e) hx fit,
    fun j => ⟨?_, ?_⟩⟩
  · change ‖idealScaleRow (coords a W) test table s slot v‖ ≤ (g+1)*B
    exact (idealScaleRow_gain (coords a W) test table s slot v).trans
      ((mul_le_mul_of_nonneg_left hy hg).trans (by linarith))
  · change ‖decodeRow (coords a W) Shape.w frac s slot
        (scale (coords a W) Shape.w test table s (x 0)) -
      idealScaleRow (coords a W) test table s slot v‖ ≤ (g+1)*(e+δ)
    have step := scale_row_error (coords a W) Shape.w test table frac s slot
      (x 0) v (B+e) e hx hdiff fit
    simp only [Fintype.card_fin] at step
    apply step.trans
    change _ + g*e ≤ _
    nlinarith [mul_nonneg hg hδ]

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
