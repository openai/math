import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Tactic.Linarith

/-! # Recovering the norm from the dual parallelogram bound -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Applying the upper parallelogram bound to the two diagonals recovers its reverse. -/
theorem parallelogram_eq_of_le (h : ∀ a b : V,
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)) (x y : V) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  refine le_antisymm (h x y) ?_
  have h' := h (x + y) (x - y)
  have hp : x + y + (x - y) = (2 : ℝ) • x := by rw [two_smul]; abel
  have hm : x + y - (x - y) = (2 : ℝ) • y := by rw [two_smul]; abel
  rw [hp, hm, norm_smul, norm_smul, Real.norm_ofNat] at h'
  linarith

/-- The dual parallelogram bound forces the original norm to come from a real inner product.
The Hahn–Banach embedding into the bidual followed by inverse Riesz is an isometry into
the dual with its Jordan–von Neumann inner product. -/
theorem innerProductSpace_of_dualParallelogramLe
    (h : ∀ a b : StrongDual ℝ V,
      ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)) :
    Nonempty (InnerProductSpace ℝ V) := by
  let : InnerProductSpace ℝ (StrongDual ℝ V) :=
    InnerProductSpace.ofNorm ℝ fun a b ↦ by simpa [sq] using parallelogram_eq_of_le h a b
  let j := NormedSpace.inclusionInDoubleDualLi (E := V) ℝ
  let r := (InnerProductSpace.toDual ℝ (StrongDual ℝ V)).symm
  refine ⟨InnerProductSpace.ofNorm ℝ fun x y ↦ ?_⟩
  simpa only [← r.map_add, ← r.map_sub, ← j.map_add, ← j.map_sub,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
    using parallelogram_law_with_norm_mul ℝ (r (j x)) (r (j y))

/-- The positive-weight bound on the dual unit ball gives the full-norm inequality
by normalizing the two nonzero functionals separately. -/
theorem innerProductSpace_of_dualBallParallelogramLe
    (h : ∀ (t u : ℝ), 0 < t → 0 < u → ∀ f g : StrongDual ℝ V, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
      ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2)) :
    Nonempty (InnerProductSpace ℝ V) := by
  apply innerProductSpace_of_dualParallelogramLe
  intro a b
  by_cases ha : a = 0
  · subst a; simp; linarith
  by_cases hb : b = 0
  · subst b; simp; linarith
  have normed (v : StrongDual ℝ V) (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀
      (norm_ne_zero_iff.mpr hv)]
  simpa [smul_smul, norm_ne_zero_iff.mpr ha, norm_ne_zero_iff.mpr hb] using
    h ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
      (‖a‖⁻¹ • a) (‖b‖⁻¹ • b) (normed a ha) (normed b hb)

end SpectralBooks
end LinearAlgebra
end OAI
