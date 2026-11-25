import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Prices of matchings at four marked sites

The two crossing wires and their two uncrossings use sites numbered cyclically.
The phase correction assigns half a unit to each of the two crossing pairs.
-/

open scoped BigOperators

namespace ThreeFlat

def xDemand (d : Fin 4 → Fin 4 → ℝ) : ℝ := d 0 2 + d 1 3

def xSide (d : Fin 4 → Fin 4 → ℝ) : ℝ := max (d 0 1 + d 2 3) (d 0 3 + d 1 2)

def xMass (d : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, d i j

noncomputable def phaseCorr (b : Fin 4 → ℝ) : ℝ := (|b 0 - b 2| + |b 1 - b 3|) / 2

theorem le_xMass {d : Fin 4 → Fin 4 → ℝ} (hd : ∀ i j, 0 ≤ d i j) (i j : Fin 4) :
    d i j ≤ xMass d := by
  exact (Finset.single_le_sum (fun k _ => hd i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hd k l)
      (Finset.mem_univ i))

theorem xDemand_mul (c : ℝ) (d : Fin 4 → Fin 4 → ℝ) :
    xDemand (fun i j => c * d i j) = c * xDemand d := by simp [xDemand, mul_add]

theorem xSide_mul {c : ℝ} (hc : 0 ≤ c) (d : Fin 4 → Fin 4 → ℝ) :
    xSide (fun i j => c * d i j) = c * xSide d := by
  simp [xSide, mul_add, mul_max_of_nonneg _ _ hc]

theorem xMass_mul (c : ℝ) (d : Fin 4 → Fin 4 → ℝ) :
    xMass (fun i j => c * d i j) = c * xMass d := by
  simp [xMass, Finset.mul_sum]

theorem phaseCorr_mul {c : ℝ} (hc : 0 ≤ c) (b : Fin 4 → ℝ) :
    phaseCorr (fun i => c * b i) = c * phaseCorr b := by
  simp only [phaseCorr, ← mul_sub, abs_mul, abs_of_nonneg hc]
  ring

/-- A product of a line and a metric satisfying the tree four-point inequality has
a crossed price bounded by a side matching and the changes of the longitudinal phase. -/
theorem crossing_le_of_transverse_fourPoint {d q : Fin 4 → Fin 4 → ℝ} (t : Fin 4 → ℝ)
    (htree : xDemand q ≤ xSide q) (hproj : ∀ i j, q i j ≤ d i j)
    (hc : ∀ i j, d i j ≤ q i j + |t i - t j|) :
    xDemand d ≤ xSide d + phaseCorr (fun i => 2 * t i) := by
  have hside : xSide q ≤ xSide d := max_le_max
    (add_le_add (hproj 0 1) (hproj 2 3)) (add_le_add (hproj 0 3) (hproj 1 2))
  rw [phaseCorr_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold xDemand phaseCorr at *
  linarith [hc 0 2, hc 1 3]

end ThreeFlat

end OAI
