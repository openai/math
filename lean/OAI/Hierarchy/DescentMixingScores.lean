import OAI.Hierarchy.DescentLinearLayouts
import OAI.Hierarchy.DescentBaseOverload
import OAI.Hierarchy.DescentRowScore

namespace OAI
/-! # The actual Walsh scoring coefficients of the exceptional-base estimator -/

namespace Hierarchy.DescentBaseVariance
open DescentGL DescentLinearLayouts DescentRowScore
open scoped BigOperators Classical
noncomputable section

def layoutHom {bits j : ℕ} (hj : j≤bits) (L : Layout bits) : Bits bits→+Bits j where
  toFun := layout hj L
  map_zero' := by ext i; simp [layout,headRows]
  map_add' x y := by ext i; simp [layout,headRows]

@[simp] theorem layout_zero {bits j : ℕ} (hj : j≤bits) (L : Layout bits) :
    layout hj L 0=0 := (layoutHom hj L).map_zero

/-- Drop the zero difference, whose autocorrelation is the sum of squared
individual weights and is shared by every candidate matrix. -/
def offDiagonal {bits j : ℕ} (hj : j≤bits) (L : Layout bits) (x : Bits bits→ℝ) : ℝ :=
  ∑ d ∈ Finset.univ.erase 0,if layout hj L d=0 then autocorrelation x d else 0

theorem square_loads_by_difference {bits j : ℕ} (hj : j≤bits) (L : Layout bits) (x : Bits bits→ℝ) :
    (∑ b,(load (layout hj L) x b)^2) = offDiagonal hj L x + ∑ i,x i^2 := by
  rw [square_load_sum]
  trans ∑ d,@ite ℝ (layout hj L d=0) (Classical.propDecidable _) (autocorrelation x d) 0
  · exact regroup_collisions (layoutHom hj L) x
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Bits bits))]
  simp [offDiagonal,autocorrelation,pow_two]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hit : layout hj L d=0 <;> simp [hit]

theorem variance_by_difference {bits j : ℕ} (hj : j≤bits) (L : Layout bits) (x : Bits bits→ℝ) :
    variance (layout hj L) x = offDiagonal hj L x + ((∑ i,x i^2) - (∑ i,x i)^2/(2:ℝ)^j) := by
  rw [variance_eq,square_loads_by_difference,card_bits]
  push_cast
  ring

theorem level_by_difference {bits j : ℕ} (hj : j≤bits) (L : Layout bits) (x : Bits bits→ℝ)
    (s : ℕ) (F : ℝ) :
    levelCharge s F (layout hj L) x = offDiagonal hj L x +
      if 1/F≤1/(2:ℝ)^s then (∑ i,x i^2) - (∑ i,x i)^2/(2:ℝ)^j else 0 := by
  by_cases coarse : 1/F≤1/(2:ℝ)^s
  · simp only [levelCharge,coarse,ite_true,variance_by_difference]
  · simp only [levelCharge,coarse,ite_false,surplus,square_loads_by_difference]
    ring

end
end Hierarchy.DescentBaseVariance

end OAI
