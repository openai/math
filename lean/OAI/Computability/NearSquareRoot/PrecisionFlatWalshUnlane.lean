import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIndex
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIdeal
import OAI.Computability.NearSquareRoot.PrecisionPlanNode

/-! # Reassembling exact Walsh row banks in physical tape order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open KernelPass PhysicalWalshNode
noncomputable section

theorem idealLane_chart (a W : ℕ) (s : Shape) (hl : 0 < s.level)
    (x : IdealRow) (g : ℕ) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    idealLane (a+1) W s x b (rowPos a s g u t) = x (rowPos a s (g*W+b.val) u t) := by
  rw [idealLane, rowPos_div a s hl, rowPos_mod a s hl, rowPos_block a s hl (g*W+b.val)]

theorem idealUnlane_chart (a W : ℕ) (hW : 0 < W) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (x : Fin W → IdealRow)
    (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    idealUnlane (a+1) hW s x ((chart a W s hl hd).symm ((g,b,t),u)) = x b (rowPos a s g u t) := by
  rw [idealUnlane, chart_symm_val]
  apply congrArg₂ x
  · apply Fin.ext
    change (rowPos a s (g.val*W+b.val) u t / PhysicalWalshNode.inner (a+1) s) % W = b.val
    rw [rowPos_div a s hl, Nat.mul_comm g.val W, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  · rw [rowPos_div a s hl, rowPos_mod a s hl, Nat.mul_comm g.val W, Nat.mul_add_div hW,
      Nat.div_eq_of_lt b.isLt, Nat.add_zero, rowPos_block a s hl g.val]

theorem idealRow_rowPos (a : ℕ) (s : Shape) (hl : 0 < s.level) (x : IdealRow)
    (g : ℕ) (t : Fin s.suff) (z : NodeAddress a s) :
    idealRow (a+1) s x (rowPos a s g z t) =
      ∑ u : NodeAddress a s, BoxFin.flatWalsh Finset.univ (KernelScaleLayout.rank z)
        (KernelScaleLayout.rank u) * x (rowPos a s g u t) := by
  have width : grow (a+1) s.level = (a+1)*(2*(a+1)^(s.level-1)) := by
    unfold grow
    nth_rw 1 [← Nat.sub_add_cancel hl]
    rw [pow_succ]
    ring
  unfold idealRow
  rw [width]
  rw [rowPos, activeRow_at _ s.suff s.suff_pos]
  rw [← (KernelScaleLayout.addressEquiv a ((a+1)^(s.level-1))).symm.sum_comp]
  rfl

/-- A bank implementing the exact active-fiber Walsh matrix, once reassembled,
computes exactly the full node on every retained physical address. -/
theorem reassemble (a W : ℕ) (hW : 0 < W) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (x : IdealRow) (bank : Fin W → IdealRow)
    (fiber : ∀ (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (z : NodeAddress a s),
      bank b (rowPos a s g.val z t) =
        ∑ u : NodeAddress a s, BoxFin.flatWalsh Finset.univ (KernelScaleLayout.rank z)
          (KernelScaleLayout.rank u) * idealLane (a+1) W s x b (rowPos a s g.val u t)) :
    atWidth (count (a+1) s) (idealUnlane (a+1) hW s bank) =
      atWidth (count (a+1) s) (idealRow (a+1) s x) := by
  ext n
  obtain ⟨⟨⟨g,b,t⟩,z⟩,rfl⟩ := (chart a W s hl hd).symm.surjective n
  change idealUnlane (a+1) hW s bank ((chart a W s hl hd).symm ((g,b,t),z)) =
    idealRow (a+1) s x ((chart a W s hl hd).symm ((g,b,t),z))
  rw [idealUnlane_chart, fiber, chart_symm_val, idealRow_rowPos _ _ hl]
  simp only [idealLane_chart a W s hl]

/-- The complete ideal node propagates any finite-prefix input perturbation
with gain one in the decoded Euclidean norm. -/
theorem idealRow_distance (A : ℕ) (s : Shape) (x y : IdealRow) :
    ‖atWidth (count A s) (idealRow A s x) - atWidth (count A s) (idealRow A s y)‖ =
      ‖atWidth (count A s) x - atWidth (count A s) y‖ := by
  rw [show atWidth (count A s) (idealRow A s x) = nodeIsometry A s (atWidth (count A s) x)
    from idealRow_isometry A s x, show atWidth (count A s) (idealRow A s y) =
      nodeIsometry A s (atWidth (count A s) y) from idealRow_isometry A s y, ← map_sub]
  exact (nodeIsometry A s).norm_map _

end
end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
