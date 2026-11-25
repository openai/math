import OAI.Computability.NearSquareRoot.PrecisionPlanNode
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIndex

/-! # Finite-lane isometry for the physical XOR instruction

The physical ordinal permutation fixes the spectator fields and changes the
active paired columns by an involution. Reindexing the finite row therefore
preserves its Euclidean norm and the error from an ideal row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open KernelPass PhysicalWalsh FlatWalshNode
noncomputable section

private theorem xorColumn_twice {A : ℕ} (gate : Fin A × Fin A) (x : Column A) :
    xorColumn gate (xorColumn gate x) = x := by
  funext i j
  by_cases hi : gate.1 ≠ gate.2 ∧ i = gate.1
  · simp [xorColumn, hi, hi.1.symm, add_assoc, ZModModule.add_self]
  · simp [xorColumn, hi]

private def xorAddress (a : ℕ) (s : Shape) (gate : Fin (a+1) × Fin (a+1)) :
    Equiv.Perm (NodeAddress a s) where
  toFun u := xorColumn gate ∘ u
  invFun u := xorColumn gate ∘ u
  left_inv u := funext fun j => xorColumn_twice gate (u j)
  right_inv u := funext fun j => xorColumn_twice gate (u j)

/-- The address gate on the exact finite ordinal interval stored in a lane. -/
def xorLanePerm (a W : ℕ) (s : Shape) (hl : 0 < s.level) (gate : Fin (a+1) × Fin (a+1)) :
    Equiv.Perm (Fin (laneCount a W s)) :=
  (laneChart a W s hl).trans ((Equiv.prodCongr (Equiv.refl _) (xorAddress a s gate)).trans
    (laneChart a W s hl).symm)

theorem xorLanePerm_val (a W : ℕ) (s : Shape) (hl : 0 < s.level) (gate : Fin (a+1) × Fin (a+1))
    (j : Fin (laneCount a W s)) : (xorLanePerm a W s hl gate j).val = xorIndex a gate s j.val := by
  obtain ⟨⟨⟨g,t⟩,u⟩,rfl⟩ := (laneChart a W s hl).symm.surjective j
  let chart := laneChart a W s hl
  have he : xorLanePerm a W s hl gate (chart.symm ((g,t),u)) =
      chart.symm ((g,t),xorColumn gate ∘ u) := by
    change chart.symm ((Equiv.prodCongr (Equiv.refl _) (xorAddress a s gate))
      (chart (chart.symm ((g,t), u)))) = _
    rw [chart.apply_symm_apply]
    rfl
  calc
    _ = (chart.symm ((g,t),xorColumn gate ∘ u)).val := congrArg Fin.val he
    _ = rowPos a s g (xorColumn gate ∘ u) t :=
      laneChart_symm_val a W s hl g t _
    _ = _ := (xorIndex_rowPos a gate s g u t).symm.trans
      (congrArg (xorIndex a gate s) (laneChart_symm_val a W s hl g t u).symm)

private def xorLaneIsometry (a W : ℕ) (s : Shape) (hl : 0 < s.level) (gate : Fin (a+1) × Fin (a+1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (xorLanePerm a W s hl gate).symm

private theorem atWidth_xorIndex (a W : ℕ) (s : Shape) (hl : 0 < s.level)
    (gate : Fin (a+1) × Fin (a+1)) (y : IdealRow) :
    atWidth (laneCount a W s) (y ∘ xorIndex a gate s) =
      xorLaneIsometry a W s hl gate (atWidth (laneCount a W s) y) := by
  ext j
  change y (xorIndex a gate s j.val) = y (xorLanePerm a W s hl gate j).val
  rw [xorLanePerm_val]

theorem laneSize_xor (a W : ℕ) (s : Shape) (hl : 0 < s.level)
    (gate : Fin (a+1) × Fin (a+1)) (y : IdealRow) :
    laneSize a W s (y ∘ xorIndex a gate s) = laneSize a W s y := by
  simp only [laneSize, atWidth_xorIndex a W s hl, LinearIsometryEquiv.norm_map]

theorem laneGap_xor (a W p : ℕ) (s : Shape) (hl : 0 < s.level)
    (gate : Fin (a+1) × Fin (a+1)) (x : Data s) (y : IdealRow) :
    laneGap a W p s (xor a gate s x) (y ∘ xorIndex a gate s) = laneGap a W p s x y := by
  change ‖atWidth _ (meaningRow p x ∘ xorIndex a gate s) -
    atWidth _ (y ∘ xorIndex a gate s)‖ = _
  rw [atWidth_xorIndex a W s hl, atWidth_xorIndex a W s hl, ← map_sub, LinearIsometryEquiv.norm_map]
  rfl

theorem xor_numericalStep {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (child : Fin (a+1) → Shape → IdealRow → IdealRow) (s : Shape) (hl : 0 < s.level)
    (p : ℕ) (cap δ : ℝ) (hδ : 0 ≤ δ) (gate : Fin (a+1) × Fin (a+1)) :
    NumericalStep (nodeOps hW plan) (idealOps a W child) (nodeGuards hW plan)
      s (laneSize a W s) (laneGap a W p s) (.xor gate) 1 cap δ := by
  intro x y B e _ _ _ bank
  refine ⟨True.intro, fun _ => ?_⟩
  let yn : IdealRow := y 0
  let xn : Data s := x 0
  have b : laneSize a W s yn ≤ B ∧ laneGap a W p s xn yn ≤ e := bank 0
  constructor
  · exact ((laneSize_xor a W s hl gate yn).le.trans b.1).trans (by rw [one_mul])
  · exact ((laneGap_xor a W p s hl gate xn yn).le.trans b.2).trans
      (by rw [one_mul]; exact le_add_of_nonneg_right hδ)

end
end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
