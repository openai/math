import OAI.Computability.NearSquareRoot.PrecisionNodeAllowance
import OAI.Computability.NearSquareRoot.PrecisionPlanNode
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshUnlane

/-! # Transferring the recursive numerical guarantee to a child instruction

The exact transform on the child's selected coordinates is an isometry. Its
error on its own decoded input is charged once. Previously accumulated input
error passes through with gain one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace PhysicalWalshNode

open IntegerMultiplication KernelPass PhysicalWalsh PhysicalWalshGrid FlatWalshNode

def childIdeal (a W : ℕ) (axis : Fin (a+1)) (s : Shape) : IdealRow → IdealRow :=
  idealRow (a+1) (descend (a+1) W axis s)

def nodeValues (A frac : ℕ) (s : Shape) (x : Data s) := atWidth (count A s) (meaningRow frac x)

def nodeTarget (A frac : ℕ) (s : Shape) (x : Data s) := atWidth (count A s) (idealRow A s (meaningRow frac x))

/-- A whole child has a committed absolute rounding budget on its own decoded
input. The budget for intermediate row sizes is shared with its caller. -/
def NodeAccurate {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (frac : ℕ) (s : Shape)
    (R T err : ℝ) : Prop :=
  ∀ (x : Data s) (M : ℝ), ‖nodeValues (a+1) frac s x‖ ≤ M → R*(M+1) ≤ T →
    Good hW plan s x ∧ ‖nodeValues (a+1) frac s (run hW plan s x) - nodeTarget (a+1) frac s x‖ ≤ err

theorem child_numericalStep {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (s : Shape)
    (hs : 0 < s.level) (frac : ℕ) (axis : Fin (a+1)) {R T δ : ℝ}
    (hR : 0 < R) (hδ : 0 ≤ δ)
    (child : NodeAccurate hW plan frac (descend (a+1) W axis s) R T δ) :
    NumericalStep (nodeOps hW plan) (idealOps a W (childIdeal a W)) (nodeGuards hW plan) s
      (laneSize a W s) (laneGap a W frac s) (.child axis) 1 (T/R-1) δ := by
  intro x y B e _hB _he head ball
  let s' := descend (a+1) W axis s
  let x₀ : Data s' := x 0
  let y₀ : IdealRow := y 0
  have hn : count (a+1) s' = laneCount a W s := child_count s axis hs
  have size y' : ‖atWidth (count (a+1) s') y'‖ = ‖atWidth (laneCount a W s) y'‖ := by rw [hn]
  have dist x' y' : ‖atWidth (count (a+1) s') x' - atWidth (count (a+1) s') y'‖ =
      ‖atWidth (laneCount a W s) x' - atWidth (laneCount a W s) y'‖ := by rw [hn]
  have hm : ‖nodeValues (a+1) frac s' x₀‖ ≤ B+e := calc
    _ = ‖atWidth (laneCount a W s) (meaningRow frac x₀)‖ := size _
    _ ≤ _ := (norm_le_norm_sub_add _ (atWidth _ y₀)).trans <|
      (add_le_add (ball 0).2 (ball 0).1).trans_eq (add_comm ..)
  obtain ⟨good,rounding⟩ := child x₀ (B+e) hm (nextCap_child hR (by linarith))
  refine ⟨good,fun _ => ⟨?_,?_⟩⟩
  · change ‖atWidth (laneCount a W s) (idealRow (a+1) s' y₀)‖ ≤ 1*B
    calc
      _ = ‖atWidth (count (a+1) s') (idealRow (a+1) s' y₀)‖ := (size _).symm
      _ = ‖atWidth (count (a+1) s') y₀‖ :=
        (congrArg norm (idealRow_isometry (a+1) s' y₀)).trans ((nodeIsometry (a+1) s').norm_map _)
      _ ≤ 1*B := (size y₀).le.trans ((ball 0).1.trans_eq (one_mul B).symm)
  · change ‖atWidth (laneCount a W s) (meaningRow frac (run hW plan s' x₀)) -
      atWidth (laneCount a W s) (idealRow (a+1) s' y₀)‖ ≤ 1*(e+δ)
    apply (dist _ _).ge.trans
    apply (norm_sub_le_norm_sub_add_norm_sub _ (nodeTarget (a+1) frac s' x₀) _).trans
    have contract : ‖nodeTarget (a+1) frac s' x₀ -
        atWidth (count (a+1) s') (idealRow (a+1) s' y₀)‖ ≤ e :=
      (idealRow_distance (a+1) s' (meaningRow frac x₀) y₀).le.trans
        ((dist _ _).le.trans (ball 0).2)
    simpa only [s',nodeValues,one_mul,add_comm e δ] using add_le_add rounding contract

end PhysicalWalshNode

end

end NearSquareRoot
end Computability
end OAI
