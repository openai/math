import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentBatchedReentry

namespace OAI
/-! # Installed ordered rotor coefficients with a bounded number of whole payload addresses -/
namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentResetGates
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p) (v : Z.bank.Site)

def laneShape : Shape p (Z.laneRecipe key m p hp fit v) := ofProgram
  (fun b=>boundaryWidth Z.bank v b/p) (Z.laneWidth_eq m p fit v) hp (Z.laneProgram key m p hp fit v)

theorem laneShape_stride (u j g) : ((Z.laneShape key m p hp fit v).chunk u j g).stride≤ max 1 (max Z.width (C*Z.width)) :=
  Z.lane_stride key m p hp fit v u j

theorem laneShape_headers : (Z.laneShape key m p hp fit v).headers*p ≤
    (max 1 (max Z.width (C*Z.width))+4)*max 2 ((2+2*h*C)*Z.width)*(2*DescentNetworkSubstitution.portLoad Z.bank v) := by
  let R:=max 1 (max Z.width (C*Z.width))+4
  let K:=max 2 ((2+2*h*C)*Z.width)
  calc
    _ ≤ R*(∑u,(Z.laneRecipe key m p hp fit v).nodeBits u) :=
      (Z.laneShape key m p hp fit v).headers_bound _ (Z.laneShape_stride key m p hp fit v)
    _ ≤ R*(∑_u : (Z.laneRecipe key m p hp fit v).Node,K*p) := Nat.mul_le_mul_left _ (Finset.sum_le_sum fun u _=>by
      change (∑_j : Fin (((Z.laneProgram key m p hp fit v).op u).arity),p)≤K*p
      simpa using Nat.mul_le_mul_right p (Z.lane_arity key m p hp fit v u))
    _ = (R*K)*(Fintype.card (Z.laneRecipe key m p hp fit v).Node*p) := by simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Z.lane_count_mul_le key m p hp fit v)
end
end Hierarchy.DescentSixParty.ResetInput

end OAI
