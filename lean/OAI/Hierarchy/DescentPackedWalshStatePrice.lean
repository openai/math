import OAI.Hierarchy.DescentPackedWalshPhysicalBasis
import OAI.Hierarchy.DescentPackedWalshFullPrice
import OAI.Hierarchy.DescentGlobalControlBill

namespace OAI
/-! # The concrete two-transform, all-depth estimator pays once for each executed native pass -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentPackedWalshReduction DescentSIMDLookup DescentCompiler
noncomputable section
variable (E : EstimatorArena)
local notation "k" => E.dim
local notation "H" => E.hosts
local notation "h" => E.payload
local notation "b" => E.precision
local notation "P" => E.plan

def transformBill (K : ℕ) := K*((8*k+12)*h+(180*k+28)*(H*h+16*H*2^k*b))
def depthBill (W K : ℕ) := 4*W+94*(K*(H*h+16*H*2^k*b))+
  Plan.wordBill H k b W K+(4+2^k*60)*W

theorem depth_bill (W K : ℕ) (j : ℕ) (width : W≤K*h) (words : H≤2^W) (digits : b≤W+1)
    (fit : laneBits k h b=E.low) (room : 8*b≤h) :
    (E.shelf j).clock P H E.high*W≤E.depthBill W K := by
  have split : k-E.low=E.high := by unfold dim;omega
  have fields:=per_layer (m:=k) H E.positive room
  dsimp only at fields
  rw [fit,split] at fields
  have read : (H*2^E.high)*W≤ K*(H*h+16*H*2^k*b) := by
    calc
      _ ≤ (H*2^E.high)*(K*h) := Nat.mul_le_mul_left _ width
      _ = K*((H*2^E.high)*h) := by ring
      _ ≤ _ := Nat.mul_le_mul_left K fields
  have host : (E.plan.padTicks+E.plan.duration E.plan.depth)*W ≤ Plan.wordBill H k b W K :=
    E.plan.program_bill W K width words digits
  have localCost:=Column.clock (Column.banks E.orderAt k (E.plan.chunks E.plan.depth) (E.plan.bits+E.plan.depth)
    (E.plan.laneBits E.plan.depth) (Column.input P (E.scratch j))) (E.plan.laneBits E.plan.depth)
  have extract := Nat.mul_le_mul_right W (Nat.add_le_add_left (Nat.mul_le_mul_left (2^k) localCost) 4)
  unfold DepthShelf.clock Column.publishTime depthBill
  simp only [show E.plan.axis = E.dim from rfl, show (E.shelf j).extract = E.orderAt from rfl,
    show (E.shelf j).first = E.scratch j from rfl]
  simpa only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc] using
    Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 94 read) (4*W))
      (Nat.add_le_add host extract)

theorem clock_bill (W K : ℕ) (width : W≤K*h) (words : H≤2^W) (digits : b≤W+1)
    (fit : laneBits k h b=E.low) (room : 8*b≤h) :
    E.clock*W ≤ E.transformBill K + (4*W+(k+1)*E.depthBill W K) + 4000*2^(5*k)*W := by
  have slice (n : ℕ) : E.calendar.ticks P H n*W≤4*W+n*E.depthBill W K := by
    induction n with
    | zero=>simp [Calendar.ticks]
    | succ n ih=>
      change (E.calendar.ticks P H n+(E.shelf n).clock P H E.high)*W ≤
        4*W+n.succ*E.depthBill W K
      simpa only [Nat.add_mul, Nat.succ_mul, Nat.add_assoc] using
        Nat.add_le_add ih (E.depth_bill W K n width words digits fit room)
  have transform := numerator_price H k E.positive room width
  have split : k-E.low=E.high := by unfold dim;omega
  dsimp only at transform
  rw [fit,split] at transform
  have gl := Nat.mul_le_mul_right W (global_solver_clock k E.solveAt E.bank)
  unfold clock
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add transform (slice _)) gl

/-- Given the actual allocated last address, every depth bank precedes the solver. -/
theorem solver_room (w : ℕ) (last : DescentGL.PhysicalTrajectory.outputBase k E.solveAt+2^k<2^w) :
    DescentGL.PhysicalTrajectory.Room w k E.solveAt E.bank :=
  ⟨fun j=>E.includes_bank j.val j.isLt,last⟩

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
