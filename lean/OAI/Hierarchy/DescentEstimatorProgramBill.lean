import OAI.Hierarchy.DescentPackedWalshLedger
import OAI.Hierarchy.DescentEstimatorLiteralIssue
import OAI.Hierarchy.DescentPackedWalshStaticText
import OAI.Hierarchy.DescentGLPhysicalInvoice

namespace OAI
/-! # The whole estimator, including the literal-printing prelude and its original instruction text -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentPackedWalshReduction DescentCompiler DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (E : EstimatorArena)
local notation "k" => E.dim
local notation "N" => E.hosts
local notation "h" => E.payload
local notation "b" => E.precision
local notation "d" => E.plan.depth
def installedCPU (w : ℕ) := (E.header (w:=w)).program.seq (E.cpu w)
def installedTicks := 4+10*(E.staticEnd-E.origin)+E.clock
def controlNames := 116+366*k+(k+1)*(351+183*d)+8000*2^(5*k)

theorem cpu_names (w : ℕ) : CheapCode (E.cpu w) ∧ names (E.cpu w)≤E.controlNames := by
  obtain ⟨spectrum,body⟩:=spectrum_text E.transformAt E.start E.squareAt N E.high E.low b w
  obtain ⟨depths,table⟩:=calendar_text E.calendar E.plan w N (k+1)
  obtain ⟨solver,program,_⟩:=global_solver_hardware w k E.solveAt E.bank
  let first := numeratorCode E.transformAt E.start E.squareAt N E.high E.low b w
  let second := E.calendar.code E.plan w N (k+1)
  let third := DescentGL.PhysicalTrajectory.program w k E.solveAt E.bank
  refine ⟨@ProtocolRAM.cheap_seq w (first.seq second) third
    (@ProtocolRAM.cheap_seq w first second @spectrum @depths) @solver,?_⟩
  unfold cpu controlNames
  rw [names_seq,names_seq]
  change names _≤8000*2^(5*k) at program
  change names _≤97+366*k at body
  omega

/-- The incoming physical host may store seven words of original instruction text per native
machine name. Count all of them as well as every mounted word and the actual machine runtime. -/
theorem installed_price (w K : ℕ) (width : w≤K*h) (hosts : N≤2^w) (digits : b≤w+1)
    (lanes : laneBits k h b=E.low) (small : 8*b≤h/2) (gain : E.gainBits≤b) :
    CheapCode (E.installedCPU w) ∧
    (E.installedTicks+7*names (E.installedCPU w))*w ≤
      115*(N*h*hostUnit k K+N*2^k*fieldUnit k b K+E.commonBill w K)+(109+7*E.controlNames)*w := by
  obtain ⟨ca,na⟩:=(E.header (w:=w)).hardware
  obtain ⟨cb,nb⟩:=E.cpu_names w
  refine ⟨@ProtocolRAM.cheap_seq w (E.header (w:=w)).program (E.cpu w) @ca @cb,?_⟩
  have price:=E.priced_words w K width hosts digits lanes small gain
  unfold installedCPU installedTicks
  rw [names_seq,na]
  change (4+10*(E.staticEnd-E.origin)+E.clock+
    7*(15*(E.staticEnd-E.origin+1)+names (E.cpu w)))*w≤_
  have step : (4+10*(E.staticEnd-E.origin)+E.clock+
      7*(15*(E.staticEnd-E.origin+1)+names (E.cpu w)))*w≤
      115*((E.clock+(E.staticEnd-E.origin))*w)+(109+7*E.controlNames)*w := by
    nlinarith only [Nat.mul_le_mul_right w nb,Nat.zero_le (E.clock*w)]
  exact step.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 115 price) _)

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
