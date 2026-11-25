import OAI.Hierarchy.DescentCalendarNodeWidths
import OAI.Hierarchy.DescentBundleBank
import OAI.Hierarchy.DescentBundleNodeCapacity
import OAI.Hierarchy.DescentRetainedRangeWidth
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! The funded argument strip and its range digits at an installed reset gate. -/
namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentDatedAddressBook
open DescentRetainedRangeDigits
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit)
local notation "key" => DescentOrderedReset.grains W B.count B.order
local notation "m" => B.reset.unit/p
local notation "fit" => Eq.symm (Nat.div_mul_cancel whole)
local notation "prog" => B.reset.laneProgram key m p hp fit
local notation "plan" => B.reset.laneShape key m p hp fit
variable (drift degree payload e prev M nextM : ℕ) (old : ResetOutput.Prior) (base : ℕ)
local notation "out" => ResetOutput.fromBoard G S ctl.board k tail i p f g drift degree payload e prev M nextM C ctl.bitsR old base

/-- The genuine reset date has positive height. Its scheduled rotor arity already
fits the unflattened argument allowance before accounting for lane stride. -/
private theorem gate_calendar :
    max 2 ((2+2*h*C)*B.reset.width)≤S.retainedArguments G :=by
  have ht : 0<S.height:=by
    by_contra! ended
    have empty:S.height=0:=by omega
    simpa [DescentCompiler.AtomSchedule.length,empty] using B.age
  have exponent : S.capGain≤operandExponent G S:=by unfold operandExponent;omega
  rw [B.width]
  apply ctl.gate_arity.trans
  change 2^S.capGain≤(2^S.height)^(operandExponent G S)
  rw [←pow_mul]
  exact Nat.pow_le_pow_right (by decide)
    (exponent.trans (Nat.le_mul_of_pos_left _ ht))

/-- Full flattened argument count for every actual bank birth, including the
case in which an affine lane intersects more than one aligned word. -/
theorem fresh_calendar_arguments (wide : max 1 (max B.reset.width (C*B.reset.width))≤drift)
    (v : B.reset.bank.Site) (t : ((prog) v).Node) :
    (((plan) v).recipe hp).arity t≤S.retainedArgumentsAt G drift:=by
  apply ((plan) v).node_keys_le hp t drift (S.retainedArguments G)
    (fun j g=>(B.reset.laneShape_stride key m p hp fit v t j g).trans wide)
  change (∑ _ : Fin ((((prog) v).op t).arity),p) ≤ p*S.retainedArguments G
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left p ((B.reset.lane_arity key m p hp fit v t).trans (gate_calendar B))

theorem fresh_argument_room (wide : max 1 (max B.reset.width (C*B.reset.width))≤drift)
    (v : B.reset.bank.Site) (t : ((prog) v).Node) :
    (((plan) v).recipe hp).arity t≤(out).birth.arguments:=fresh_calendar_arguments B hp whole drift wide v t

/-- Each of the three range digits fits both the primitive span input and the
shared operand lookup field, including unused argument slots. -/
theorem fresh_range_room (wide : max 1 (max B.reset.width (C*B.reset.width))≤drift)
    (v : B.reset.bank.Site) (t : ((prog) v).Node) (j : ℕ) (field : Fin 3) :
    atSlot ((plan) v) t j field<2^(out).birth.spanBits ∧
    atSlot ((plan) v) t j field<2^(out).setup.fieldBits:=by
  have small:=atSlot_fits G S ((plan) v) t k tail drift degree
    (fun a g=>(B.reset.laneShape_stride key m p hp fit v t a g).trans wide) j field
  exact ⟨small,small.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_max_left ..))⟩

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
