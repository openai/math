import OAI.Hierarchy.DescentClosedFreshKinds
import OAI.Hierarchy.DescentResetOriginRank
import OAI.Hierarchy.DescentInstalledRoleCases

namespace OAI
/-! # Device identity, numbered original gate and public role at the reached reset node -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentPrimitivePalette DescentChosenRouter Chronology Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit) (a : Archive W)

local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "prog" => B.reset.laneProgram birth unit p hp splitEq
local notation "bitsAt" => B.reset.laneRecipe birth unit p hp splitEq
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "place" => B.reset.placement
local notation "choice" => selected place B.reset.graph B.reset.positive B.reset.pay B.reset.circuit
local notation "role_" => DescentBatchedBank.InstalledRole B.reset.graph B.reset.positive
  B.reset.unit unit (place).contact (place).input (place).site (place).owner (place).align d

/-- The actual ordinal after renaming identifies a gate in one of the two installed
devices. The same gate has the public tag and arity dictated by its device. -/
theorem closed_fresh_original (earlier : Local a.bit) (x : NodeOrder.All next_)
    (v : B.reset.bank.Site) (u : (prog v).Node)
    (origin : resetOrigin B hp whole a x=.inr (.inr ⟨v,u⟩)) :
    let number:=(DescentLocalArchiveOrder.reset B p hp whole a earlier x.1 x.2).val
    B.reset.MountedAt birth unit p hp splitEq ⟨v,u⟩ number ∧
      role_ v.1.1 v.1.2 (choice v.1.1 v.1.2) v.2 number
        (((prog v).op u).arity) ((bitsAt v).tag u) :=by
  intro number
  have rn:=reached_node_rank B hp whole a earlier x
  rw [origin] at rn
  change number=B.reset.nodeIndex birth unit p hp splitEq v u at rn
  rw [rn]
  exact ⟨B.reset.closed_fresh_kinds birth unit p hp splitEq v u,
    B.reset.bank_role_cases birth unit p hp splitEq v u⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
