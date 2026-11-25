import OAI.Hierarchy.DescentRotorOperandTicket
import OAI.Hierarchy.DescentInstalledRotorHeader

namespace OAI
/-! # A local rotor operand selects the actual installed receiver row -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n

def localPrivateOrdinal (u : Host) :=
  (private_local_chart B u).trans (localPrivateId r sz capacity)

local notation "configuredEdge" => fun (s : Bool) (g' : (placement).Good) =>
  DescentCommonPalette.rotorEdgeEquiv (Z).graph d
    (DescentChosenRouter.selectedRotorLayers placement (Z).graph (Z).positive (Z).pay (Z).circuit s g') C (Z).width (Z).unit

def goodOccurrence (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge) :
    PrivateOccurrence B := ⟨(s,.inl g₀),configuredEdge s g₀ e⟩

theorem good_ticket (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge) :
    localPrivateId r sz capacity (privateTicket B (goodOccurrence B s g₀ e))=
      candidate (Z).graph height r sz s ((Z).goodLabel T g₀) e := by
  exact congrArg (candidate (Z).graph height r sz s ((Z).goodLabel T g₀)) ((configuredEdge s g₀).symm_apply_apply e)

theorem actual_candidate (u : Host) (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge)
    (incident : (blocks B).src (privateWire B (goodOccurrence B s g₀ e))=u ∨ (blocks B).dst (privateWire B (goodOccurrence B s g₀ e))=u) :
    localPrivateOrdinal B u ⟨goodOccurrence B s g₀ e,incident⟩=
      candidate (Z).graph height r sz s ((Z).goodLabel T g₀) e := good_ticket B s g₀ e

/-- Validation against the wide installed geometry is confined to this proof. Each live operand
    issues the bounded candidate just above; the old input vertex code is absent from the request. -/
theorem actual_original (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge) :
    (ResetInput.installedResetOrdinal Z T vertexCode birth (privateWire B (goodOccurrence B s g₀ e))).val=
      DescentRotorPrivateFields.completePort (oldCap:=∑e,B.count e) (Z).graph placement height vertexCode s g₀ e := by
  exact congrArg Prod.fst ((Z).rotorArchive T vertexCode birth s g₀ e)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
