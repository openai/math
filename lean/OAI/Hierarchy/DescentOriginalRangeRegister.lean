import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentRangeRegisterCore

namespace OAI
/-! # Reading the original retained operand through its actual public address register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentSIMDLookup DescentColonies
open DescentRetainedRangeDigits DescentDatedPriorOperand DescentPackedColony DescentOperandStateBanks
open Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist)
    (B : BitDescription W) (localOrder : ∀v,(B.recipe v).Node≃Fin (Fintype.card (B.recipe v).Node))
    (capacity : ∀v,Fintype.card (B.recipe v).Node≤ports.nodes)
    (hosts : ∀v,(Reached.NodeCells.coordinate r v).1.val<ports.operandHosts) (groups : S.groupCount age=ports.venue.groups)
    (radix : k=ports.venue.k) (pos : 0<ports.operandLanes) (m : Memory w)

local notation "coords" v => Reached.NodeCells.coordinate r v
local notation "blocksAt" => fun x : NodeOrder.All B=>(coords x.1).2.2.cast (congrArg (2^·) radix)
local notation "hostsAt" => fun x : NodeOrder.All B=>(⟨(coords x.1).1.val,hosts x.1⟩:Fin ports.operandHosts)
local notation "groupsAt" => fun x : NodeOrder.All B=>(coords x.1).2.1.cast groups
local notation "slots" => fun x : NodeOrder.All B=>(localOrder x.1 x.2).castLE (capacity x.1)
local notation "l" => ports.rangeLayout

/-- All four coordinates come directly from the occupants' registered placement. -/
def rangeRegister : Register B :=
  fromRAM ports.archive l ports.operandBits m pos blocksAt hostsAt groupsAt slots

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
