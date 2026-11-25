import OAI.Hierarchy.DescentTerminalRegisteredHeaderDigit
import OAI.Hierarchy.DescentArchiveOriginalSlot
import OAI.Hierarchy.DescentTerminalOperandSlotNumber
import OAI.Hierarchy.DescentRegisteredOperandFields

namespace OAI
/-! # The four registered pointer digits at a reached operand site -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)
local notation "Node" => NodeOrder.All B
local notation "L" => ports.rangeLayout

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "slot" => slotAt ports r B number room
local notation "arguments" y => occurrences (shape.sites (y:Node).1) y.2



open DescentTerminalPointerIssue DescentLocalPrivateNames DescentTerminalChronologicalBooks
open DescentPriorOperandColumns
variable {ports r B number room shape op label pointer flags}
variable {m : Memory w} (held : Hierarchy.DescentSixParty.Chronology.DatePorts.ArchiveRead
      ports r B number room shape op label pointer flags m)
    (hp : 0<p) (fmt : Widths) (capacity : fmt.nodeCapacity=some ports.nodes) (width : ∀f,fmt.pointer f=ports.operandBits)
    (packed : (ports.operandBits*ports.nodes)*ports.operandLanes≤w) (single : chunks ports.venue.groups ports.operandLanes=1)
    (v : W.graph.Site) {K d₀ : ℕ}
local notation "coord_" => Reached.NodeCells.coordinate r v
local notation "block_" => (coord_).2.2.cast (congrArg (2^·) room.radix)
local notation "host_" => (⟨(coord_).1.val,room.hosts v⟩ : Fin ports.operandHosts)
local notation "group_" => (coord_).2.1.cast room.groups
local notation "rawR" => (shape.sites v).recipe hp
local notation "birth_" => (number v).toEmbedding.trans Fin.valEmbedding

include held capacity width packed single in
/-- The four chronological header digits at the true home, low block and local
node. A singleton word per host lets the terminal use the original group index. -/
theorem ArchiveRead.header_at_original (u : (rawR).Node) (j : Fin ports.argumentsPerNode)
    (live : j.val<(rawR).arity u) (f : Fin 4) :
    fmt.nodeDigit (fmt.pointer f) (DescentTerminalPointerIssue.row rawR birth_ (room.capacity v) u).val
      (r.placement.pos v).1.val
      (m ((previousBank ports.rangeLayout ports.archive.arguments block_ (pageOf j f)).base+
        (Reached.NodeCells.coordinate r v).1.val)).val=(pointer ⟨v,u⟩ j.val).header f:=by
  have read:=ArchiveRead.terminal_header_digit (F:=F) (W:=W) (G:=G) held fmt capacity width room.positive packed block_
    ((number v u).castLE (room.capacity v)) j f host_ group_ (⟨v,u⟩ : NodeOrder.All B)
    (slotAt_original ports r B number room v u) (by
      rw [DescentRetainedRangeDigits.length _ _ hp]
      exact live)
  obtain ⟨addr,group⟩:=DescentTerminalPointerDigits.singleton_pitch single room.positive host_ group_
  rw [addr,group] at read
  have loc : (DescentTerminalPointerIssue.row rawR birth_ (room.capacity v) u).val=(number v u).val:=by
    let originalNode : (B.recipe v).Node := u
    change (ordinal birth_ originalNode).val=(number v originalNode).val
    exact (ordinal_val birth_ originalNode).trans (Reached.earlier_count (number v) originalNode)
  rw [loc]
  exact read

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
