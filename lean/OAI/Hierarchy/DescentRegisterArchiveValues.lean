import OAI.Hierarchy.DescentDatePortArchiveRead
import OAI.Hierarchy.DescentArchiveOriginalSlot

namespace OAI
/-! # Reading an original node's range at its genuine receiver coordinate -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)
local notation "coord" v:arg => Reached.NodeCells.coordinate r v
local notation "blockAt" v:arg => (coord v).2.2.cast (congrArg (2^·) room.radix)
local notation "hostAt" v:arg => (⟨(coord v).1.val,room.hosts v⟩:Fin ports.operandHosts)
local notation "groupAt" v:arg => (coord v).2.1.cast room.groups
local notation "slotAt_" v:arg u:arg => (number v u).castLE (room.capacity v)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (ptr : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
    (m : Memory w)
local notation "reg" => rangeRegister ports r B number room.capacity room.hosts room.groups room.radix room.positive m
variable (seen : ArchiveRead ports r B number room shape op label ptr flags m)
include seen in
theorem ArchiveRead.original_range (v : W.graph.Site) (u : (B.recipe v).Node) (j : Fin ports.argumentsPerNode)
    (f : Fin 3) (live : j.val<(occurrences (shape.sites v) u).length ∨ f=2)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w) :
    (reg).word ⟨v,u⟩ j.val f=atSlot (shape.sites v) u j.val f :=by
  obtain ⟨cells,read,digits⟩:=seen.spans (blockAt v) j f
  exact (range_word ports r B number room.capacity room.hosts room.groups room.radix room.positive m
    v u j f cells read width).trans (digits _ _ _ ⟨v,u⟩ (slotAt_original ports r B number room v u) live)

/-- Invert a physical hit before using the original range bank, including when the
padded host bound or the packed group indices differ in type. -/
theorem slotAt_coordinates (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes) (h : Fin ports.operandHosts)
    (g : Fin ports.venue.groups) (v : W.graph.Site) (u : (B.recipe v).Node)
    (hit : slotAt ports r B number room x n h g=some ⟨v,u⟩) :
    x=blockAt v ∧ n=slotAt_ v u ∧ h=hostAt v ∧ g=groupAt v :=by
  obtain ⟨host,group,block,node⟩:=(Reached.NodeCells.atPhysical_some r B number _ _ _ _ v u).1 hit
  exact ⟨Fin.ext (congrArg Fin.val block).symm,Fin.ext node,Fin.ext host.symm,Fin.ext (congrArg Fin.val group).symm⟩

theorem spans_of_range (x : Fin (2^ports.venue.k)) (j : Fin ports.argumentsPerNode) (f : Fin 3)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (cells : Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.operandBits*ports.nodes))
    (read : Reads (previousBank ports.rangeLayout ports.archive.arguments x
      (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) cells ports.operandLanes m)
    (values : ∀y : NodeOrder.All B,(j.val<(occurrences (shape.sites y.1) y.2).length ∨ f=2) →
      (reg).word y j.val f=atSlot (shape.sites y.1) y.2 j.val f)
    (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) (n : Fin ports.nodes) (y : NodeOrder.All B)
    (hit : slotAt ports r B number room x n h g=some y)
    (live : j.val<(occurrences (shape.sites y.1) y.2).length ∨ f=2) :
    ((encode ports.operandBits ports.nodes).symm (cells h g) n).val=atSlot (shape.sites y.1) y.2 j.val f :=by
  rcases y with ⟨v,u⟩
  obtain ⟨rfl,rfl,rfl,rfl⟩:=slotAt_coordinates ports r B number room _ _ _ _ v u hit
  exact (range_word ports r B number room.capacity room.hosts room.groups room.radix room.positive m
    v u j f cells read width).symm.trans (values ⟨v,u⟩ live)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
