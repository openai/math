import OAI.Hierarchy.DescentArchiveCellRead

namespace OAI
/-! # Finding an original vertex at its attained receiver coordinate -/
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
local notation "coord" v => Reached.NodeCells.coordinate r v
local notation "blockAt" v => (coord v).2.2.cast (congrArg (2^·) room.radix)
local notation "hostAt" v => (⟨(coord v).1.val,room.hosts v⟩:Fin ports.operandHosts)
local notation "groupAt" v => (coord v).2.1.cast room.groups
local notation "slotAt_" v:arg u:arg => (number v u).castLE (room.capacity v)
theorem slotAt_original (v : W.graph.Site) (u : (B.recipe v).Node) :
    slotAt ports r B number room (blockAt v) (slotAt_ v u) (hostAt v) (groupAt v)=some ⟨v,u⟩ :=by
  apply (Reached.NodeCells.atPhysical_some r B number _ _ _ _ v u).2
  refine ⟨rfl,Fin.ext rfl,Fin.ext rfl,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
