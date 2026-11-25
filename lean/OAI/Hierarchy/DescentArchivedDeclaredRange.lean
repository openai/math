import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
/-! # Original interval words including slots beyond the allocated operand capacity -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w p R s Z : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {ptr : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w} (seen : ArchiveRead ports r B number room shape op label ptr flags m)
include seen in
theorem ArchiveRead.all_range_words
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (slots : ∀y : NodeOrder.All B,(occurrences (shape.sites y.1) y.2).length≤ports.argumentsPerNode)
    (y : NodeOrder.All B) (j : ℕ) (f : Fin 3) (need : j<(occurrences (shape.sites y.1) y.2).length ∨ f=2) :
    (rangeRegister ports r B number room.capacity room.hosts room.groups room.radix room.positive m).word y j f=
      atSlot (shape.sites y.1) y.2 j f:=by
  by_cases allocated : j<ports.argumentsPerNode
  · exact ArchiveRead.original_range ports r B number room shape op label ptr flags m seen y.1 y.2 ⟨j,allocated⟩ f need width
  · have past:ports.argumentsPerNode≤j:=Nat.le_of_not_lt allocated
    have absent:= (slots y).trans past
    rw [←layout] at absent
    rw [atSlot_padding _ _ _ _ absent]
    exact unallocated _ _ _ _ _ _ _ _ _ _ _ _ past
end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
