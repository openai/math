import OAI.Hierarchy.DescentDatePortArchiveRead
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentOrdinaryMountedBirth

namespace OAI
/-! Earlier numerical input words of an ordinary date, taken directly from the single archived register. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}


open DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

/-- View the previous seven operand and primitive banks at the same signed RAM
state, with exactly the block/width enumerations used by `ordinary_role_inputs`. -/
theorem ArchiveRead.ordinary_input_pages (stored : ArchiveRead ports r B number room shape op label pointer flags m)
    {X : ℕ} (blocks : X=2^ports.venue.k) (width : 2≤ports.operandBits) :
    let L:=ports.argumentLayout X
    (∃old : DescentOperandStateBanks.Pages L.operands→Fin L.blocks→Fin L.hosts→Fin L.groups→
      Cell (DescentOrdinaryPriorRetile.digits L),
      ∀x j,Reads (previousBank L ports.archive.arguments x j) (old j x) L.lanes m) ∧
    ∀x : Fin X,Reads (ports.archive.roles.bank x.val)
      (fun h g=>encode (printedBits G s Z op) ports.nodes (fun j=>
        (slotAt ports r B number room (x.cast blocks) j h g).elim 0 (fun y=>token G s Z op (label y)))) ports.roleLanes m:=by
  subst X
  intro L
  constructor
  · choose data read using stored.operands
    have bits : ports.operandBits*ports.nodes=DescentOrdinaryPriorRetile.digits L:=by
      change _=(ports.operandBits-2+2)*ports.nodes
      rw [Nat.sub_add_cancel width]
    refine ⟨fun j x=>rowsAt rfl rfl bits (data x j),?_⟩
    intro x j
    exact reads_at rfl rfl bits rfl (read x j)
  · intro x
    exact stored.primitive x

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
