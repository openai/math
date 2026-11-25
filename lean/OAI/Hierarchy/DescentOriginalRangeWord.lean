import OAI.Hierarchy.DescentOriginalRangeRegister
import OAI.Hierarchy.DescentOriginalNodeCapacity
import OAI.Hierarchy.DescentArchiveCellReads

namespace OAI
/-! # Reading a retained node at the original physical date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentLocalArchiveOrder DescentSIMDLookup DescentRetainedRangeDigits DescentKernelHistory DescentColonies
open DescentOrdinaryAtomFieldRAM.ScalarOperand Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist)
    (B : BitDescription W) (localOrder : Local B) (room : RangeRoom ports r B)
    (population : Fintype.card r.V≤ports.operandHosts) (m : Memory w)

/-- The original compact host ordinal selects a physical archived group, before it enters the
ordinary operand gather. The finite site bound includes unused SIMD cells and unpaid sites. -/
def physicalRangeSource (j : ℕ) (f : Fin 3) (b : Block k) (h : Fin (Fintype.card r.V))
    (g : Fin (S.groupCount age)) : Cell (ports.operandBits*ports.nodes) :=
  previousRangeCell ports.archive ports.rangeLayout ports.operandBits m room.positive j f
    (b.cast (congrArg (2^·) room.radix)) (h.castLE population) (g.cast room.groups)

theorem physicalRangeSource_word (y : NodeOrder.All B) (j : ℕ) (f : Fin 3) :
    (rangeRegister ports r B localOrder room.capacity room.hosts room.groups room.radix room.positive m).word y j f=
      (take (((bounded B localOrder y.1).trans (Fin.castLEEmb (maxNodes_le B room.capacity))) y.2)
        (physicalRangeSource ports r B room population m j f (r.placement.block y.1)
          (r.vertex (r.placement.pos y.1).2) (r.placement.pos y.1).1)).val :=rfl

theorem rangeRegister_unallocated (y : NodeOrder.All B) (j : ℕ) (f : Fin 3) (past : ports.argumentsPerNode≤j) :
    (rangeRegister ports r B localOrder room.capacity room.hosts room.groups room.radix room.positive m).word y j f=0 :=by
  apply unallocated
  exact past

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
