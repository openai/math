import OAI.Hierarchy.DescentArchiveCellRead

namespace OAI
/-! Four pointer fields of the original chronological archive at each actual operand. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

variable {p R : ℕ} (shape : WorldShape p R B) (pointer : NodeOrder.All B → ℕ→Pointer)
def HeaderRows (m:Memory w) : Prop := ∀(x : Fin (2^ports.venue.k)) (j : Fin ports.argumentsPerNode) (f : Fin 4),
      ∃cells : (Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits*ports.nodes)),
        Reads (previousBank ports.rangeLayout ports.archive.arguments x
        (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j)) cells ports.operandLanes m ∧
        ∀h g n (y : NodeOrder.All B),slotAt ports r B number room x n h g=some y → j.val<(occurrences (shape.sites y.1) y.2).length →
          ((encode ports.operandBits ports.nodes).symm (cells h g) n).val = (pointer y j.val).header f

theorem ArchiveRead.headerRows {s Z : ℕ} {op : RotorSpec} {label : NodeOrder.All B → Label G s Z op}
    {flags : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ}
    {m : Memory w} (stored : ports.ArchiveRead r B number room shape op label pointer flags m) :
    HeaderRows ports r B number room shape pointer m :=
  stored.headers


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
