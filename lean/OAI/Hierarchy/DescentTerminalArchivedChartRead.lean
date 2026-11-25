import OAI.Hierarchy.DescentTerminalArchivedSlices

namespace OAI
/-! # Reading the retained primitive, arity and affine operands after the archive prefix -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalSliceRuns DescentTerminalSliceShelf DescentTerminalPointerDigits
open scoped Classical Fin.CommRing
noncomputable section

/-- Any later input that agrees on the addresses of the selected archive row supplies
the same primitive token, bounded arity and live affine spans to the physical gather. -/
theorem ArchiveRead.slice_at_chart (ports : DatePorts)
    {F P : Type} [Field F] {D : ℕ} {size : P → ℕ} {W : MarkedWorld F D P size}
    {G : PoweredGadget F} {q ε : ℝ} {sched : AtomSchedule} {k age z degree wire hist w d : ℕ}
    (r : Reached W G q ε sched k age z degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B) {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B → Label G s Z op) (ptr : NodeOrder.All B → ℕ → Pointer)
    (flags : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ)
    (lastMem original : Memory w) (stored : ArchiveRead ports r B number room shape op label ptr flags lastMem)
    (pitch : ports.operandLanes = ports.venue.groups) (roles : ports.roleLanes = ports.venue.groups)
    (wide : physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits ≤ w)
    (covered : physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits ≤ d)
    {blocks hosts groups nodes limit : ℕ}
    (chart : Fin (Columns ports.argumentsPerNode) → Fin blocks → Gather.Address) (cfg : RawWidths)
    (hostD : hosts = ports.operandHosts) (nodeD : nodes = ports.nodes) (groupD : groups = ports.venue.groups)
    (widths : cfg = ⟨printedBits G s Z op, ports.operandBits, fun _ => ports.operandBits⟩)
    (x : Fin (2^ports.venue.k)) (block : Fin blocks) (shop : Fin hosts) (group : Fin groups) (slot : Fin nodes)
    (y : NodeOrder.All B) (hit : slotAt ports r B number room x (slot.cast nodeD) (shop.cast hostD) (group.cast groupD) = some y)
    (addresses : ∀ c, archiveSliceChart ports c x = chart c block)
    (earlier : ∀ c, (chart c block).Fits limit hosts w) (frame : ∀ a < limit, original a = lastMem a) :
    let raw := extract cfg (seen (d:=d) chart original block shop) group slot
    let used := occurrences (shape.sites y.1) y.2
    raw.token = (token G s Z op (label y)).val ∧ raw.live = (used.length : Cell ports.operandBits).val ∧
      ∀ (j : Fin ports.argumentsPerNode) (f : Fin 3), j.val < used.length ∨ f = 2 →
        value (raw.header j) f = atSlot (shape.sites y.1) y.2 j.val f := by
  subst hosts
  subst nodes
  subst groups
  subst cfg
  have same : seen (d:=d) chart original block shop = seen (d:=d) (archiveSliceChart ports) lastMem x shop := by
    funext c
    change ((original ((chart c block).atHost shop)).val : Cell d) =
      ((lastMem ((archiveSliceChart ports c x).atHost shop)).val : Cell d)
    rw [addresses c, frame _ ((chart c block).below (earlier c) shop)]
  dsimp only
  rw [same]
  exact ArchiveRead.slice_at (d:=d) ports r B number room shape op label ptr flags lastMem
    stored pitch roles wide covered x shop group slot y hit

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
