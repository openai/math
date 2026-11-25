import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentTerminalSliceWordRead

namespace OAI
/-! The terminal slice reader on an occupied slot of the actual archived register. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalSliceRuns DescentTerminalSliceShelf DescentTerminalPointerDigits
open scoped Classical Fin.CommRing
noncomputable section
variable (ports : DatePorts)

def archiveSliceChart (c : Fin (Columns ports.argumentsPerNode)) (x : Fin (2^ports.venue.k)) : Gather.Address :=
  .hosts (Sum.elim (fun (j : Fin 2)=>if j.val=0 then ports.archive.roles.bank x.val else metadataPage ports 1 x)
    (fun (z : Fin (3*ports.argumentsPerNode))=>let e : Fin 3×Fin ports.argumentsPerNode:=finProdFinEquiv.symm z
      previousBank ports.rangeLayout ports.archive.arguments x
        (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page e.1) e.2))
    (finSumFinEquiv.symm c))

@[simp] theorem archive_leading_token (x : Fin (2^ports.venue.k)) :
    archiveSliceChart ports (leading 0) x=.hosts (ports.archive.roles.bank x.val) :=by
  simp [archiveSliceChart,leading]

@[simp] theorem archive_leading_count (x : Fin (2^ports.venue.k)) :
    archiveSliceChart ports (leading 1) x=.hosts (metadataPage ports 1 x) :=by
  simp [archiveSliceChart,leading]

@[simp] theorem archive_triple (f : Fin 3) (j : Fin ports.argumentsPerNode) (x : Fin (2^ports.venue.k)) :
    archiveSliceChart ports (triple f j) x=.hosts (previousBank ports.rangeLayout ports.archive.arguments x
      (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) :=by
  simp only [archiveSliceChart,triple,Equiv.symm_apply_apply,Sum.elim_inr]

variable {F P : Type} [Field F] {D : ℕ} {size : P→ℕ} {W : MarkedWorld F D P size}
  {G : PoweredGadget F} {q ε : ℝ} {sched : AtomSchedule} {k age grain degree wire hist w d : ℕ}
  (r : Reached W G q ε sched k age grain degree wire hist) (B : BitDescription W)
  (number : Local B) (room : RangeRoom ports r B) {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
  (label : NodeOrder.All B→Label G s Z op) (ptr : NodeOrder.All B→ℕ→Pointer)
  (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
  (m : Memory w) (stored : ArchiveRead ports r B number room shape op label ptr flags m)
variable (pitch : ports.operandLanes=ports.venue.groups) (roles : ports.roleLanes=ports.venue.groups)
  (wide : (physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits)≤w) (covered : (physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits)≤d)
  (x : Fin (2^ports.venue.k)) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) (n : Fin ports.nodes) (y : NodeOrder.All B)
  (hit : slotAt ports r B number room x n h g=some y)

include stored hit pitch roles wide covered in
/-- The same physical row gives the actual primitive label, live operand count, and each
recorded affine coordinate. A zero-count padding digit also has its recorded value. -/
theorem ArchiveRead.slice_at :
    let widths : RawWidths := ⟨printedBits G s Z op,ports.operandBits,fun _=>ports.operandBits⟩
    let raw := extract widths (seen (d:=d) (archiveSliceChart ports) m x h) g n
    let used := occurrences (shape.sites y.1) y.2
    (raw).token=(token G s Z op (label y)).val ∧ (raw).live=((used).length : Cell ports.operandBits).val ∧
    ∀(j : Fin ports.argumentsPerNode) (f : Fin 3),j.val<(used).length ∨ f=2 →
      value ((raw).header j) f=atSlot (shape.sites y.1) y.2 j.val f := by
  dsimp only
  have fits {bits : ℕ} (small : bits≤ max (printedBits G s Z op) ports.operandBits) : bits*ports.nodes*ports.venue.groups≤(physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits) :=by
    simpa [physicalWidth,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_right (ports.nodes*ports.venue.groups) small
  have low:=fits (Nat.le_max_left (printedBits G s Z op) ports.operandBits)
  have high:=fits (Nat.le_max_right (printedBits G s Z op) ports.operandBits)
  constructor
  · have src:=stored.primitive x
    rw [roles] at src
    have read:=stored_lane _ _ m src (low.trans wide) (low.trans covered) h g n
    simpa [extract,seen,Gather.Address.atHost,hit] using read
  constructor
  · have src:=stored.arity x
    rw [pitch] at src
    have read:=stored_lane _ _ m src (high.trans wide) (high.trans covered) h g n
    simpa [extract,seen,Gather.Address.atHost,hit] using read
  · intro j f need
    obtain ⟨cells,src,truth⟩:=stored.spans x j f
    rw [pitch] at src
    have read:=stored_lane _ _ m src (high.trans wide) (high.trans covered) h g n
    have eqn:=read.trans (truth h g n y hit need)
    fin_cases f <;> simpa [value,extract,seen,Gather.Address.atHost] using eqn

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
