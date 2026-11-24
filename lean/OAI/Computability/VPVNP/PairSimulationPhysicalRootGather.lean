import OAI.Computability.VPVNP.PairSimulationPhysicalScanData
import OAI.Computability.VPVNP.PairTerminalGatherNative
import OAI.Computability.VPVNP.PairTerminalGatherReadSafety

/-!
# Gathering the chosen terminal payload into the private root packet

The three incidence directories precede the shared-bit bank. The completed
physical bit phase preserves those rows and writes each bit once. Its outgoing
and incoming gathers use that same bank, with the inverse directory selecting
the source of each incoming slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PhysicalScanData

open BurstRAM PrivateRAM Compression CompressorRecords LocalHistory TerminalLink
open TerminalGatherGeometry TerminalRootGather
open scoped Fin.CommRing

open private incidence_end_le from OAI.Computability.VPVNP.CompressorDescriptorSpace

/-- On the selected descriptor layout the inverse and width columns are
packed at columns 4 and 5 of the last level. Its prefix table also ends
before the final wire bank, even when that level has no arcs. -/
theorem packed_heads (D : DescriptorSpace.Layout) (last : Fin D.levels)
    (tab : Fin D.shape.tables) (L : Layout) (n : ℕ) (slots : n ≤ DescriptorSpace.slotCapacity D)
    (cells : n ≤ DescriptorSpace.tableWords D)
    (inverse : L.incomingHead = DescriptorSpace.incidenceBase D last n 4)
    (widths : L.widthHead = DescriptorSpace.incidenceBase D last n 5)
    (starts : L.prefixHead = DescriptorSpace.tableBase D last tab)
    (wireBase : DescriptorSpace.endAddress D ≤ L.wires) :
    ∀ h ∈ [L.incomingHead, L.widthHead, L.prefixHead], h + n ≤ L.wires := by
  have next := (DescriptorSpace.levelStart_mono D last.isLt).trans wireBase
  have array := (incidence_end_le D last).trans next
  have prefixEnd := (DescriptorSpace.tableEnd_le_nextLevel D last tab).trans next
  have bound := Nat.mul_le_mul_left 6 slots
  change DescriptorSpace.incidenceStart D last + 6 * DescriptorSpace.slotCapacity D ≤ _ at array
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · rw [inverse]
    change DescriptorSpace.incidenceStart D last + 4 * n + n ≤ _
    omega
  · rw [widths]
    change DescriptorSpace.incidenceStart D last + 5 * n + n ≤ _
    omega
  · rw [starts]
    omega

variable {a g w p r k : ℕ} (X : State a g)
  (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0)
  (low : ℕ) (pub : M.publicData base = FinalBits.cursor w low 0) (m : Memory w) (extra : ℕ)
  (fit : low + X.totalWidth < 2 ^ w)

local notation "scan" => stateScanPhase X M pc reg base done hl he low pub m extra fit
local notation "bits" => assignment X M pc reg base done hl he low pub m extra fit

variable {width : ℕ} (F : DescriptorSpace.Shape) (limit : ℕ)
  (S : VertexImage.Part → VertexImage.Segment) (ops : Fin 11 → Word width) (cap : ℕ)
  {input : Memory width} (q : QuietPrefix (TerminalProgram.workers F limit S) ops cap input)
  (src : Memory width) (L : Layout) (layout : FinalBits.Worker.Layout ops src L.wires X.totalWidth)
  (clock : 54 ≤ cap) (room : (header ops).val + 32 ≤ 2 ^ width)
  (below : L.wires + X.totalWidth ≤ (header ops).val)
  (agree : SourceTransport.Agree (workerCell (header ops)) src q.traversalRows.val.memory)

local notation "bank" => physical X M pc reg base done hl he low pub m extra fit F limit S
  ops cap src q.traversalRows.val.memory L.wires layout clock room below agree

/-- The fourth block of this quiet prefix is indexed by the nomination's data path. -/
noncomputable def bitPaths : (scan).Path ≃ q.BitPaths := bank

variable (valid : (Entry.resume Stage.sharedBits (0 : Word width)).Valid
  (header ops) q.traversalRows.val.memory)

local notation "arrayBits" => fun x i =>
  bits x (Fin.cast (TerminalPrefix.width_sum X) i)

include valid in
private theorem bank_read (x : (scan).Path) (i : Fin (∑ j, TerminalPrefix.width X j)) :
    (bank x).val.memory (L.wires + i.val) = PrivateFields.bitValue width (arrayBits x i) :=
  SharedBitPhase.readback F limit S ops cap src _ layout clock room below agree valid _
    (Fin.cast (TerminalPrefix.width_sum X) i)

variable (rows : Rows X L src)
  (heads : ∀ h ∈ [L.incomingHead, L.widthHead, L.prefixHead],
    h + TerminalPrefix.arcCount X ≤ L.wires)

include valid rows heads

/-- All three gathered directories keep their source entries through the linked shared-bit phase. -/
theorem rows_after_bits (x : (scan).Path) : Rows X L (bank x).val.memory := by
  apply rows.transfer
  intro h hh i
  have head := heads h hh
  have hi := i.isLt
  have lt : h + i.val < L.wires := by omega
  have h31 : (header ops + 31).val = (header ops).val + 31 := by
    rw [Fin.val_add]
    change ((header ops).val + 31 % (2 ^ width)) % (2 ^ width) = _
    rw [Nat.mod_eq_of_lt (by omega : 31 < 2 ^ width), Nat.mod_eq_of_lt (by omega)]
  have data : workerCell (header ops) (h + i.val) := ⟨by omega, by omega⟩
  have image := SharedBitPhase.memory_image F limit S ops cap src _ layout clock room below
    agree valid (bits x)
  exact (image _ data).symm.trans (FinalBits.outside L.wires layout.fits _ src _ (.inl lt))

variable {v : X.network.Site} (num : Numbering X L v)

include num

local notation "argument(" x ")" => NodeArguments.packed X v
  (WireTensor.edgeAssignment X.network.src X.network.dst (ScanPhase.payload scan x) v)

/-- The root packet includes both endpoint slots of a loop, as well as
every slot of parallel arcs and every empty field of a zero-width arc. -/
theorem packet (x : (scan).Path) : L.packet (bank x).val.memory =
    (argument(x)).map (PrivateFields.bitValue width) := by
  have rr := rows_after_bits X M pc reg base done hl he low pub m extra fit F limit S
    ops cap q src L layout clock room below agree valid rows heads x
  have read := bank_read X M pc reg base done hl he low pub m extra fit F limit S
    ops cap q src L layout clock room below agree valid x
  rw [payload X M pc reg base done hl he low pub m extra fit x]
  exact packet_eq num rr (arrayBits x) read

/-- The linked root-gather instruction sequence installs the nomination's
argument in the private store and reaches the DFS continuation. -/
theorem native_root_reads {P T : ℕ} {host : Machine width P T 11} {labels : PC → Fin P}
    {regs : Reg ↪ Fin T} {exit : Fin P} (code : Linked host labels regs exit)
    (destFit : L.dest + TerminalGatherNative.argumentSize X v < 2 ^ width)
    (x : (scan).Path) (c : Config width P T) (hc : c.pc = labels (.boot 0))
    (saved : Saved L regs c) (hn : host.publicData 6 = (L.n : Word width))
    (stride : c.privateMem (c.privateMem (L.n : Word width) + 7) = (L.stride : Word width)) :
    ∃ out es, out.pc = exit ∧ Frame regs c out ∧
      out.privateMem = PrivateFields.storeBits L.dest argument(x) c.privateMem ∧
      Cost es (15 + 21 * 2 ^ a + 5 * TerminalGatherNative.argumentSize X v)
        (5 * 2 ^ a + TerminalGatherNative.argumentSize X v) ∧
      SourceTransport.Reads (workerCell (header ops)) es ∧
      Prefix host (bank x).val.memory c es out := by
  have rr := rows_after_bits X M pc reg base done hl he low pub m extra fit F limit S
    ops cap q src L layout clock room below agree valid rows heads x
  have read := bank_read X M pc reg base done hl he low pub m extra fit F limit S
    ops cap q src L layout clock room below agree valid x
  have bound := layout.fits
  have countFit : TerminalPrefix.arcCount X < 2 ^ width := by
    have h := heads L.widthHead (by simp)
    omega
  have enough := fits num rr (arrayBits x) read countFit
    (fun h hh => (heads h hh).trans (by omega)) bound destFit
  have allowed := worker_readable num rr (header ops) (by omega)
    (fun h hh => (heads h hh).trans (by omega)) below
  obtain ⟨out, es, ret, frame, image, cost, reads, run⟩ :=
    TerminalRootGather.run_reads code L _ enough c hc saved hn stride _ allowed
  rw [payload X M pc reg base done hl he low pub m extra fit x]
  refine ⟨out, es, ret, frame, image.trans (placed_packet num rr _ read enough _), ?_, reads, run⟩
  simpa only [num.degree, packet_eq num rr _ read, List.length_map, NodeArguments.packed_length,
    TerminalGatherNative.argumentSize] using cost

/-- Private memory and the remaining branch stream at the root DFS continuation. -/
theorem native_root {P T : ℕ} {host : Machine width P T 11} {labels : PC → Fin P}
    {regs : Reg ↪ Fin T} {exit : Fin P} (code : Linked host labels regs exit)
    (destFit : L.dest + TerminalGatherNative.argumentSize X v < 2 ^ width)
    (x : (scan).Path) (c : Config width P T) (hc : c.pc = labels (.boot 0))
    (saved : Saved L regs c) (hn : host.publicData 6 = (L.n : Word width))
    (stride : c.privateMem (c.privateMem (L.n : Word width) + 7) = (L.stride : Word width)) :
    ∃ out es, out.pc = exit ∧ Frame regs c out ∧
      out.privateMem = PrivateFields.storeBits L.dest argument(x) c.privateMem ∧
      Cost es (15 + 21 * 2 ^ a + 5 * TerminalGatherNative.argumentSize X v)
        (5 * 2 ^ a + TerminalGatherNative.argumentSize X v) ∧
      Prefix host (bank x).val.memory c es out := by
  obtain ⟨out, es, ret, frame, image, cost, _, run⟩ :=
    native_root_reads X M pc reg base done hl he low pub m extra fit F limit S ops cap q src L
      layout clock room below agree valid rows heads num code destFit x c hc saved hn stride
  exact ⟨out, es, ret, frame, image, cost, run⟩

end PairSimulation.PhysicalScanData

end VPVNP
end Computability
end OAI
