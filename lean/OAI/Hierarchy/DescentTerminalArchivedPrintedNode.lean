import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentTerminalArchivedChartRead
import OAI.Hierarchy.DescentTerminalPrintedNode

namespace OAI
/-! The six native role fields read from an occupied slot in the original archive. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentOperandStateBanks DescentPrimitivePalette DescentSIMDLookup
open DescentTerminalSliceRuns DescentTerminalSliceShelf DescentTerminalCombinedRole DescentTerminalPointerDigits
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (ports : DatePorts) {F P : Type} [Field F] {D : ℕ} {size : P → ℕ} {W : MarkedWorld F D P size}
    {G : PoweredGadget F} {q ε : ℝ} {sched : AtomSchedule} {k age grain degree wire hist bw d : ℕ}
    (r : Reached W G q ε sched k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B) {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B → Label G s Z op) (ptr : NodeOrder.All B → ℕ → Pointer)
    (flags : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ)
    (previous original acquired : Memory bw)
    (stored : ArchiveRead ports r B number room shape op label ptr flags previous)
variable {blocks hosts groups nodes limit : ℕ}
    (chart : Fin (Columns ports.argumentsPerNode) → Fin blocks → Gather.Address)
    (cfg : RawWidths) (a capacity start advice : ℕ)
    (x : Fin (2^ports.venue.k)) (block : Fin blocks) (shop : Fin hosts)
    (group : Fin groups) (slot : Fin nodes) (y : NodeOrder.All B)

local notation "paletteCodec" => DescentPrimitivePalette.codec (G:=G) (s:=s) (Z:=Z) op
local notation "colors_" => DescentPrimitivePalette.colors G s Z op
local notation "widths" => fun f : Fin 6 => DescentTerminalCombinedRole.width colors_ a capacity p R f * nodes * groups
local notation "bankCount" => Columns ports.argumentsPerNode
local notation "rawBanks" => fun f : Fin 6 => DescentTerminalSliceShelf.field start bankCount d (blocks*hosts) (Fin.val f)
local notation "roleTable" => DescentTerminalRoleTables.role widths rawBanks advice
local notation "emitter" => writePanel (d:=d) (M:=ports.argumentsPerNode) (s:=s) (Z:=Z) (N:=nodes) (groups:=groups) G op a capacity p R cfg
local notation "outputMemory" => DescentTerminalSliceShelf.memory start chart emitter hosts original
local notation "finish" => DescentTerminalSliceShelf.fence start bankCount d (blocks*hosts)
local notation "inputAt" => extract cfg (seen (d:=d) chart original block shop) group slot
local notation "viewAt" => observed (n:=colors_) (A:=a) (G:=capacity) (p:=p) (R:=R) (N:=nodes) (M:=groups)
  roleTable acquired (Fin.val (finProdFinEquiv (block,shop)) : Computability.VPVNP.BurstRAM.Word bw)
local notation "operandRows" => Shape.sliceFields (shape.sites (Sigma.fst y)) (Sigma.snd y)
local notation "operandWords" => repeatFields (List.flatten operandRows)

include stored in
/-- A slot identified in the archive supplies its primitive word, live count and all three
affine coordinates at each used operand. The native writer reads the same addresses and
the subsequent prefix preserves its six output banks. -/
theorem ArchiveRead.printed_at_original
    (hostD : hosts = ports.operandHosts) (nodeD : nodes = ports.nodes) (groupD : groups = ports.venue.groups)
    (widthD : cfg = ⟨printedBits G s Z op,ports.operandBits,fun _ => ports.operandBits⟩)
    (pitch : ports.operandLanes = ports.venue.groups) (roles : ports.roleLanes = ports.venue.groups)
    (wide : physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits ≤ bw)
    (covered : physicalWidth ports.venue.groups ports.nodes (printedBits G s Z op) ports.operandBits ≤ d)
    (hit : slotAt ports r B number room x (slot.cast nodeD) (shop.cast hostD) (group.cast groupD) = some y)
    (addresses : ∀c, archiveSliceChart ports c x = chart c block)
    (earlier : ∀c, (chart c block).Fits limit hosts bw) (frame : ∀i < limit, original i = previous i)
    (positive : 0 < p) (kind : (classify G p s (label y)).correct operandRows)
    (valid : DescentBundleTagKeys.Fits paletteCodec a capacity p R (label y,operandRows))
    (argRoom : ports.argumentsPerNode < 2^ports.operandBits) (fit : (operandWords).length ≤ ports.argumentsPerNode)
    (ok : ∀ c b, (chart c b).Fits start hosts bw) (off : 2^d < 2^bw) (room_ : finish < 2^bw)
    (fitsWord : ∀ f, widths f ≤ bw) (kept : ∀i < finish, acquired i = outputMemory i) :
    Printed paletteCodec (fields (node viewAt group slot)) (label y) operandRows := by
  obtain ⟨roleAt,countAt,coordinateAt⟩ := ArchiveRead.slice_at_chart (d:=d) ports r B number room
    shape op label ptr flags previous original stored pitch roles wide covered chart cfg hostD nodeD groupD
    widthD x block shop group slot y hit addresses earlier frame
  have runs := DescentRetainedRangeDigits.layout (shape.sites y.1) y.2
  have count : (inputAt).live = (operandWords).length := by
    rw [countAt,←runs]
    exact Nat.mod_eq_of_lt (fit.trans_lt argRoom)
  apply printed_at_node G op a capacity p R start advice cfg chart original acquired block shop group slot
    positive (shape.sites y.1) y.2 (label y) kind valid ok off room_ fitsWord kept
    (roleAt.trans (token_val G s Z op (label y))) count fit
  intro _ j
  have exactField (f : Fin 3) :
      value ((inputAt).header (j.castLE fit)) f = value ((operandWords)[j.val]) f := by
    have used : (j.castLE fit).val < (occurrences (shape.sites y.1) y.2).length := by
      rw [←runs]
      exact j.isLt
    exact (coordinateAt (j.castLE fit) f (Or.inl used)).trans (atSlot_lt (shape.sites y.1) y.2 f j)
  rcases issued : (inputAt).header (j.castLE fit) with ⟨s₁,t₁,c₁⟩
  rcases expected : (operandWords)[j.val] with ⟨s₂,t₂,c₂⟩
  have begins := exactField 0
  have strides := exactField 1
  have counts := exactField 2
  rw [issued,expected] at begins strides counts
  change s₁=s₂ at begins
  change t₁=t₂ at strides
  change c₁=c₂ at counts
  cases begins
  cases strides
  cases counts
  rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
