import OAI.Computability.VPVNP.PairVirtualOrdinalCalls
import OAI.Computability.VPVNP.PairSelectedNativeRoles

/-!
# Transport of the installed vertex contracts to the virtual pair

The private regions and role offset used in the packed per-level proofs
are exactly the geometry read from the current ordinal's memory. The
machine's end-of-stack word has the actual input length as its value.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds LocalHistory TraversalRows
open VertexImage CutSchedule ExponentTrace TreeDecode NetworkKernel
open scoped Fin.CommRing

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
    {D : FixedProgramDiagonal.Program} {B : S.Templates} {u : PairExponents B.growthConstant}
    {n : ℕ} {hn : 2 ≤ n} {ht : 21 ≤ 2 ^ (D.geometry n).w} {clk : 44 ≤ n ^ 10000}
    (V : D.VirtualPairs B u hn D.constants.circuitExponent)
    (adv : Bits (n ^ D.constants.advicePower))
    (ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower))
    (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
    {labels : ℕ} (order : B.Entry ≃ Fin labels) (f : B.Entry → A) (ok : B.IsSolution f)
    (sites : SiteParsers f V.scanState.network)
    (z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)
    (baseBits laneBits ord power scan : ℕ)

local notation "group" => D.executionGroup n ht clk
local notation "pub" => terminalOperands (group)
local notation "hdr" => vertexHeader (group)
local notation "w₀" => Geometry.w (D.geometry n)
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "X₀" => VirtualPairs.scanState V
local notation "exec₀" => B.execute f ok (T₀) le_rfl (X₀)
local notation "Y₀" => StateExecution.finalState (exec₀) z
local notation "L₀" => BlockProgram.layout B (Fin.val (pub 2)) (State.positions (X₀)) (T₀)
local notation "base" => endAddress (L₀)
local notation "tags" => TraversalRoles.selected B f ok (T₀) le_rfl (X₀) z
local notation "size" => TraversalRoles.tagWords B.recordLimit (tags)
local notation "width" => State.totalWidth (Y₀)
local notation "offset" => (((size) + (width) : ℕ) : BurstRAM.Word w₀)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n ((base) + (size)) labels
local notation "image" => TerminalProgram.nativeSegments B D.constants D.numerator
  D.denominator order
local notation "placement₀" => VertexImage.placement (image)
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template (image)) w₀ pub
local notation "vals₀" => LeafVisit.cacheWords (V.data adv ξ i (physicalNomination rfl μ))
  (virtualBits D.addressFactor n) (roundedUp 1 4 n)

attribute [local irreducible] VertexImage.placement VertexImage.template BlockProgram.layout
  BlockSchedule.Templates.execute CursorNetwork.cursorState CursorBounds.wordBits
  selectedDesc ordinalJobCost

/-- Replace the typed role table's common frame by the twelve words
actually initialized in the current private burst. -/
theorem VirtualPairs.rowsAt_of_layout {calendar reference : Memory w₀} (m : Memory w₀)
    {bits : Fin (Y₀).totalWidth → Bool} {tab : Fin (L₀).shape.tables}
    (pack : VertexPacked (group) (L₀) B.recordLimit (tags) (width))
    (entry : TerminalProgram.VertexEntry B f ok (T₀) le_rfl (X₀) z (L₀) tab baseBits laneBits
      pub calendar reference bits)
    (later : LinkedVertexMemory (group) reference ord m)
    (length : (pub 6).val = n) (count : (pub 9).val = labels)
    (domain : BurstRAM.Word w₀ → DFS.Scratch w₀ n → Prop)
    (handlers : NodeDispatch.Role → DFS.HookParser w₀ n)
    (rows : let data := NativeFrame.leafWords (slotDegree S) pub hdr (offset) m
      let fmt := SelectedPacketFormat B f ok (T₀) le_rfl (X₀) z (base)
      let desc := selectedDesc B f ok (T₀) le_rfl (X₀) z (base)
      let valid := Budgeted (W := w₀) (endAddr := n) (area).arguments fmt
        (VertexFrameData (area) data (offset) (vals₀)) desc
        (privateHistogram order.symm (area).histBase) (n ^ 9000) (n * n ^ 9000)
      SelectedChecks B f ok (T₀) le_rfl (X₀) z (base) (placement₀) (M₀) m
        ((NativeFrame.frameBase (area) : ℕ) : BurstRAM.Word w₀) (offset) (area).histBase order.symm
        sites valid domain handlers (ordinalJobCost n power scan)) :
    V.SelectedRowsAt adv ξ i μ order f ok sites z m power scan := by
  obtain ⟨geometry, role, _⟩ := entry.role_layout B f ok (T₀) le_rfl (X₀) z (group) n labels
    baseBits laneBits ord m pack later length count
  unfold VirtualPairs.SelectedRowsAt
  rw [geometry, role, length]
  exact ⟨domain, handlers, rows⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
