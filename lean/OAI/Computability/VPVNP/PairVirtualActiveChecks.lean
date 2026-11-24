import OAI.Computability.VPVNP.PairSelectedRefreshRows
import OAI.Computability.VPVNP.PairSelectedShrinkRows
import OAI.Computability.VPVNP.PairVirtualSelectedRoles
import OAI.Computability.VPVNP.PairVirtualCursorLeafNumbered

/-! # The three native readers on the same selected vertex burst -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds LocalHistory TraversalRows
open TraversalRoles VertexImage CutSchedule ExponentTrace TreeDecode NetworkKernel DFS
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
    (baseBits laneBits ord : ℕ)

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
local notation "tags" => selected B f ok (T₀) le_rfl (X₀) z
local notation "passes" => executeLevels B f ok (T₀) le_rfl (X₀) z
local notation "first" => TaggedLayer.mk (leafLayer (siteOrder (X₀))) Role.cursor
local notation "size" => tagWords B.recordLimit (tags)
local notation "width" => State.totalWidth (Y₀)
local notation "tagWord" => (((size) + (width) : ℕ) : BurstRAM.Word w₀)
local notation "image" => TerminalProgram.nativeSegments B D.constants D.numerator
  D.denominator order
local notation "V₀" => VertexImage.placement (image)
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template (image)) w₀ pub
local notation "vals₀" => LeafVisit.cacheWords (V.data adv ξ i (physicalNomination rfl μ))
  (virtualBits D.addressFactor n) (roundedUp 1 4 n)
local notation "rate" => RatedRoles.scan B order

attribute [local irreducible] VertexImage.placement VertexImage.template BlockProgram.layout
  BlockSchedule.Templates.execute CursorNetwork.cursorState CursorBounds.wordBits
  selectedDesc ordinalJobCost

set_option maxHeartbeats 1200000 in
-- Unifying the three dependent row domains traverses the entire selected state history.
/-- Choose each frozen role reader once. Its native code and its selected
monomial paths then use exactly the same reader and the same argument frame
in the combined private burst. -/
theorem VirtualPairs.activeChecks {calendar reference : Memory w₀} (m : Memory w₀)
    {bits : Fin (Y₀).totalWidth → Bool} {tab : Fin (L₀).shape.tables}
    (pack : VertexPacked (group) (L₀) B.recordLimit (tags) (width))
    (entry : TerminalProgram.VertexEntry B f ok (T₀) le_rfl (X₀) z (L₀) tab baseBits laneBits
      pub calendar reference bits)
    (later : LinkedVertexMemory (group) reference ord m)
    (length : (pub 6).val = n) (count : (pub 9).val = labels)
    (shrinking : TerminalProgram.ShrinkRows B f ok (group) n D.numerator D.denominator order
      (T₀) le_rfl (X₀) z m)
    (refreshing : TerminalProgram.RefreshRows B f ok (group) n D.numerator D.denominator order
      (T₀) le_rfl (X₀) z m)
    (cursor : let area := NativeFrame.fromHeader (slotDegree S) pub hdr m
      let offset := m (hdr + 14).val
      let data := NativeFrame.leafWords (slotDegree S) pub hdr offset m
      let fmt := SelectedPacketFormat B f ok (T₀) le_rfl (X₀) z (base)
      let desc := selectedDesc B f ok (T₀) le_rfl (X₀) z (base)
      ∃ leaf : HookParser w₀ n,
        leaf.ExactOn (RoleDomains.Leaf (X₀) B.recordLimit (base) area data offset (vals₀))
          (M₀) ((V₀).entry .leaf) ((V₀).dfsPC 3) (V₀).dfs m ∧
        ∀ shrink refresh : HookParser w₀ n, SelectedCursorLeaf.Rows (V₀) (M₀)
          (RoleDomains.handlers leaf shrink refresh) m offset area data (vals₀) B.recordLimit
          (base) fmt desc order.symm (TerminalLink.workerCell hdr) (n ^ 9000) (n * n ^ 9000)
          1 (rate) (X₀) sites) :
    V.SelectedRowsAt adv ξ i μ order f ok sites z m 1 (rate) := by
  obtain ⟨geom, offset, _⟩ := entry.role_layout B f ok (T₀) le_rfl (X₀) z (group) n labels
    baseBits laneBits ord m pack later length count
  obtain ⟨s, shr⟩ := shrinking
  obtain ⟨r, ref⟩ := refreshing
  obtain ⟨leaf, leafNative, leafRows⟩ := cursor
  let sr := ShrinkRoleDirectory.parser B.recordLimit (base) (first) (passes) s
  let handlers := RoleDomains.handlers leaf sr r
  have both := leafRows sr r
  rw [geom, offset] at leafNative both
  obtain ⟨shrNative, shrLevels⟩ := shr (vals₀)
  obtain ⟨refNative, refLevels⟩ := ref (vals₀)
  apply V.rowsAt_of_layout adv ξ i μ order f ok sites z baseBits laneBits ord 1 (rate) m
    pack entry later length count _ handlers
  apply TerminalProgram.VertexEntry.native_checks B f ok (T₀) le_rfl (X₀) z (group)
    D.numerator D.denominator n labels order baseBits laneBits ord 1 (rate) m pack entry
    later (vals₀) leaf s r sites length count
  · intro role
    cases role with
    | leaf => exact leafNative
    | shrink => exact shrNative
    | refresh => exact refNative
  · exact both
  · exact shrLevels leaf r
  · exact refLevels leaf sr

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
