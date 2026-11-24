import OAI.Computability.VPVNP.PairVertexShrinkFamilies
import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkTraversalAtVertex
import OAI.Computability.VPVNP.PairVertexRootEntry
import OAI.Computability.VPVNP.PairTerminalNativeTable

/-! # The shrinking handler at one linked vertex of the live pair machine -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM DFS Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles ShrinkRoleDirectory TerminalProgram NativeFrame NodeArguments
open LiveProgram PairStages PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {k K : Type} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes T : ℕ} (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) {G : Group} {n limit : ℕ}

attribute [local irreducible] ShrinkRoleDirectory.occurrence BlockProgram.layout
  BlockSchedule.Templates.execute StateExecution.finalState executeLevels ShrinkRole.canonicalFamily
  ShrinkRole.parentParser ShrinkRole.canonicalActions
set_option quotPrecheck false

local notation "pub₀" => terminalOperands G
local notation "layout₀" => BlockProgram.layout B (pub₀ 2).val X.positions T
local notation "passes₀" => executeLevels B f hf T hT X z
local notation "tags₀" => selected B f hf T hT X z
local notation "Y₀" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "base₀" => endAddress (layout₀)
local notation "rows₀" => tagWords B.recordLimit (tags₀)
local notation "rowEnd₀" => (base₀)+words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "count₀" => Fintype.card B.Entry
local notation "R₀" => TerminalLayout.privateRegions (slotDegree S) n ((base₀)+(rows₀)) (count₀)
local notation "off₀" => (((rows₀)+(Y₀).totalWidth : ℕ) : Word G.w)

variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables} {baseBits laneBits ordinal : ℕ}
    {calendar reference phy : Memory G.w} {wireBits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past B f hf (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
      (CompiledResident.payload B f hf (terminalOperands G 2) X.positions T n) (executeLevels B f hf T hT X z) calendar)
    (entry : VertexEntry B f hf T hT X z (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
      table baseBits laneBits (terminalOperands G) calendar reference wireBits)
    (packed : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
      B.recordLimit (selected B f hf T hT X z) (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
    (frame : LinkedVertexMemory G reference ordinal phy)
    (width : MapConstants.widthThreshold B.shrink ≤ G.w)
    (fits : ∀ (x : ShrinkSite (executeLevels B f hf T hT X z)) motif, ShrinkRole.canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) (Fintype.card B.Entry) n ((endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T))+words B.recordLimit (selectedLayers B f hf T hT X z))
      (layerBase B.recordLimit (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T)) (selected B f hf T hT X z) x.val.1.val) limit motif)

local notation "bank₀" => ShrinkRole.physicalSiteBank B f hf hT X z history entry packed frame width fits
local notation "H₀" => vertexHeader G
local notation "data₀" => leafWords (slotDegree S) (pub₀) (H₀) (off₀) phy

variable (p q : ℕ) (order : B.Entry ≃ Fin (Fintype.card B.Entry))
local notation "seg₀" => nativeSegments B G.constants p q order
local notation "V₀" => placement (seg₀)
local notation "M₀" => (template (seg₀)).instantiate G.w (pub₀)

set_option maxHeartbeats 2000000 in
/-- The current eleven-operand image executes the actual bank of selected
shrinking sites. Its directory locator, length, geometry and cache word all
come from the linked vertex memory and the fixed public operands. -/
theorem nativeShrink_at_vertex (size : (pub₀ 6).val = n) (labels : (pub₀ 9).val = (count₀))
    {vals : LeafSourceLoad.Static 34 → Word G.w} {counts : Scratch G.w n → B.Entry → ℕ}
    {nodeCap wordLimit : ℕ}
    (facts : ∀ (x : ShrinkSite (passes₀)), ShrinkRole.CanonicalSiteData ((bank₀) x) (M₀) f hf T hT X z
      x.val.1 (siteId B f hf T hT X z x) (base₀))
    (maps : ∀ (x : ShrinkSite (passes₀)) (parent : x.occurrence.nextState.network.Half x.occurrence.site),
      ShrinkRole.CanonicalMapData ((bank₀) x) (H₀) parent) :
    (shrinkHandler X B.recordLimit (base₀) (passes₀) (bank₀) order).ExactOn
      (Domain X B.recordLimit (base₀) (passes₀) (R₀) (data₀) (off₀) vals counts nodeCap wordLimit .shrink)
      (M₀) ((V₀).entry .shrink) ((V₀).dfsPC 3) (V₀).dfs phy := by
  have rowsEq : (rows₀) = words B.recordLimit (selectedLayers B f hf T hT X z) :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have reg := entry.selected_regions packed frame n (count₀) size labels
  rw [← rowsEq] at reg
  have cache : (data₀) 8 = ((R₀).cacheBase : Word G.w) := by
    change ((fromHeader (slotDegree S) (pub₀) (H₀) phy).cacheBase : Word G.w) = _
    rw [reg]
  have length : (data₀) 9 = (n : Word G.w) := by
    change (pub₀) 6 = (n : Word G.w)
    rw [← size]
    exact (Fin.cast_val_eq_self _).symm
  have bankRegion (x : ShrinkSite (passes₀)) :
      TerminalLayout.privateRegions (slotDegree S) n ((bank₀) x).rowEnd (count₀) = (R₀) := by
    change TerminalLayout.privateRegions (slotDegree S) n (rowEnd₀) (count₀) = (R₀)
    rw [rowsEq]
  have bankMemory (x : ShrinkSite (passes₀)) : ((bank₀) x).mem = phy := rfl
  obtain ⟨ds,resident⟩ := entry.shrinkLocator packed frame
  have checked := selectedFamilies B f hf T hT X z order (VertexGeometry.segment G.constants (slotDegree S) p q)
    TerminalRootGather.segment LeafRole.segment
    (RefreshVertex.refreshSegment B (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride order)
    (V₀) (M₀) (template_contains (seg₀) (pub₀)) (bank₀) (base₀) (R₀) (data₀) (off₀) vals counts
    nodeCap wordLimit phy ds resident bankRegion bankMemory cache length (H₀) facts maps
  have wordSpace : 1 < 2^G.w := by have room := packed.room; omega
  have live : 0 < G.w := by
    by_contra! zero
    rw [show G.w=0 by omega] at wordSpace
    norm_num at wordSpace
  have endFit : layerBase B.recordLimit (base₀) (tags₀) ((passes₀).length+1) ≤ 2^G.w := by
    have len : (tags₀).length = (passes₀).length+1 := by simp [selected]
    rw [← len,layerBase,List.take_length]
    change (base₀)+(rows₀) ≤ 2^G.w
    have arena := packed.arena
    have top := packed.room
    omega
  exact nativeShrink X B.recordLimit (base₀) (passes₀) (R₀) (data₀) (off₀) vals counts
    nodeCap wordLimit (bank₀) order (M₀) ((V₀).entry .shrink) ((V₀).dfsPC 3) (V₀).dfs phy
    live endFit (fun x => congrArg LeafArena.Regions.arguments (bankRegion x)) checked

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
