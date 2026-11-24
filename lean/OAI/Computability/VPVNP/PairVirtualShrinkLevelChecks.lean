import OAI.Computability.VPVNP.PairVirtualShrinkPhysics
import OAI.Computability.VPVNP.PairVirtualShrinkPhysicalCost
import OAI.Computability.VPVNP.PairShrinkSelectedFootprint
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalLevelChecks
import OAI.Computability.VPVNP.PairSelectedShrinkRows

/-!
# Shrinking level checks for the physical site readers of a virtual pair

The directory used by the installed shrinking hook selects the same site
bank as the level-check proof. The chronological occurrence identifies the
child order, histogram increment, protected-memory reads and clock charge
of each accepted row.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.VirtualShrink

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary Compression CompressorRecords
open DescriptorSpace DFS TerminalProgram TraversalRows TraversalRoles VertexImage NodeArguments
open LocalHistory TreeDecode ShrinkRole
open scoped Fin.CommRing

variable {k A : Type} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) (G : PairStages.Group)
    (n p q : ℕ) (order : B.Entry ≃ Fin (Fintype.card B.Entry)) {lanes : ℕ} (T : ℕ)
    (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (m : Memory G.w)

attribute [local irreducible] BlockProgram.layout BlockSchedule.Templates.execute executeLevels
  StateExecution.finalState VertexImage.template VertexImage.placement
  ShrinkRoleDirectory.occurrence selectedDesc canonicalParent physicalSiteBank

set_option quotPrecheck false
local notation "pub" => terminalOperands G
local notation "L" => BlockProgram.layout B (pub 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "rows" => selectedLayers B f hf T hT X z
local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes
local notation "first" => (⟨leafLayer (siteOrder X), .cursor⟩ : TaggedLayer)
local notation "base" => endAddress L
local notation "size" => tagWords B.recordLimit tags
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "width" => State.totalWidth Y
local notation "offset" => ((size+width : ℕ) : Word G.w)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n (base+size)
  (Fintype.card B.Entry)
local notation "tableArea" => TerminalLayout.privateRegions (slotDegree S) n
  (base+words B.recordLimit rows) (Fintype.card B.Entry)
local notation "hdr" => vertexHeader G
local notation "data" => NativeFrame.leafWords (slotDegree S) pub hdr offset m
local notation "image" => nativeSegments B G.constants p q order
local notation "place" => placement image
local notation "host" => PrivateRAM.Template.instantiate (template image) G.w pub
local notation "hist" => privateHistogram (W := G.w) (endAddr := n) order.symm (area).histBase
local notation "typed" vals => Budgeted (W := G.w) (endAddr := n) (area).arguments
    (SelectedPacketFormat B f hf T hT X z base) (VertexFrameData area data offset vals)
    (selectedDesc B f hf T hT X z base) hist (n^9000) (n*n^9000)
local notation "earlier" j => layerBase B.recordLimit base tags j

variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
  {baseBits laneBits ord limit : ℕ} {calendar reference : Memory G.w}
  {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
  (history : SelectedPayloadHistory.Past B f hf
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    (CompiledResident.payload B f hf (terminalOperands G 2) X.positions T n)
    (executeLevels B f hf T hT X z) calendar)
  (entry : TerminalProgram.VertexEntry (w := G.w) B f hf T hT X z
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T) table baseBits laneBits
    (terminalOperands G) calendar reference bits)
  (packed : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    B.recordLimit (TraversalRoles.selected B f hf T hT X z)
    (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
  (frame : LinkedVertexMemory G reference ord m)
  (wide : MapConstants.widthThreshold B.shrink ≤ G.w)

variable (fits : ∀ x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z),
  ∀ m, canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection (w := G.w)
    (Fintype.card B.Entry) n
    (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T) +
      words B.recordLimit (selectedLayers B f hf T hT X z))
    (layerBase B.recordLimit
      (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T))
      (TraversalRoles.selected B f hf T hT X z) x.val.1.val) limit m)
local notation "bank" => physicalSiteBank (G := G) (n := n) (T := T)
  B f hf hT X z history entry packed frame wide fits
local notation "shrinkHook" => ShrinkRoleDirectory.parser B.recordLimit base first passes
    (fun x => canonicalParent (bank x) order f hf)

set_option maxHeartbeats 2400000 in
-- The physical and chronological packet formats have dependent site and half types.
/-- Every shrinking index in the selected physical bank meets the terminal contract
for every saved static frame and every choice of leaf and refresh handlers. -/
theorem levelChecks_at (phy : Physics B f hf G n order T hT X z m)
    (info : ∀ x : sites, CanonicalSiteData (bank x) host f hf T hT X z x.val.1
      (RoleDomains.siteId B f hf T hT X z x) base)
    (maps : ∀ (x : sites) parent, CanonicalMapData (bank x) hdr parent)
    (vals : LeafSourceLoad.Static 34 → Word G.w)
    (native : (shrinkHook).ExactOn
      (RoleDomains.Domain X B.recordLimit base passes area data offset vals hist
        (n^9000) (n*n^9000) .shrink)
      host ((place).entry .shrink) ((place).dfsPC 3) (place).dfs m)
    (leaf refresh : HookParser G.w n) (i : Fin (passes).length)
    (shrinking : tagLevel B f hf (passes)[i] = .shrink) :
    LevelChecks B f hf (dispatcher (RoleDomains.handlers leaf shrinkHook refresh) m offset)
      (typed vals) hist
      (JobGuard place host m (TerminalLink.workerCell hdr)
        (ordinalJobCost n 1 (RatedRoles.scan B order)))
      B.recordLimit (earlier i.val) (passes)[i] := by
  have region : tableArea = area := congrArg
    (fun count => TerminalLayout.privateRegions (slotDegree S) n (base + count)
      (Fintype.card B.Entry))
    phy.rowEq.symm
  have checked := canonicalLevelChecks (w := G.w) (n := n) B f hf T hT X z base i shrinking
    place host m (size+width) data vals order
    (n^9000) (n*n^9000) 1 (RatedRoles.scan B order) bank
    (RoleDomains.handlers leaf shrinkHook refresh) rfl
    (template_contains image pub) phy.published phy.codes phy.tagEnd phy.headerFit
    le_rfl le_rfl (by rw [region]; exact phy.histFit) le_rfl phy.budget.width
    phy.budget.credit (by rw [region]; exact native)
    (fun _ => by unfold physicalSiteBank; rfl) (fun _ => by unfold physicalSiteBank; rfl) info maps
    (phy.budget.label_count f hf hT z i shrinking) (fun x s tape tail job hit => by
      have guard := physicalSiteBank_rowTrace (G := G) (n := n) (T := T)
        B f hf hT X z history entry packed frame wide fits x order s tape job tail hit
      have cost := physical_rates (G := G) (n := n) (T := T)
        B f hf hT X z order phy.budget history entry packed frame wide fits x
        (ShrinkRoleDirectory.address B.recordLimit base first passes x.val : Word G.w)
        s tape tail job hit
      exact ⟨guard.1, guard.2, cost⟩)
  have headerEq : TerminalLink.header (host).publicData = hdr := rfl
  simpa only [region, headerEq, List.get_eq_getElem, Fin.getElem_fin] using checked

end PairSimulation.VirtualShrink

end

end VPVNP
end Computability
end OAI
