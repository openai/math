import OAI.Computability.VPVNP.PairVertexRoleHandlers
import OAI.Computability.VPVNP.PairVertexRoleDomains
import OAI.Computability.VPVNP.PairVertexSelectedRoles
import OAI.Computability.VPVNP.PairVertexSelectedDesc
import OAI.Computability.VPVNP.PairVertexSelectedRoleLayout
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost
import OAI.Computability.VPVNP.PairTerminalNativeTable

/-!
# Selecting the actual vertex role at each chronological pass

The frozen descriptor chooses either a shrinking or refresh kernel at each
output layer. The three physical readers share a finite instruction table,
a private histogram and the same budgeted packet frontier. Header fields
and stored role words are read in the current site memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM LiveProgram LiveProgram.PairStages.Group.Auxiliary
open Compression CompressorRecords LocalHistory NodeArguments TraversalRows TraversalRoles
open DFS TreeDecode VertexImage NetworkKernel
open scoped Fin.CommRing

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
    (G : PairStages.Group) (p q n labels : ℕ) (order : B.Entry ≃ Fin labels)
    (baseBits laneBits : ℕ) (ord : ℕ) (power scan : ℕ)

local notation "pub" => terminalOperands G
local notation "hdr" => vertexHeader G
local notation "passes" => executeLevels B f hf T hT X z
local notation "first" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "tags" => selected B f hf T hT X z
local notation "L" => BlockProgram.layout B (Fin.val (pub 2)) X.positions T
local notation "base" => DescriptorSpace.endAddress (L)
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "width" => State.totalWidth (Y)
local notation "size" => tagWords B.recordLimit (tags)
local notation "offset" => (((size) + (width) : ℕ) : Word G.w)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n ((base) + (size)) labels
local notation "segments" => nativeSegments B G.constants p q order
local notation "V" => VertexImage.placement (segments)
local notation "M" => PrivateRAM.Template.instantiate (VertexImage.template (segments)) G.w pub

variable {calendar reference : Memory G.w} (m : Memory G.w)
    {bits : Fin ((B.execute f hf T hT X).finalState z).totalWidth → Bool}
    {tab : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
    (pack : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
      B.recordLimit (selected B f hf T hT X z) ((B.execute f hf T hT X).finalState z).totalWidth)
    (entry : VertexEntry B f hf T hT X z
      (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
      tab baseBits laneBits (terminalOperands G) calendar reference bits)
    (later : LinkedVertexMemory G reference ord m)

local notation "data" => NativeFrame.leafWords (slotDegree S) pub hdr (offset) m

variable (vals : LeafSourceLoad.Static 34 → Word G.w) (leaf : HookParser G.w n)
    (shrinkSites : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z)
      → HookParser G.w n)
    (refreshReader : HookParser G.w n) (sites : SiteParsers f X.network)

local notation "shrink" => ShrinkRoleDirectory.parser B.recordLimit (base)
  (first) (passes) shrinkSites
local notation "readers" => RoleDomains.handlers leaf (shrink) refreshReader
local notation "source" => privateHistogram order.symm (LeafArena.Regions.histBase (area))
local notation "doms" => RoleDomains.Domain X B.recordLimit (base) (passes) (area) (data) (offset)
  vals (source) (n ^ 9000) (n * n ^ 9000)
local notation "shape" => selectedDesc B f hf T hT X z (base)
local notation "valid" => Budgeted (W := G.w) (endAddr := n) (LeafArena.Regions.arguments (area))
  (SelectedPacketFormat B f hf T hT X z (base))
  (VertexFrameData (area) (data) (offset) vals) (shape) (source) (n ^ 9000) (n * n ^ 9000)
local notation "hook" => dispatcher (readers) m (offset)
local notation "guard" => JobGuard (V) (M) m (TerminalLink.workerCell hdr)
  (ordinalJobCost n power scan)
local notation "leaves" => sitePointers B.recordLimit (base) (siteOrder X)
local notation "inputs" => (fun u h => Packet.mk (Prod.fst ((leaves) u)) (packed X u h))
local notation "atLevel" => (fun i : Fin (passes).length => LevelChecks B f hf (hook) (valid)
  (source) (guard) B.recordLimit (layerBase B.recordLimit (base) (tags) (Fin.val i)) (passes)[i])

attribute [local irreducible] VertexImage.placement VertexImage.template
  ShrinkRoleDirectory.parser LevelChecks
  ordinalJobCost selectedDesc

include pack entry later in
/-- Role selection and the input domain are fixed by the installed
eleven-operand table and its frozen rows. Only local role-specific
execution contracts are required. -/
theorem VertexEntry.native_checks
    (length : (pub 6).val = n) (count : (pub 9).val = labels)
    (native : ∀ r, ((readers) r).ExactOn ((doms) r) (M) ((V).entry (rolePart r))
      ((V).dfsPC 3) (V).dfs m)
    (cursor : Subtrees (hook) (valid) sites (fun u => leafTree ((leaves) u)) (inputs) ∧
      Emits (valid) (source) (guard) sites (inputs) (leafJobs sites (leaves)))
    (shrinkRows : ∀ i : Fin (passes).length, tagLevel B f hf (passes)[i] = .shrink → (atLevel) i)
    (refreshRows : ∀ i : Fin (passes).length,
      tagLevel B f hf (passes)[i] = .refresh → (atLevel) i) :
    SelectedChecks B f hf T hT X z (base) (V) (M) m
      ((NativeFrame.frameBase (area) : ℕ) : Word G.w) (offset) (area).histBase
      order.symm sites (valid) (roleDomain (area) (data) (offset) vals (doms) m)
      (readers) (ordinalJobCost n power scan) := by
  obtain ⟨_, _, stored⟩ := entry.role_layout B f hf T hT X z G n labels
    baseBits laneBits ord m pack later length count
  have room := pack.room
  have span := pack.arena
  have fit : (offset).val + (base) + (size) ≤ 2 ^ G.w := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : (size) + (width) < 2 ^ G.w)]
    omega
  apply SelectedChecks.ofRoleRows B f hf T hT X z (base) (V) (M) m (area) (offset) (data) vals
    order.symm sites (shape) (n ^ 9000) (n * n ^ 9000) (readers) (doms)
    (ordinalJobCost n power scan)
  · have codes : 2 < 2 ^ G.w := by omega
    exact RoleDomains.domainsReady X B.recordLimit (base) (passes) (area) (data) (offset) vals
      (source) (n ^ 9000) (n * n ^ 9000) m stored codes fit le_rfl
  · exact native
  · exact cursor
  · intro vs layers i
    let v := vs[i]
    have role : tagLevel B f hf v = .shrink ∨ tagLevel B f hf v = .refresh := by
      rcases v with ⟨_, _, _, _, _, _, origin, _, _⟩
      cases origin <;> simp [tagLevel, ofOrigin]
    exact role.elim (shrinkRows i) (refreshRows i)

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
