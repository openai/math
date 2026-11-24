import OAI.Computability.VPVNP.PairRefreshOriginLevelGeometry

/-! # Preparing and dispatching a selected refresh head -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles LocalHistory NetworkKernel NodeArguments TreeDecode
open VertexImage DFS
open scoped Fin.CommRing
set_option quotPrecheck false

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n hist w start positions width : ℕ)

local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => selected B f hf blocks budget X branch
local notation "rows" => tagWords B.recordLimit (tags₀)
local notation "pos" => layerBase B.recordLimit first (tags₀)
local notation "format₀" => SelectedPacketFormat B f hf blocks budget X branch first
local notation "desc₀" => selectedDesc B f hf blocks budget X branch first
variable (room : Rooms n hist w start positions blocks ⟨leafLayer (siteOrder X), .cursor⟩
      (executeLevels B f hf blocks budget X branch))
    (x : Row (executeLevels B f hf blocks budget X branch))
local notation "i₀" => x.val.1
local notation "u₀" => x.val.2
local notation "v₀" => (passes)[i₀]
local notation "R₀" => rowSite n hist w start positions blocks width (leaf₀) passes room x
local notation "nextBase" => TraversalRows.address B.recordLimit
  ((pos) (i₀).val) (siteOrder (v₀).input).length
local notation "ptr" => sitePointers B.recordLimit nextBase (ShrinkRoleDirectory.outputOrder (v₀))
local notation "head₀" => (fun z => Packet.mk ((ptr) u₀).1
  (pullBits ((v₀).pass.output_eq (v₀).term) (packed ((v₀).pass.next (v₀).term)) u₀ z))

private theorem preparedHead {bits len labels : ℕ} (R : RefreshHook.Site B len labels bits)
    {q : Packet} {new : R.nextState.network.Half R.newerSite} {node : Word bits}
    {fmt : Packet → Prop} {desc : ℕ → List ℕ} {counts : Scratch bits len → B.Entry → ℕ}
    {cap limit : ℕ} {pending : List Packet} {s : Scratch bits len}
    {data : Fin 10 → Word bits} {vals : LeafSourceLoad.Static 34 → Word bits}
    (addr : node.val = R.parent)
    (frame : R.geometry = (NativeFrame.frameBase R.regions : Word bits))
    (eqn : q = ⟨R.parent, packed R.nextState R.newerSite new⟩)
    (ready : Budgeted R.arena fmt (VertexFrameData R.regions data R.roleOffset vals)
      desc counts cap limit (q :: pending) s) : R.Prepared node s := by
  have stored := ready.frontier.head.2.2.2
  rw [eqn] at stored
  have resident := ready.frontier.frame.resident
  rw [← frame] at resident
  exact ⟨addr, resident, new, stored⟩

set_option maxHeartbeats 1500000 in
-- The selected term carries dependent input and output networks.
/-- A genuine budgeted head gives the resident geometry and stored newer
half used by the local parser at its physical entry. -/
theorem level_prepared {data : Fin 10 → Word w} {vals : LeafSourceLoad.Static 34 → Word w}
    {counts : Scratch w n → B.Entry → ℕ} {nodeCap limit : ℕ}
    {pending : List Packet} {s : Scratch w n}
    (z : ((v₀).pass.step.term (v₀).term).output.Half u₀)
    (ready : Budgeted (R₀).arena (format₀) (VertexFrameData (R₀).regions data (R₀).roleOffset vals)
      (desc₀) counts nodeCap limit ((head₀) z :: pending) s) :
    (R₀).Prepared (((ptr) u₀).1 : Word w) s := by
  have addr := level_parent B f hf blocks budget X branch n hist w start positions width room x
  have fit := level_parent_val B f hf blocks budget X branch n hist w start positions width room x
  have node := (congrArg (fun j : ℕ => (j : Word w).val) addr).trans fit
  have packetEq :=
    level_packet B f hf blocks budget X branch n hist w start positions width room x z
  exact preparedHead B (R₀) node rfl packetEq ready

set_option maxHeartbeats 1500000 in
-- The site address and its packed representation use the selected execution.
include room width in
/-- The physical dispatch probe reads the published refresh role and avoids
both terminal-controller cells. The exclusive tag end can equal the header. -/
theorem level_dispatch (offset : ℕ) (terminal : Word w) (m : Memory w)
    (published : TraversalRoles.Reads w m offset B.recordLimit first (tags₀))
    (codes : 2 < 2 ^ w) (below : offset + first + rows ≤ terminal.val)
    (headerFit : terminal.val + 31 < 2 ^ w) :
    let cell := ((offset : Word w) + (((ptr) u₀).1 : Word w)).val
    NodeDispatch.role (m cell) = .refresh ∧ TerminalLink.workerCell terminal cell := by
  intro cell
  have ptrEq := level_parent B f hf blocks budget X branch n hist w start positions width room x
  have parentEq := parent_eq n hist w start positions blocks width (leaf₀) passes room x
  have fits := level_parent_val B f hf blocks budget X branch n hist w start positions width room x
  have atRow : (((ptr) u₀).1 : Word w).val = ShrinkRoleDirectory.address B.recordLimit first
      (leaf₀) passes x.val :=
    (congrArg (fun j : ℕ => (j : Word w).val) ptrEq).trans (fits.trans parentEq)
  have hit := ShrinkRoleDirectory.dispatch_at_site B.recordLimit first (leaf₀) passes
    published codes (below.trans terminal.isLt.le) _ x.val atRow
  refine ⟨hit.trans (congrArg Role.dispatch x.property),TerminalLink.workerCell_of_lt headerFit ?_⟩
  have parentBound : (R₀).parent < first + rows := (R₀).room.parentBound
  have addressBound : offset + (R₀).parent < terminal.val := by omega
  change ((offset : Word w) + (((ptr) u₀).1 : Word w)).val < _
  rw [ptrEq, ← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (addressBound.trans terminal.isLt)]
  exact addressBound

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
