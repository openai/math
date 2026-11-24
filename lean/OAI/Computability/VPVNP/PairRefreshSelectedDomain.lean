import OAI.Computability.VPVNP.PairRefreshSelectedPackets
import OAI.Computability.VPVNP.PairVertexRoleDomains

/-! # Preparing the refresh reader from a popped vertex packet -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM Compression CompressorRecords DescriptorSpace TraversalRows TraversalRoles
open DFS VertexImage LocalHistory
open scoped Fin.CommRing

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n hist w start positions : ℕ)

local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "rows" => tagWords B.recordLimit (selected B f hf blocks budget X branch)
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget X) branch)
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n (first + rows) hist

/-- On the selected execution, the vertex frame supplies the geometry pointer
and role offset of the refresh reader. Its stored packet supplies the typed
half at the promoted port of the same chronological row. -/
theorem prepared_of_domain (room : Rooms n hist w start positions blocks (leaf₀) passes)
    {data : Fin 10 → Word w} {vals : LeafSourceLoad.Static 34 → Word w}
    {counts : Scratch w n → B.Entry → ℕ} {nodeCap limit : ℕ} {node : Word w} {s : Scratch w n}
    (domain : RoleDomains.Domain X B.recordLimit first passes region data
      ((rows + width : ℕ) : Word w) vals counts nodeCap limit .refresh node s) :
    Prepared n hist w start positions blocks width (leaf₀) passes room node s := by
  obtain ⟨site, tag, address, out⟩ := domain
  obtain ⟨z, _, stored⟩ := out.packet
  let x : Row passes := ⟨site, tag⟩
  exact ⟨x, prepared_at n hist w start positions blocks width (leaf₀) passes room x node s z
    address out.frame.resident stored⟩

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
