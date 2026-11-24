import OAI.Computability.VPVNP.PairRefreshOriginLevelMemory
import OAI.Computability.VPVNP.PairRefreshSelectedGuardRows
import OAI.Computability.VPVNP.PairRefreshSelectedPublished

/-!
# All refresh level operands at the actual terminal vertex

The selected calendar's retained payload and the first four terminal phases
supply the memory for every refresh row. The two controller words and the
motif histogram may change between vertices. The physical memory frame
transfers the level rows, tags and map read bounds across those writes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TerminalProgram LiveProgram PairStages.Group.Auxiliary

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    (G : PairStages.Group) (n hist : ℕ) {l : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ l)
    (X : State (S.degreeExponent 0) l) (z : (B.execute f hf T hT X).Choices)

local notation "pub" => terminalOperands G
local notation "passes" => executeLevels B f hf T hT X z
local notation "L" => BlockProgram.layout B (Fin.val (pub 2)) X.positions T
local notation "tags" => selected B f hf T hT X z
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf T hT X) z)
local notation "size" => tagWords B.recordLimit (tags)

set_option maxHeartbeats 1500000 in
/-- The genuine live workspace realizes the complete refresh level memory
predicate at every reachable terminal site, independently of its ordinal. -/
theorem levelMemory_at (room : Rooms n hist G.w (terminalOperands G 2).val X.positions T
    ⟨leafLayer (siteOrder X),.cursor⟩ (executeLevels B f hf T hT X z))
    {baseBits laneBits ord : ℕ} {tab : Fin (L).shape.tables} {calendar vertex m : Memory G.w} {wire : Fin (width) → Bool}
    (entry : VertexEntry B f hf T hT X z (L) tab baseBits laneBits pub calendar vertex wire)
    (history : SelectedPayloadHistory.Past B f hf (L) (CompiledResident.payload B f hf (pub 2) X.positions T n)
      (passes) calendar)
    (packed : VertexPacked G (L) B.recordLimit (tags) (width)) (frame : LinkedVertexMemory G vertex ord m)
    (stack : (TerminalLayout.privateRegions (slotDegree S) n (endAddress (L)+size) hist).stackBase ≤ 2^G.w)
    (blocks : T ≤ n.log2+1) :
    LevelMemory B f hf T hT X z n G.w (pub 2).val X.positions width room pub m := by
  have arena := packed.arena
  have header := packed.room
  refine ⟨packed.roleWords frame ?_,?_,?_,?_,stack,?_,?_,?_⟩
  · rw [tagWords,selected_layers]
    exact entry.roles
  · change (size+width)+endAddress (L)+size ≤ (vertexHeader G).val
    omega
  · change (vertexHeader G).val+31 < 2^G.w
    omega
  · omega
  · exact published_at_site B f hf G (pub 2) X.positions T hT X z entry history packed frame room
  · exact guardLayout_at B f hf G n hist T hT X z room entry history packed frame
  · exact later_le B f hf G n hist T hT X z room blocks

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
