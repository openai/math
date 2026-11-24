import OAI.Computability.VPVNP.PairShrinkSiteSources
import OAI.Computability.VPVNP.PairShrinkSiteHistory
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory

/-!
# The complete resident bank in the running terminal worker

A single chronological shrinking occurrence supplies all row certificates
for the vertex. Its old and successor DFS pointers, chosen terms and both
interval banks remain readable after preceding vertices have flushed their
private histograms.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots LocalHistory
open TraversalRoles TraversalRows LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {K : Type} {A : Type*} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
variable (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f) {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes)
variable (start : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf T hT start).Choices)
variable {G : Group} (positions n : ℕ)
local notation "vs" => executeLevels B f hf T hT start branch
local notation "tags" => selected B f hf T hT start branch
local notation "rows" => selectedLayers B f hf T hT start branch
local notation "params" => terminalOperands G
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val positions T
local notation "rowEnd" => (endAddress D + words B.recordLimit rows)
variable (cur : Fin (executeLevels B f hf T hT start branch).length) (i : Fin S.steps) {g : ℕ}
variable (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (tape : List Bool)
local notation "older" => layerBase B.recordLimit (endAddress D) tags cur.val
local notation "later" => layerBase B.recordLimit (endAddress D) tags (cur.val + 1)
private noncomputable local instance bankBase : DecidableEq X.Base := Classical.decEq _

set_option maxHeartbeats 2000000 in
-- The selected pass and its actual directory share both dependent graph indices.
/-- The producing pass yields all resident sources, for every possible old
assignment and parent packet, at any later physical vertex call. -/
theorem rowSources_vertex
    (occurrence : vs[cur] = shrinkLevel B f hf i X sel tape)
    {tab : Fin (D).shape.tables} {baseBits laneBits cap width ord : ℕ}
    {roles : List TraversalRoles.TaggedLayer} {calendar reference phy : Memory G.w}
    {bits : Fin (StateExecution.finalState (B.execute f hf T hT start) branch).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past B f hf D
      (CompiledResident.payload B f hf (params 2) positions T n) vs calendar)
    (entry : TerminalProgram.VertexEntry B f hf T hT start branch D tab baseBits laneBits params
      calendar reference bits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy) :
    ∃ bounds : ShrinkResidentSources.Bounds B i X (params 2) positions T cur.val,
      ∀ v (x : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
        X.packingInputIso.site.symm) X.network.Half v)
        (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
        (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v),
        RowSources B i X sel (params 2) positions T cur.val bounds n rowEnd older later v x parent
          phy (vertexHeader G) q := by
  have live := entry.packedSitePayload packed frame history
  have input := CompiledResident.read live cur
  rw [occurrence] at input
  have data := (CompiledResident.shrink_payload ..).mp input
  have shrinking : vs[cur].origin.ordinal < S.steps := by rw [occurrence]; exact i.isLt
  refine ⟨data.bounds, fun v x parent q ↦ ?_⟩
  apply rowSources B i X sel (params 2) positions T cur.val data.bounds n rowEnd older later
    v x parent phy (vertexHeader G) q data.words data.sources
  · exact entry.packedSiteLayer packed frame cur.val cur.isLt.le
  · exact entry.packedSiteLayer packed frame (cur.val + 1) cur.isLt
  · exact CompiledResident.shrink_successor_stride live cur shrinking
  · exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans packed.arena)

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
