import OAI.Computability.VPVNP.PairTerminalSiteDirectories

/-!
# Selected payloads and DFS layer bases in a physical site memory

The final prefix preserves the selected payloads in the reference memory.
The vertex packet preserves the directories and their operands as the
site loop advances, including the layer base of the terminal state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs LiveProgram.PairStages
open LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {K A : Type*} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {n T : ℕ}
variable {hT : T * S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices} {G : Group} {positions : ℕ}
variable {baseBits laneBits : ℕ}
local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "last" => List.length (List.dropLast (selectedLayers B f hf T hT X z))
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val positions T

private theorem selected_live : (vs).length < (D).levels := by
  rw [← TerminalBootstrap.selected_last_index, TerminalBootstrap.selected_prior_length,
    BlockProgram.actual_level_count, Nat.mul_comm T]
  omega

/-- All producing snapshots remain available in the actual physical memory
at this ordinal of the linked vertex scan. -/
theorem VertexEntry.packedSitePayload {cap width ord : ℕ} {table : Fin (D).shape.tables}
    {roles : List TaggedLayer} {calendar reference phy : Memory G.w}
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z D table baseBits laneBits (terminalOperands G)
      calendar reference bits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy)
    {data : SelectedPayloadHistory.Data (w := G.w) B f hf}
    (past : SelectedPayloadHistory.Past B f hf D data (vs) calendar) :
    SelectedPayloadHistory.Past B f hf D data (vs) phy := by
  have live : (vs).length < (D).levels := selected_live
  have idx := TerminalBootstrap.selected_last_index B f hf T hT X z
  have frozen := entry.payload B f hf T hT X z (idx ▸ live) past
  exact (packed.site_operands frame entry live (by change 28 ≤ 54; decide) frozen).2

/-- Cell 14 of each live level contains that layer's actual DFS row prefix
on entry to the physical site. The last state is included. -/
theorem VertexEntry.packedSiteLayer {cap width ord : ℕ} {table : Fin (D).shape.tables}
    {roles : List TaggedLayer} {calendar reference phy : Memory G.w}
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z D table baseBits laneBits (terminalOperands G)
      calendar reference bits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy)
    (j : ℕ) (hj : j ≤ (vs).length) :
    phy (levelStart D j + 14) = (layerBase B.recordLimit (endAddress D) tags j : Word G.w) := by
  obtain ⟨low, high⟩ := packed.traversal_frames frame
  obtain ⟨ds, stored⟩ := entry.site_directories selected_live
    (by change 28 ≤ 54; decide) low high
  have row := stored.currentBase j (by simpa only [levelFibers, List.length_ofFn] using hj)
  rw [levelFibers_tags (vs) ds] at row
  simpa only [levelStart, Nat.zero_mul, Nat.add_zero, TraversalRoles.selected] using row

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
