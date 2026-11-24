import OAI.Computability.VPVNP.PairTerminalPackedPrefix
import OAI.Computability.VPVNP.PairTerminalVertexFramePacked
import OAI.Computability.VPVNP.CompressorCompiledResident

/-!
# Reading a compiled pass payload in the current physical vertex memory

Each producing pass retains its input level and the successor pointer and
incidence bank. Even for the last pass, this bank ends at the final array base,
before the terminal program's offset table. Earlier physical vertices can
update counters and terminal control words without changing any retained cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

open BurstRAM Compression CompressorRecords DescriptorSpace PairSimulation
open LocalHistory TerminalProgram TraversalRows TraversalRoles LiveProgram.PairStages
open LiveProgram.PairStages.Group.Auxiliary

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {lanes T : ℕ}
variable {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
variable {z : (B.execute f hf T hT X).Choices}
variable {G : Group} {positions cap width ord baseBits laneBits : ℕ} {roles : List TaggedLayer}

local notation "pub" => terminalOperands G
local notation "passes" => executeLevels B f hf T hT X z
local notation "last" => List.length (List.dropLast (selectedLayers B f hf T hT X z))
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val positions T

variable {calendar reference phy : Memory G.w}
private theorem cells_before_offset {L : DescriptorSpace.Layout} {i final x : ℕ}
    (t : Fin L.shape.tables) (prev : i < final) (live : final < L.levels)
    (cell : SelectedPayloadHistory.Cells L i x) :
    L.base ≤ x ∧ x < endAddress L ∧ x < DescriptorSpace.tableBase L final t := by
  obtain ⟨lo, hi⟩ := SelectedPayloadHistory.cells_interval prev cell
  have floor : L.base ≤ levelsBase L := by
    unfold levelsBase directoryBase plannerTag frameBase
    omega
  have before : x < DescriptorSpace.tableBase L final t := hi.trans_le (Nat.le_add_right ..)
  have stop := (tableEnd_le_nextLevel L final t).trans (levelStart_mono L live)
  exact ⟨floor.trans lo, (before.trans_le (Nat.le_add_right ..)).trans_le stop, before⟩

private theorem final_live : last < (D).levels := by
  rw [TerminalBootstrap.selected_prior_length B f hf T hT X z, BlockProgram.actual_level_count]
  rw [Nat.mul_comm T, Nat.one_add]
  exact Nat.lt_succ_self _

attribute [local irreducible] BlockProgram.layout BlockSchedule.Templates.execute
  StateExecution.finalState executeLevels CompiledResident.payload SelectedPayloadHistory.Past

set_option maxHeartbeats 800000 in
-- Elaborate the physical word and pass types indexed by this branch of the compressor.
/-- The complete footprint of a selected pass has its calendar value at this
physical site, including every column of the successor incidence bank. -/
theorem PairSimulation.TerminalProgram.VertexEntry.packedPayloadWindow
    {table : Fin (D).shape.tables}
    {wireBits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
    (entry : VertexEntry (w := G.w) B f hf T hT X z D table baseBits laneBits
      (terminalOperands G) calendar reference wireBits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy)
    (j : Fin (passes).length) :
    SourceTransport.Agree (w := G.w) (SelectedPayloadHistory.Cells D j.val) calendar phy := by
  have prev : j.val < last := j.isLt.trans_eq (TerminalBootstrap.selected_last_index
    B f hf T hT X z).symm
  have live : last < (D).levels := final_live
  intro x cell
  obtain ⟨lo, hi, before⟩ := cells_before_offset (L := D) table prev live cell
  exact ((packed.directory frame lo hi).trans (entry.raw x hi (.inl before))).symm

variable {inputLength : ℕ}
local notation "data" => CompiledResident.payload (w := G.w) B f hf (pub 2) positions T inputLength

set_option maxHeartbeats 800000 in
-- Elaborate the physical word and pass types indexed by this branch of the compressor.
/-- Read a pass of either kind at its chronological index in physical memory. -/
theorem CompressorRecords.CompiledResident.read_vertex
    {table : Fin (D).shape.tables}
    {wireBits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past (w := G.w) B f hf D data passes calendar)
    (entry : VertexEntry (w := G.w) B f hf T hT X z D table baseBits laneBits
      (terminalOperands G) calendar reference wireBits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy)
    (j : Fin (passes).length) : data j.val passes[j] phy :=
  CompiledResident.payload_transfer (B := B) (f := f) (hf := hf) (workspace := pub 2)
    (positions := positions) (blocks := T) (n := inputLength) (cur := j.val) (v := passes[j])
    (CompiledResident.read (B := B) (f := f) (hf := hf) (workspace := pub 2)
      (positions := positions) (blocks := T) (n := inputLength) history j)
    (entry.packedPayloadWindow packed frame j)

set_option maxHeartbeats 800000 in
-- Elaborate the physical word and pass types indexed by this branch of the compressor.
/-- All native shrinking sources, header words, selected term and child
directory of the specified occurrence are present in the current site memory. -/
theorem CompressorRecords.CompiledResident.shrink_vertex
    {table : Fin (D).shape.tables}
    {wireBits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past (w := G.w) B f hf D data passes calendar)
    (entry : VertexEntry (w := G.w) B f hf T hT X z D table baseBits laneBits
      (terminalOperands G) calendar reference wireBits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy)
    (j : Fin (passes).length) {i : Fin S.steps} {g : ℕ}
    {Y : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)}
    {sel : SelectedScore.Selection B Y} {tape : List Bool}
    (occurrence : passes[j] = ⟨_, _, _, _, Y, _, .shrink i rfl Y, sel, tape⟩) :
    CompiledResident.ShrinkPayload (w := G.w) B (pub 2) positions T inputLength
      j.val i Y sel phy := by
  have current := CompiledResident.read_vertex (G := G) (inputLength := inputLength)
    history entry packed frame j
  rw [occurrence] at current
  exact (CompiledResident.shrink_payload B f hf (pub 2) positions T inputLength j.val i Y sel
    tape phy).mp current

end VPVNP
end Computability
end OAI
