import OAI.Computability.VPVNP.PairTerminalPackedPrefix
import OAI.Computability.VPVNP.PairTerminalVertexFramePacked

/-!
# Selected compressor levels at a physical vertex call

The terminal prefix publishes wire offsets in a table of the final level.
The traversal rows, shared wire bits and role tags all lie above the level
allocation. During the vertex scan the counter suffix lies below the levels
and the two terminal controller words lie above them. Consequently each
earlier level still has its calendar image when a vertex invokes a map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace TraversalRows LocalHistory
open LiveProgram.PairStages.Group.Auxiliary

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
  {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {n T : ℕ}
  {hT : T * S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
  {z : (B.execute f hf T hT X).Choices}
  {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ}
local notation "last" => List.length (List.dropLast (selectedLayers B f hf T hT X z))
local notation "levels" => executeLevels B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- At each physical ordinal, all words up to the end of an earlier selected
level have their calendar values. This includes its map headers and term rows. -/
theorem VertexEntry.linkedLevelWindow {w : ℕ} {pub : Fin 11 → Word w}
    {calendar reference phy : Memory w} {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar reference bits)
    {base grammar labels ord : ℕ}
    (frame : VertexFrame.Linked (TerminalLink.header pub) base grammar labels reference ord phy)
    (room : (TerminalLink.header pub).val + 32 ≤ 2 ^ w)
    (counters : base + grammar + labels ≤ levelsBase L)
    (arena : endAddress L ≤ (TerminalLink.header pub).val)
    (allocated : (levels).length ≤ L.levels) (j : Fin (levels).length) :
    ∀ x, levelsBase L ≤ x → x < levelStart L (j.val + 1) → phy x = calendar x := by
  intro x lo hi
  have final := TerminalBootstrap.selected_last_index B f hf T hT X z
  have before := hi.trans_le (levelStart_mono L j.isLt)
  have bound := before.trans_le (levelStart_mono L allocated)
  have start : levelStart L last ≤ DescriptorSpace.tableBase L last tab := by
    unfold DescriptorSpace.tableBase arrayBase incidenceStart
    omega
  rw [← final] at before
  exact (frame.below room (counters.trans lo) (bound.trans_le arena)).trans
    (entry.raw x bound (.inl (before.trans_le start)))

open LiveProgram.PairStages

variable {G : Group} {positions : ℕ}
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val positions T

/-- The packed group workspace supplies the separation from both counter
stores and controller stores for the actual terminal public operands. The
calendar allocates one level for each selected pass and one for its output. -/
theorem VertexEntry.packedLevelWindow {cap width ord : ℕ} {table : Fin (D).shape.tables}
    {roles : List TraversalRoles.TaggedLayer} {calendar reference phy : Memory G.w}
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z D table baseBits laneBits (terminalOperands G)
      calendar reference bits)
    (packed : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord phy)
    (j : Fin (levels).length) :
    ∀ x, levelsBase D ≤ x → x < levelStart D (j.val + 1) → phy x = calendar x := by
  have base : (D).base ≤ levelsBase D := by
    unfold levelsBase directoryBase plannerTag frameBase
    omega
  have allocated : (levels).length ≤ (D).levels := by
    rw [← TerminalBootstrap.selected_last_index, TerminalBootstrap.selected_prior_length,
      BlockProgram.actual_level_count, Nat.mul_comm T]
    omega
  have arena : endAddress D ≤ (vertexHeader G).val :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans packed.arena)
  exact entry.linkedLevelWindow frame packed.room (packed.counter_base.trans base)
    arena allocated j

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
