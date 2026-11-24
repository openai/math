import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkRoleSelectedChildren
import OAI.Computability.VPVNP.PairTerminalSiteDirectories
import OAI.Computability.VPVNP.PairVertexLevelReads
import OAI.Computability.VPVNP.PairRefreshVertexInputWrites

/-! # Locator reads at a physical shrinking site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open TraversalControllerInputs

private theorem childSetup_footprint {w endAddr H first pitch offset cap base : ℕ}
    {pub : Fin 11 → Word w} {m : Memory w} {leaf : TaggedLayer} {ls : List (Fiber w)}
    (resident : Resident pub m H first pitch offset cap base leaf ls)
    (beforeH : ∀ j ≤ ls.length, first + j * pitch + 28 ≤ H)
    (level : Fin ls.length) (steps stage a : ℕ) (node : Word w) (saved : Scratch w endAddr) :
    let es := (selectedChildSetup pub m ls.length level.val steps stage a).trace node saved
    SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub)) es ∧
      SourceTransport.Writes (fun _ => False) es := by
  dsimp only
  have bound : level.val + 1 + (ls.length - (level.val + 1)) ≤ ls.length := by
    have := level.isLt
    omega
  have reads := VertexLevel.trace_worker_reads resident beforeH _ _ bound
  have writes := VertexLevel.trace_noWrites pub m (level.val + 1) (ls.length - (level.val + 1))
  constructor <;> intro addr value member <;>
    simp only [selectedChildSetup, Setup.seq, Setup.ticks, locatorSetup, List.mem_append,
      List.mem_replicate, reduceCtorEq, and_false, or_false] at member
  · exact reads addr value member
  · exact writes addr value member

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
  {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
  (z : (B.execute f hf T hT X).Choices) {G : Group} {n limit : ℕ}

attribute [local irreducible] ShrinkRoleDirectory.occurrence
set_option quotPrecheck false
local notation "pub" => terminalOperands G
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "rowBase" => endAddress D
local notation "rowEnd" => rowBase + words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "labelCount" => Fintype.card B.Entry

local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes
local notation "before" j => layerBase B.recordLimit rowBase tags j

/-- The selected child setup at every packed shrinking site reads only worker cells
and makes no external writes, for any incoming node and scratch state. -/
theorem physicalSiteBank_locator_footprint
    {table : Fin (D).shape.tables} {baseBits laneBits ord : ℕ}
    {calendar reference phy : Memory G.w} {bits : Fin (Y).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past B f hf D
      (CompiledResident.payload B f hf (pub 2) X.positions T n) passes calendar)
    (entry : TerminalProgram.VertexEntry B f hf T hT X z D table baseBits laneBits pub
      calendar reference bits)
    (packed : VertexPacked G D B.recordLimit tags (Y).totalWidth)
    (frame : LinkedVertexMemory G reference ord phy)
    (width : MapConstants.widthThreshold B.shrink ≤ G.w)
    (fits : ∀ x : sites, ∀ m, canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) labelCount n rowEnd (before x.val.1.val) limit m)
    (x : sites) (node : Word G.w) (saved : Scratch G.w n) :
    let site := physicalSiteBank B f hf hT X z history entry packed frame width fits x
    let es := (selectedChildSetup site.publicData site.mem site.levels site.passIndex
      S.steps x.occurrence.i.val (ShrinkBlockInputs.a x.occurrence.i)).trace node saved
    SourceTransport.Reads (TerminalLink.workerCell (vertexHeader G)) es ∧
      SourceTransport.Writes (fun _ => False) es := by
  have live : (passes).length < (D).levels :=
    (executeLevels_length B f hf T hT X z).trans_lt (by rw [BlockProgram.actual_level_count]; omega)
  have wide : 28 ≤ (D).shape.scalarFields := by change 28 ≤ 54; decide
  obtain ⟨low, high⟩ := packed.traversal_frames frame
  obtain ⟨ds, resident⟩ := entry.site_directories live wide low high
  have len : (levelFibers passes ds).length = (passes).length := by
    simp only [levelFibers, List.length_ofFn]
  have beforeH (j : ℕ) (hj : j ≤ (levelFibers passes ds).length) :
      levelStart D 0 + j * levelWords D + 28 ≤ (vertexHeader G).val :=
    (TraversalResidentHandoff.headers_before D live wide j (len ▸ hj)).trans
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans packed.arena))
  let level : Fin (levelFibers passes ds).length := ⟨x.val.1.val, by rw [len]; exact x.val.1.isLt⟩
  have scan := childSetup_footprint resident beforeH level S.steps x.occurrence.i.val
    (ShrinkBlockInputs.a x.occurrence.i) node saved
  let es := (selectedChildSetup pub phy (passes).length x.val.1.val S.steps x.occurrence.i.val
    (ShrinkBlockInputs.a x.occurrence.i)).trace node saved
  change SourceTransport.Reads _ es ∧ SourceTransport.Writes _ es
  simpa only [es, level, len] using scan

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
