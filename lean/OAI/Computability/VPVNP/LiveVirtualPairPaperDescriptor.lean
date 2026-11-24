import OAI.Computability.VPVNP.LiveVirtualPairDescriptorExecution
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.LiveCompressedPairDescriptorPaths
import OAI.Computability.VPVNP.LiveCompressedPairPaperStartup

/-! # The descriptor path of the fixed physical compressed pair

The four cursor visits and the selected block visits are consecutive
segments of the same RAM program. The selected terms retain the readback
data for their terminal vertices. The path equivalence below uses the same
choice, memory and report sequence as the chronological probe bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair
open CompressorRecords ScheduledTrace DescriptorSpace
open scoped Fin.CommRing
open PairSimulation PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
  {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry)
  (base clk rate : ℕ) (pub : Fin 11 → Word (wordBits D.addressFactor n)) (m : Memory (wordBits D.addressFactor n))

local notation "addr" => D.addressFactor
local notation "ww" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "A" => BlockProgram.script B
local notation "P" => initialPositions D.addressFactor n
local notation "X" => VirtualPairs.scanState V
local notation "E" => B.execute f hf T le_rfl (VirtualPairs.scanState V)
local notation "small" => BlockClock.small B D.addressFactor n
local notation "cap" => sourceCap pub clk
local notation "L" => BlockProgram.layout B base P T
local notation "boot" => paperBootstrap B u
set_option quotPrecheck false in
local notation "entry" => after m (eventLog (cursorStartupLogs boot pub addr n base m (A).initial.length (A).block.length (A).size))
local notation "data" => CompiledResident.payload (w := ww) B f hf base P T n
local notation "res" => V.nativeResident f hf base data
set_option quotPrecheck false in
local notation "lastStage" => TerminalProgram.table (BlockProgram.layout B base P T).shape B.recordLimit (paperSegments B u c labels)

attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs TerminalProgram.workers

/-- A descriptor has a startup proof, a physical cursor interval, and a
scheduled result whose input memory is the output of that interval. -/
structure DescriptorData (Startup : Prop) (Cursor : Type*) (cost : Cursor → Prop)
    (clockSlack clockValue : Prop) (Run : Cursor → Type*) where
  init : Startup
  /-- The four chronological cursor visits preceding the first compressor pass. -/
  cursor : Cursor
  cursorCost : cost cursor
  slack : clockSlack
  clock : clockValue
  /-- The complete selected execution starting on the final cursor memory. -/
  result : Run cursor

/-- The actual selected calendar on the dynamic directory of this physical group. -/
abbrev VirtualPairs.PaperDescriptor :=
  DescriptorData (StartupResult boot (A).plan lastStage pub addr n base m clk)
    (InitialInterval B base P T cap small b l (initialWidth addr n) pub entry)
    (fun cursor => RAMBuckets.cost Report.probes cursor.interval.source.logs ≤ initialRate B*(P+1))
    (small+3 ≤ cap) (cap+24 = clockAt pub clk CompressedPair.Stage.online)
    (fun cursor => ScheduledTrace.Result res pub (levelWords L : Word ww) (directoryRows L) cap small
      (T*(S.steps+1)*rate+4) E (executeOrigins B f hf T le_rfl X) _
      (nativeReaders (B := B) (f := f) (hf := hf) le_rfl X) []
      cursor.interval.segment.state cursor.interval.segment.memory)

/-- Compile the chosen physical stages at the packed layout. Its shape differs
from the template's allocation shape only in the runtime directory sizes. -/
theorem VirtualPairs.paperDescriptor_of_runs
    (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0))
    (start : InitialLive B f hf (blockRatio u).num (blockRatio u).den addr n base clk
      (paperTerminal B u c labels) pub m hd)
    (control : Schedule.Online.Run.ControlBounds (A).plan small (w := ww))
    (sizes : PrefixLevelScale.Within P n E)
    (passes : LocatedRuns res pub (levelWords L : Word ww) (directoryRows L) cap small rate T P n) :
    Nonempty (V.PaperDescriptor f hf c labels base clk rate pub m) := by
  have active : InitialLive B f hf (blockRatio u).num (blockRatio u).den addr n base clk lastStage pub m hd := by
    rw [paper_terminal_rows]
    exact start
  obtain ⟨init,cursor,cost,slack,clock,⟨out⟩⟩ :=
    V.descriptor_execution f hf base clk rate lastStage pub m hd active data control sizes passes
  refine ⟨⟨init,cursor,cost,slack,clock,?_⟩⟩
  exact cursor.interval.state.symm ▸ out

variable {V f hf c labels base clk rate pub m}
variable (Y : VirtualPairs.PaperDescriptor V f hf c labels base clk rate pub m)

/-- Every descriptor term sequence is one genuine online path on the post-startup RAM. -/
abbrev VirtualPairs.PaperDescriptor.paths : (E).Choices ≃
    StagePaths boot (A).plan lastStage pub clk CompressedPair.Stage.online entry :=
  DescriptorPaths.paths Y.cursor.interval Y.result boot lastStage clk Y.clock Y.slack

theorem VirtualPairs.PaperDescriptor.post (z : (E).Choices) :
    onlinePost (Y.paths z) = writeMemory (Y.result.trace.cut.part z).memory (PairTag.address pub)
      (LiveStageLink.tagWord ww CompressedPair.Stage.terminal) :=
  DescriptorPaths.paths_post Y.cursor.interval Y.result boot lastStage clk Y.clock Y.slack z

/-- Online source-frame proof for reachable prefixes on the physical program. -/
def VirtualPairs.PaperDescriptor.protectedOnline (below : (PairTag.address pub).val < (pub 2).val+6) :
    Protected boot (A).plan lastStage pub clk CompressedPair.Stage.online entry :=
  DescriptorPaths.protectedStage Y.cursor.interval Y.result boot lastStage clk Y.clock below

theorem VirtualPairs.PaperDescriptor.online_word (below : (PairTag.address pub).val < (pub 2).val+6)
    (x : ℕ) (low : x < (pub 2).val+6) : (Y.protectedOnline below).word x :=
  DescriptorPaths.protectedStage_word Y.cursor.interval Y.result boot lastStage clk Y.clock below x low

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
