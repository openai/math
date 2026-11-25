import OAI.Hierarchy.TaggedWideScatter
import OAI.Hierarchy.TaggedWideInputInverse
import OAI.Hierarchy.ProbeFixedWideCountedCode
import OAI.Hierarchy.TaggedWireOldBoardNative
import OAI.Hierarchy.ProtocolRAMTurnRankProgram
import OAI.Hierarchy.ProtocolRAMTurnShelfProgram
import OAI.Hierarchy.ProtocolRAMFrozenFormat
import OAI.Hierarchy.TaggedWideNativeSeries
import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # Two literal native programs for the same finite calendar and purchased catalogue -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMFrozenWindow ProbeStage.CoreBoard.HistoryRoles
open scoped Classical BigOperators

/-- Addresses shared by the endpoint classifier, the original-order amount prefix, and
the seven-word-to-five-word itinerary pass of the settled terminal matrix. -/
structure Terminal where
  board : RoleProgram.Board
  stock : RoleProgram.Inventory
  rankStart : ℕ
  edges : ℕ
  routeEntries : ℕ
  accounts : RouteSettlement.Banks
  turns : ℕ
  sites : ℕ
  seats : ℕ
  header : ℕ
  headerBits : ℕ
  startColumn : ℕ
  source : ℕ
  sourceBits : ℕ
  rom : ℕ
  romBits : ℕ
  base : ℕ
  scratch : ℕ
  sink : ℕ
  columns : ProtocolRAMTurnChart.Data
  heads : Bank
  walk : ProtocolRAMTurnItinerary.Banks

def Terminal.code (t : Terminal) (W : ℕ) (paidAtLast : Bank) : Procedure W :=
  ((t.board.extended t.stock W).seq
    (ProtocolRAMTurnReplayed.procedure W t.rankStart t.edges t.routeEntries t.accounts paidAtLast)).seq
    (ProtocolRAMChronologicalShelf.program W t.turns t.sites t.seats t.header t.headerBits t.startColumn t.source
      t.sourceBits t.rom t.romBits t.base t.scratch t.sink t.columns t.heads t.walk)

def Terminal.ticks (t : Terminal) (paidAtLast : Bank) :=
  (t.board.extendedTime t.stock+ProtocolRAMTurnReplayed.time t.rankStart t.edges t.routeEntries t.accounts paidAtLast)+
    (72+6096*t.turns+30*(t.sites*t.seats))

structure Layout (m : ℕ) where
  tagScratch : ℕ
  scatterLast : ℕ
  scatter : Fin (scatterLast+1) → Scatter
  terminal : Terminal
  windows : Fin (m+1) → ProtocolRAMFrozenWindow.Format
  inputs : Fin (m+1) → ProtocolRAMFrozenWindow.Inputs
  floor : ℕ
  pruneScratch : ℕ
  pruneRows : ℕ
  lengthCode : ℕ
  threshold : ℕ
  ends : Bank
  metrics : Bank
  layers : Bank

variable {m : ℕ} (l : Layout m)

def Layout.need (i : Fin (m+1)) := (l.windows i).window.stop 0
def Layout.windowBase (i : Fin (m+1)) := WindowSeries.start l.floor l.need i
def Layout.banks (W : ℕ) (i : Fin (m+1)) := (l.windows i).phase W (l.windowBase i) (l.inputs i)
def Layout.windowTicks (i : Fin (m+1)) := (l.windows i).clock (l.windowBase i) (l.inputs i)
def Layout.localCode (W : ℕ) (paidAtLast : Bank) : Procedure W :=
  (ProcedureBank.program l.scatterLast (fun i=>(l.scatter i).code W)).seq (l.terminal.code W paidAtLast)
def Layout.localTicks (paidAtLast : Bank) := (∑i,(l.scatter i).ticks)+l.terminal.ticks paidAtLast
def Layout.prune := PruneFlag.term l.ends l.metrics l.layers l.lengthCode

def Layout.finish {W : ℕ} (prefixCode : Procedure W) (paidAtLast : Bank) : Procedure W :=
  (((prefixCode.seq (l.localCode W paidAtLast)).seq (ProcedureBank.program m (l.banks W)))).seq
    (SumScores.procedure W l.pruneScratch l.pruneRows l.threshold l.prune)

def Layout.ticks (first : ℕ) (paidAtLast : Bank) :=
  ((first+l.localTicks paidAtLast)+(∑i,l.windowTicks i))+(4+(l.pruneRows+1)*(42+2*l.prune.work))

end Hierarchy.ProtocolRAM.Calendar.WideCPU

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ) {m : ℕ} (l : WideCPU.Layout m)
local notation "D" => 2^v.W
local notation "W" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "C" => v.wideSignedChart h width (v.fixedTerminalStock P h width)
local notation "A" => v.privateArena P h width
local notation "compileEvent" => v.wideEventSlices h width bits
local notation "prefixCode" => v.wideCountedPrefix h width bits
local notation "paidAtLast" => (v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length

/-- Program texts are chosen jointly before both the exposed permutation tag and the
private histogram word. Every suffix instruction is a concrete RAM scan, indexed
write, chronological itinerary, or purchased compaction-format publisher. -/
def widePrograms : Procedure W × Procedure W :=
  let inv:=TagInverse.program W h l.tagScratch
  (inv.seq ((Native.Compact.subdivision h D).seq (checked C ((A).endAddress v.mesh))),
   inv.seq (l.finish prefixCode paidAtLast))

def wideProgramTicks : ℕ × ℕ :=
  (TagInverse.ticks h+(Native.Compact.constant D*2^h+checkedCost C),
    TagInverse.ticks h+l.ticks (v.wideCountedTime h width bits) paidAtLast)

theorem widePrograms_first : (v.widePrograms h width bits l).1=
    (TagInverse.program W h l.tagScratch).seq ((Native.Compact.subdivision h D).seq (checked C ((A).endAddress v.mesh))) := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
