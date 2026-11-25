import OAI.Hierarchy.ProbeFixedWideReplayArchive
import OAI.Hierarchy.ProbeFixedWideSignedOutput
import OAI.Hierarchy.ProtocolRAMCalendarPrefixNative

namespace OAI
/-! # Public syntax and cost of settlement and both dated prefix reporters -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

def wideSettledBody (ss : List PaidWidths.Slice) : Procedure w :=
  (Native.subdivisionProgram h D).seq (CatalystArchive.terminal C L routes ((A).endAddress v.mesh) sink (TerminalLayout.source page)
    ss original num cnt supply)

def wideSettledTime (ss : List PaidWidths.Slice) :=
  Native.subdivisionConstant D*2^h+CatalystArchive.terminalTime C L routes sink ss original num cnt supply

variable (compile : Event→List PaidWidths.Slice)
local notation "ss" => (events v.mesh).flatMap compile
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss

/-- Both tables use original calendar order. Inactive rows occupy exactly their
public arities, so the procedure is independent of data fields and input tags. -/
def widePrefixBody : Procedure w :=
  ((v.wideSettledBody h width ss).seq (PrefixWidths.program lw (PrefixWidths.prefixRows (events v.mesh) compile) w last)).seq
    (PrefixReserve.program lr old a (PrefixReserve.publicCount v.mesh decl) supply w last)

def widePrefixTime : ℕ :=
  (v.wideSettledTime h width ss+PrefixWidths.time lw (PrefixWidths.prefixRows (events v.mesh) compile) last)+
    PrefixReserve.cost num (PrefixReserve.publicCount v.mesh decl) last

attribute [local irreducible] CheapCode

set_option maxHeartbeats 1200000 in
theorem widePrefixCheap : CheapCode (v.widePrefixBody h width compile) := by
  let settle := CatalystArchive.terminal C L routes ((A).endAddress v.mesh) sink
    (TerminalLayout.source page) ss original num cnt supply
  let widths := PrefixWidths.program lw (PrefixWidths.prefixRows (events v.mesh) compile) w last
  let reserve := PrefixReserve.program lr old a (PrefixReserve.publicCount v.mesh decl) supply w last
  have paid : CheapCode settle := CatalystArchive.terminal_cheap C L routes ((A).endAddress v.mesh) sink
    (TerminalLayout.source page) ss original num cnt supply
  have readWidths : CheapCode widths := PrefixWidths.cheap lw (PrefixWidths.prefixRows (events v.mesh) compile) last
  have readReserve : CheapCode reserve := PrefixReserve.cheap lr old a (PrefixReserve.publicCount v.mesh decl) supply last
  let boot := Native.subdivisionProgram h D
  exact @cheap_seq w ((boot.seq settle).seq widths) reserve
    (@cheap_seq w (boot.seq settle) widths
      (@cheap_seq w boot settle (Native.subdivision_cheap h D) paid) readWidths) readReserve

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
