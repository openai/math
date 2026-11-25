import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.ProbeFixedWidePrefixProgram
import OAI.Hierarchy.ProtocolRAMCatalystArchiveRun
import OAI.Hierarchy.ProbeStageCompactRun

namespace OAI
/-! # Native paid controller and clock after an arbitrary subdivision -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
variable (bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
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
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
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
local notation "ss" => v.widePaidSlices h width bits
local notation "compile" => v.wideEventSlices h width bits
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss
local notation "n" => PrefixReserve.publicCount v.mesh decl
local notation "subs" => PrefixWidths.prefixRows (events v.mesh) compile

def wideAfterCT (bits : ℕ) :=
  CatalystArchive.terminal C L routes ((A).endAddress v.mesh) sink (TerminalLayout.source page) (v.widePaidSlices h width bits)
    original num cnt supply
def wideAfterCTTime (bits : ℕ) :=
  CatalystArchive.terminalTime C L routes sink (v.widePaidSlices h width bits) original num cnt supply

def wideFromCT (boot : Procedure w) :=
  (((boot.seq (v.wideAfterCT h width bits)).seq (PrefixWidths.program lw subs w last)).seq
    (PrefixReserve.program lr old a n supply w last))

def wideFromCTTime (t : ℕ) :=
  (t+v.wideAfterCTTime h width bits+PrefixWidths.time lw subs last)+PrefixReserve.cost num n last

/-- Fixed parent-level program. Its input has both signed private words and the
additional fixed ROM suffix ahead of the later registered gate records. -/
def wideCountedPrefix := v.wideFromCT h width bits (Native.Compact.subdivision h D)
def wideCountedTime := v.wideFromCTTime h width bits (Native.Compact.constant D*2^h)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
