import OAI.Hierarchy.ProbeFixedWidePrefixProgram
import OAI.Hierarchy.ProtocolRAMPaidWidthReprice
import OAI.Hierarchy.ProtocolRAMCalendarPrefixPages

namespace OAI
/-! # Price all authentic dated reports by reiterating the original width and reserve bills -/
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
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



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
local notation "routes" => stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

open ProbeStage.Native
variable (compile : Event→List PaidWidths.Slice)
local notation "ss" => (events v.mesh).flatMap compile
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss


/-- Each replay makes at most one copy of the paid scan and one of the reserve scan
for a date. Both of these scans occur in the original true settled process. -/
theorem wide_prefix_price :
    v.widePrefixTime h width compile≤(last+2)*v.wideSettledTime h width ss ∧
    text (v.widePrefixBody h width compile)≤(last+2)*text (v.wideSettledBody h width ss) := by
  let wbill:=PaidWidths.clock (old).width rows ss
  let rbill:=19+12*num+160*cnt
  let paid:=PaidWidths.native w rows (TerminalLayout.source page) (old).width ss
  have sinkBanks : (sink).banks = old := rfl
  have origClock : wbill+rbill≤v.wideSettledTime h width ss := by
    unfold wideSettledTime CatalystArchive.terminalTime
    rw [sinkBanks, ReserveUse.clock_eq]
    change PaidWidths.clock (old).width rows ss+(19+12*num+160*cnt)≤_
    omega
  have origText : text paid+218≤text (v.wideSettledBody h width ss) := by
    unfold wideSettledBody CatalystArchive.terminal
    simp only [text_seq,sinkBanks,PrefixReserve.native_text]
    change text (PaidWidths.native w rows (TerminalLayout.source page) (old).width ss)+218≤_
    omega
  have timeLimit : PrefixWidths.time lw (PrefixWidths.prefixRows (events v.mesh) compile) last≤(last+1)*wbill :=
    PrefixWidths.time_prefix_le lw (events v.mesh) compile (old).width last
  have textLimit : text (PrefixWidths.program lw (PrefixWidths.prefixRows (events v.mesh) compile) w last)
      ≤(last+1)*text paid :=
    PrefixWidths.text_prefix_le w lw (events v.mesh) compile (old).width (TerminalLayout.source page) last
  have costLimit : PrefixReserve.cost num (PrefixReserve.publicCount v.mesh decl) last≤(last+1)*rbill :=
    PrefixReserve.cost_le _ _
  constructor
  · calc
      _ ≤ v.wideSettledTime h width ss+((last+1)*wbill+(last+1)*rbill) := by
        unfold widePrefixTime
        exact (Nat.add_assoc ..).le.trans (Nat.add_le_add_left (Nat.add_le_add timeLimit costLimit) _)
      _ = v.wideSettledTime h width ss+(last+1)*(wbill+rbill) := by rw [Nat.mul_add (last+1) wbill rbill]
      _ ≤ v.wideSettledTime h width ss+(last+1)*v.wideSettledTime h width ss :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ origClock) _
      _ = _ := (Nat.add_comm _ _).trans (Nat.succ_mul (last+1) _).symm
  · rw [widePrefixBody,text_seq,text_seq,PrefixReserve.program_text]
    calc
      _ ≤ text (v.wideSettledBody h width ss)+((last+1)*text paid+(last+1)*218) := by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.add_le_add_right textLimit _) _
      _ = text (v.wideSettledBody h width ss)+(last+1)*(text paid+218) := by rw [Nat.mul_add (last+1) (text paid) 218]
      _ ≤ text (v.wideSettledBody h width ss)+(last+1)*text (v.wideSettledBody h width ss) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ origText) _
      _ = _ := (Nat.add_comm _ _).trans (Nat.succ_mul (last+1) _).symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
