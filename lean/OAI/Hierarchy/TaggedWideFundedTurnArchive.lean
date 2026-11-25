import OAI.Hierarchy.ProbeFixedWideLocalRun
import OAI.Hierarchy.ProbeFixedWideCorrectedSpillSource
import OAI.Hierarchy.ProbeFixedWideTerminalFloors

namespace OAI
/-! # The original terminal role tape retained by the priced and unpriced window scans -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU StripDirectory
open scoped Classical BigOperators Fin.CommRing
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


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k)) (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw v.maxBits issues who cj marks)


variable (ell unitCost rom work : ℕ)
local notation "dated" => v.wideDated h width ell unitCost
local notation "tRom" => (dated).romEnd rom
local notation "tWork" => (dated).workEnd work
local notation "limitROM" => v.wideTerminalROMEnd h width bits tRom tWork
local notation "T" => v.wideTerminal h width bits tRom tWork
local notation "board" => v.wideTerminalBoard h width bits tWork
local notation "ceiling" => v.wideTerminalWorkEnd h width bits tWork
local notation "stageExtent" => (board).endAt+3*(board).old
local notation "pubPort" => Public v.sampler h v.W k v.wideJobs
local notation "heads" => fun e (on : 0<counts e) side=>
  (Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side)):pubPort)
local notation "funding" => v.FundedTurnSource h width size M π raw issues who cj marks unique A₀ tRom tWork

/-- Take the `after` and `out` witnesses of `wide_local_run`. Its all-row native archive
read and the old active-role read both survive every subsequent format and prune step.
The ROM words retain their original header address, including on skipped rows. -/
def wide_turn_source_from_local (m seedTerms after out : Memory w)
    {amount : Fin (board).old→ℕ} {portAt : ∀i,0<amount i→Bool→pubPort}
    (keep : ∀a<full,m a=settled a) (funded : full≤work)
    (publicRoom : limitROM≤work) (room : ceiling≤2^w)
    (terminalROM : ∀a,tRom≤a→a<limitROM→
      m a=v.wideTerminalWords h width bits tRom tWork seedTerms a)
    (outLow : ∀a<work,out a=m a) (afterLow : ∀a<work,after a=m a)
    (recorded : ∀a<stageExtent,out a=(board).extendedState (T).stock after a)
    (actual : (board).LiveReads v.sampler amount counts portAt heads out)
    (current : Memory w) (retain : ∀a<ceiling,current a=out a) : funding current := by
  obtain ⟨base,rawWindow,weighted,final,realOld,realNew⟩ :=
    v.wide_terminal_role_floors h width bits tWork room
  have tape : stageExtent≤ceiling := rawWindow.trans (weighted.trans final)
  have workFloor : work≤tWork := by
    simp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,Dated.controlStart,Dated.rolesEnd,endOf]
    omega
  have oldFloor : work≤ceiling := workFloor.trans (base.trans ((Nat.le_add_right _ _).trans tape))
  refine FundedTurnSource.mk (v := v) (h := h) (width := width) (size := size) (M := M)
    (π := π) (raw := raw) (issues := issues) (who := who) (cj := cj) (marks := marks)
    (unique := unique) (A₀ := A₀) (terminalROM := tRom) (terminalWork := tWork) (initial := current)
    after seedTerms ?_ ?_ amount portAt (Board.LiveReads.frame (S := v.sampler) (b := board)
      actual ceiling tape realOld realNew retain) ?_
  · intro a ha
    exact (afterLow a (ha.trans_le funded)).trans (keep a ha)
  · intro a ha
    exact (retain a (ha.trans_le tape)).trans (recorded a ha)
  · intro a left right
    have below := right.trans_le publicRoom
    exact (retain a (below.trans_le oldFloor)).trans ((outLow a below).trans (terminalROM a left right))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
