import OAI.Hierarchy.ProbeFixedWideCorrectedSpillRun

namespace OAI
/-! # Concrete paid register snapshot retained by both variants of the dated spill network -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
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


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
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
variable (horizon : full≤ size) (age : v.wideFundedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
  (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry num width) (card : recordCount v.mesh issues=cnt)
  (who : Fin (recordCount v.mesh issues)→Fin num) (cj : Columns h D×Fin k→Fin num)
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw v.maxBits issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R»:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "ports" => livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "value" => v.wideDatedValue h width bits mid chk issues
local notation "tb" => v.wideTerminalBoard h width bits 0

local notation "bsize" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π v.depth marks (P).catalogue order bsize axis
local notation "ordinal" => (P).catalogue.ordinal v.sampler π v.depth marks order bsize
local notation "embedded" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order bsize
local notation "sparse" => sparseKey v.sampler π v.depth marks (P).catalogue order bsize
  (PurchaseInventory.slotEquiv h N k) axis
local notation "partialRow" => DatedRows.lookup v.sampler π v.depth marks (P).catalogue order bsize names
local notation "direction" => DatedRows.inputSide v.sampler π v.depth marks names
local notation "siteCount" => siteLast h D k+1

variable (ell unitCost first rom oldWork : ℕ)
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "region" => v.wideSpillPage h width bits first
local notation "tape" => v.wideSpillRanks h width bits first
local notation "required" => (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)
local notation "content" => v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork

variable (terminalROM terminalWork : ℕ)
local notation "endDates" => (correct).endAt startAt
local notation "nt" => v.wideTerminal h width bits terminalROM terminalWork
local notation "parentB" => v.wideCorrectedSpillProgram h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "billed" => v.wideCorrectedSpillTicks h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "endAll" => v.wideCorrectedSpillEnd h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "pre" => (correct).preClip oldWork startAt
local notation "post" => fun j=>(baseModel).roleStart oldWork j.succ
local notation "lo" => fun j=>(correct).dateRole startAt j 1
local notation "hiRole" => fun j=>(correct).dateRole startAt j 2
local notation "panel" => v.wideSpillTurnPage h width bits rom terminalROM terminalWork first endDates pre post lo hiRole
local notation "Seat" => ProtocolRAMTurnShelf.Seats (nt).sites (nt).seats
local notation "G" => fun (m : Memory w)=>∀j : Fin last,(panel j).Inputs endDates m

local notation "board" => v.wideTerminalBoard h width bits terminalWork
local notation "stageExtent" => (board).endAt+3*(board).old
local notation "pubPort" => Public v.sampler h v.W k v.wideJobs
local notation "heads" => fun e (on : 0<counts e) side=>
  (Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side)):pubPort)

local notation "funding" => v.FundedTurnSource h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork
local notation "origins" => v.nativeTurnSources h width size M π raw first
attribute [local irreducible] rounds Native.wordBits Nat.pow

/- Generating the dependent projections over field types avoids unfolding the native
   tape arithmetic each time a register is referenced. -/
structure NativeSpillRegisters.FieldTypes where
  fundsType : Type
  originType : Prop
  baselineType : Prop
  boughtType : Prop
  costType : Prop
  radiusType : Prop
  paidHeightType : Prop
  storedType : Prop
  settledLowType : Prop
  romBelowType : Prop
  replayedType : Prop
  terminalFloorType : Prop
  fundedFloorType : Prop
  oldBeforeType : Prop
  gapType : Prop
  wordRoomType : Prop
  rankFrameType : Prop
  roleFrameType : Prop
  writtenFrameType : Prop
  inputsFrameType : Prop
  contentsType : Prop
  shelfType : fundsType → originType → baselineType → boughtType → costType → radiusType →
    paidHeightType → storedType → settledLowType → romBelowType → replayedType → terminalFloorType →
    fundedFloorType → oldBeforeType → gapType → wordRoomType → Prop

structure NativeSpillRegisters.Evidence (spec : NativeSpillRegisters.FieldTypes) where
  funds : spec.fundsType
  origin : spec.originType
  baseline : spec.baselineType
  bought : spec.boughtType
  cost : spec.costType
  radius : spec.radiusType
  paidHeight : spec.paidHeightType
  stored : spec.storedType
  settledLow : spec.settledLowType
  romBelow : spec.romBelowType
  replayed : spec.replayedType
  terminalFloor : spec.terminalFloorType
  fundedFloor : spec.fundedFloorType
  oldBefore : spec.oldBeforeType
  gap : spec.gapType
  wordRoom : spec.wordRoomType
  rankFrame : spec.rankFrameType
  roleFrame : spec.roleFrameType
  writtenFrame : spec.writtenFrameType
  inputsFrame : spec.inputsFrameType
  contents : spec.contentsType
  shelf : spec.shelfType funds origin baseline bought cost radius paidHeight stored settledLow romBelow
    replayed terminalFloor fundedFloor oldBefore gap wordRoom

private def nativeRegisterFieldTypes (initial ranked sch final : Memory w) (inputs : Fin last→Memory w) : NativeSpillRegisters.FieldTypes where
  fundsType := funding initial
  originType := origins initial sch
  baselineType := Whole.Reconciliation sink original supply who dur ord ci cj archive
  boughtType := ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
    ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val)
  costType := ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w
  radiusType := M=v.radius
  paidHeightType := v.wideSpillPaidHeight≤h
  storedType := ∀i,i<(A).endAddress v.mesh→initial i=chk i
  settledLowType := ∀a<full,initial a=settled a
  romBelowType := v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork
  replayedType := v.wideReplayedTurnBase h width ss≤terminalWork
  terminalFloorType := v.wideTerminalWorkEnd h width bits terminalWork≤first
  fundedFloorType := full≤first
  oldBeforeType := oldWork≤first
  gapType := 3*(baseModel).romEnd rom+2≤oldWork
  wordRoomType := endDates<2^w
  rankFrameType := ∀a,a<first → ranked a=initial a
  roleFrameType := ∀a,a<startAt→sch a=ranked a
  writtenFrameType := ∀a,a<endDates→final a=sch a
  inputsFrameType := ∀j a,a<first→inputs j a=initial a
  contentsType := content inputs ranked final
  shelfType funds origin baseline bought cost radius paidHeight stored settledLow romBelow
    replayed terminalFloor fundedFloor oldBefore gap wordRoom :=
    ∀j (f : Fin 5) (seat : Seat),
    final ((panel j).base+f.val*((nt).sites*(nt).seats)+seat.1.val*(nt).seats+seat.2.val)=
    (v.fundedSpillAccess h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
      ell unitCost first rom oldWork terminalROM terminalWork initial sch funds origin baseline bought cost radius paidHeight
      stored settledLow romBelow replayed terminalFloor fundedFloor oldBefore gap wordRoom j).word f seat

attribute [reducible] nativeRegisterFieldTypes
local notation "regSpec" => v.nativeRegisterFieldTypes h width size M π raw horizon age budget small operandAge issues card who cj
  marks unique A₀ ell unitCost first rom oldWork terminalROM terminalWork initial ranked sch final inputs
/-- Physical register and ROM witnesses from the invocation that emitted the five words.
The four data types and every address below are the ones of the executed procedure. -/
abbrev NativeSpillRegisters (initial ranked sch final : Memory w) (inputs : Fin last→Memory w) : Type := NativeSpillRegisters.Evidence regSpec
namespace NativeSpillRegisters
variable {v h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀ ell unitCost first rom oldWork terminalROM terminalWork} {initial ranked sch final : Memory w} {inputs : Fin last→Memory w}
    (file : v.NativeSpillRegisters h width size M π raw horizon age budget small operandAge issues card who cj
  marks unique A₀ ell unitCost first rom oldWork terminalROM terminalWork initial ranked sch final inputs)
abbrev mk := @NativeSpillRegisters.Evidence.mk regSpec
abbrev rec := @NativeSpillRegisters.Evidence.rec regSpec
abbrev recOn := @NativeSpillRegisters.Evidence.recOn regSpec
abbrev casesOn := @NativeSpillRegisters.Evidence.casesOn regSpec
abbrev funds := NativeSpillRegisters.Evidence.funds file
abbrev origin := NativeSpillRegisters.Evidence.origin file
abbrev baseline := NativeSpillRegisters.Evidence.baseline file
abbrev bought := NativeSpillRegisters.Evidence.bought file
abbrev cost := NativeSpillRegisters.Evidence.cost file
abbrev radius := NativeSpillRegisters.Evidence.radius file
abbrev paidHeight := NativeSpillRegisters.Evidence.paidHeight file
abbrev stored := NativeSpillRegisters.Evidence.stored file
abbrev settledLow := NativeSpillRegisters.Evidence.settledLow file
abbrev romBelow := NativeSpillRegisters.Evidence.romBelow file
abbrev replayed := NativeSpillRegisters.Evidence.replayed file
abbrev terminalFloor := NativeSpillRegisters.Evidence.terminalFloor file
abbrev fundedFloor := NativeSpillRegisters.Evidence.fundedFloor file
abbrev oldBefore := NativeSpillRegisters.Evidence.oldBefore file
abbrev gap := NativeSpillRegisters.Evidence.gap file
abbrev wordRoom := NativeSpillRegisters.Evidence.wordRoom file
abbrev rankFrame := NativeSpillRegisters.Evidence.rankFrame file
abbrev roleFrame := NativeSpillRegisters.Evidence.roleFrame file
abbrev writtenFrame := NativeSpillRegisters.Evidence.writtenFrame file
abbrev inputsFrame := NativeSpillRegisters.Evidence.inputsFrame file
abbrev contents := NativeSpillRegisters.Evidence.contents file
abbrev shelf := NativeSpillRegisters.Evidence.shelf file
end NativeSpillRegisters


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
