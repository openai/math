import OAI.Hierarchy.TaggedWireNativeReport
import OAI.Hierarchy.TaggedWireWidePaidGroups
import OAI.Hierarchy.ProbeFixedWidePaidReadout
import OAI.Hierarchy.TaggedWideWindowWidthCap
import OAI.Hierarchy.ProbeFixedMeasuredBudget
import OAI.Hierarchy.TaggedWideMaskWord
import OAI.Hierarchy.TaggedWideWindowMask
import OAI.Hierarchy.TaggedWideFullGates
import OAI.Hierarchy.TaggedWidePrunePrices
import OAI.Hierarchy.ProtocolRAMPruneActive
import OAI.Hierarchy.TaggedWideEmissionFrame
import OAI.Hierarchy.TaggedWideWindowRejected
import OAI.Hierarchy.TaggedWideWindowReady
import OAI.Hierarchy.TaggedWideWindowCutImage
import OAI.Hierarchy.TaggedWidePrintedStage

namespace OAI
/-! # Positive cuts on the original funded terminal report -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
open Tagged Tagged.WideStack
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


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
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
local notation "last" => (events v.mesh).length

local notation "pair" => pairKeys (Columns h D) k
private def fundedCutMarksAt : Marks h v.W k v.wideJobs :=
  v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
    (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
local notation "days" => fundedCutMarksAt v h width size π raw

private def fundedCutOriginalOrder : Catalogue v.sampler π v.depth days ↪ Fin rows :=
  (P).catalogue.ordinal v.sampler π v.depth days order rfl
local notation "publicOrder" => fundedCutOriginalOrder v h width size π raw

private def fundedCutSourceOrder : Catalogue v.sampler π v.depth days → Fin rows :=
  (P).catalogue.original v.sampler π v.depth days order (v.wideBoughtOrdinal h width π days)

private def cutAlignmentAt (rawRows : Fin rows → ProtocolRAMEmit.Row) :=
  Alignment (P).catalogue v.sampler π v.depth days v.radius rawRows (fun e => (rawRows e).width) publicOrder
private def cutSourceAlignmentAt (rawRows : Fin rows → ProtocolRAMEmit.Row) :=
  Alignment (P).catalogue v.sampler π v.depth days v.radius rawRows (fun e => (rawRows e).width)
    (fundedCutSourceOrder v h width size π raw)
private def cutAgreementAt (rawRows : Fin rows → ProtocolRAMEmit.Row)
    (geometry : ProtocolRAMEmit.Geometry (boardLayout h D k width supply) v.radius 1 rawRows)
    (aligned : cutAlignmentAt v h width size π raw rawRows) : Prop :=
  (aligned : Alignment _ _ _ _ _ _ _ _ _).geometry width supply = geometry
private def cutInvoiceAt (rawRows : Fin rows → ProtocolRAMEmit.Row) : Prop :=
  TermBudget p q Q Λ (2^h) width v.radius (∑_j : Columns h D×Fin k,supply)
    (scaleOf v.sampler π v.depth days) (fun e=>(lenCode v.sampler π v.depth days v.radius e:ℝ))
    (fun e=>((rawRows (publicOrder e)).width:ℝ)/width)
private def cutApertureAt (rawRows : Fin rows → ProtocolRAMEmit.Row) :=
  ∀ _ : 0 < width,
    {j : Fin rows // 0 < ProtocolRAMReportedPorts.pieces
      (atScale ((P).catalogue.transport order) (fun _ => 0) 0 rawRows) width j} × Bool ↪ Fin (directory).groups × Fin H
private def cutOwnerAt (rawRows : Fin rows → ProtocolRAMEmit.Row) (mapping : cutApertureAt v h width rawRows) : Prop :=
  ∀ hw i side, ((mapping hw) (i,side)).1.val = (rawRows i.val).group
private def cutApertureAgreementAt (rawRows : Fin rows → ProtocolRAMEmit.Row) (mapping : cutApertureAt v h width rawRows)
    (aligned : cutSourceAlignmentAt v h width size π raw rawRows) : Prop :=
  ∀ (exclusive : Exclusive days) (hw : 0<width), mapping hw =
    (CatalogueRows.Alignment.location v.sampler π v.depth days exclusive (P).catalogue order
      (v.wideBoughtOrdinal h width π days) rawRows aligned (fun _=>0) 0 width hw).trans
        (ReportSockets.packed directory)

section
attribute [local irreducible] widePlacement CatalogueRows.Board.rows Native.wordBits Nat.pow ProbeStage.rounds boardLayout

/-- The calibrated purchase reads the board emitted by the funded reporter, including
the actual integer widths at its original ordinals. -/
structure FundedCutRows
    (rawRows : Fin rows→ ProtocolRAMEmit.Row)
    (geometry : ProtocolRAMEmit.Geometry (boardLayout h D k width supply) v.radius 1 rawRows)
    (unitCost : ℕ) where
  alignment : cutAlignmentAt v h width size π raw rawRows
  sameGeometry : cutAgreementAt v h width size π raw rawRows geometry alignment
  invoice : cutInvoiceAt v h width size π raw rawRows
  originalId : ∀j, (rawRows j).link = j.val
  widthBound : ∀j, (rawRows j).width ≤ v.wideInstalledCap unitCost * width
  aperture : cutApertureAt v h width rawRows
  owner : cutOwnerAt v h width rawRows aperture
  sourceAlignment : cutSourceAlignmentAt v h width size π raw rawRows
  aperture_eq : cutApertureAgreementAt v h width size π raw rawRows aperture sourceAlignment

end

private abbrev fundedCutCost :=
  ∀e : Fin rows, PaidWidths.total ss chk e + (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : fundedCutCost v h width size π raw)
private abbrev fundedCutDates := Dates C mid L pay num width

variable {dates : fundedCutDates v h width size π raw} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
private def fundedCutEntries (entries : fundedCutDates v h width size π raw) : Attempt → Entry num width :=
  CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay)
    (count := num) (payload := width) entries
local notation "issues" => fundedCutEntries v h width size π raw dates

private def fundedCutSites (entries : fundedCutDates v h width size π raw) (positive : 0 < num) :
    Fin (recordCount (count := num) (payload := width) v.mesh (fundedCutEntries v h width size π raw entries)) → Fin num :=
  CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh
    (fundedCutEntries v h width size π raw entries) positive chk
local notation "who" => fundedCutSites v h width size π raw dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "nativeRows" => (sink).terminalRows closed ord ci (fun j=>(pair j).val)
private abbrev fundedCutReceipt (observed : fundedCutDates v h width size π raw) (positive : 0 < num) :=
  let entries := fundedCutEntries v h width size π raw observed
  let sites := fundedCutSites v h width size π raw observed positive
  Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh entries) (count := num) («w» := w) sink original supply sites
    (CatalystArchive.debit (count := num) (payload := width) v.mesh entries) ord ci pair archive

private abbrev fundedCutAlignment (observed : fundedCutDates v h width size π raw) (positive : 0 < num) :=
  v.WideFundedAlignment h width size bits π raw (fundedCutSites v h width size π raw observed positive)
    (CatalystArchive.debit (count := num) (payload := width) v.mesh (fundedCutEntries v h width size π raw observed)) (fun j=>(pair j).val)

variable (unitCost : ℕ)

/-- Preserving the original ordinal spelling changes only the proof naming a live row.
Its endpoints, geometry, widths and positive identity on the native board are untouched. -/
def wide_report_cut_rows
    (receipt : fundedCutReceipt v h width size π raw dates pos)
    (names : fundedCutAlignment v h width size π raw dates pos)
    (invoice : TermBudget p q Q Λ (2^h) width v.radius (∑_j : Columns h D×Fin k,supply)
      (scaleOf v.sampler π v.depth days) (fun e=>(lenCode v.sampler π v.depth days v.radius e:ℝ))
      (fun e=>(receipt.originalWidth (publicOrder e):ℝ)/width))
    (ids : v.WideFundedRowIds h width size bits π raw who dur (fun j=>(pair j).val))
    (owners : v.WideFundedOwners h width size bits π raw who dur (fun j=>(pair j).val))
    (paidCap : ∀j,(nativeRows j).width≤ v.wideInstalledCap unitCost*width) :
    v.FundedCutRows h width size π raw (v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates := dates) (pos := pos) receipt names).rows
      (v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates := dates) (pos := pos) receipt names).geometry unitCost := by
  let oldNames:=names.1.some
  let newNames : Alignment (P).catalogue v.sampler π v.depth days v.radius nativeRows
      (fun e=>(nativeRows e).width) publicOrder :=
    ⟨oldNames.ident, fun i =>
      (congrFun (v.wide_funded_original h width size bits π raw) (oldNames.ident i)).symm.trans (oldNames.original i),
      oldNames.joins, oldNames.metric⟩
  letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  have exclusive : Exclusive days := by apply v.paid_days_exclusive
  let aperture (hw : 0< width) := (CatalogueRows.Alignment.location v.sampler π v.depth days exclusive
    (P).catalogue order (v.wideBoughtOrdinal h width π days) nativeRows oldNames (fun _=>0) 0 width hw).trans
      (ReportSockets.packed directory)
  exact ⟨newNames,rfl,invoice,ids,paidCap,aperture,(fun hw=>owners exclusive oldNames hw),oldNames,fun _ _=>rfl⟩

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- Recover the dates from the reconciliation's actual count of issued records. -/
open Lean Elab Term in
local elab "fundedCutReportDates " cert:ident : term => do
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rowCountExpr := reconciliation.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let count ← Meta.whnf rowCountExpr
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issuedExpr ← Meta.whnf count.getAppArgs.back!
  unless issuedExpr.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issuedExpr.getAppArgs.back!





end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "ports" => WideMemory.H x.h v.W k jobs
local notation "dir" => WideMemory.dir x.h v.W k jobs
local notation "order" => v.wideOrder x.h x.w
local notation "positive" => (b).transport order
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (kept : geometry.links.Keep (2^x.h)) (lanesFit : v.wideInstalledCap unitCost≤2^ell)
local notation "anchor" => (FundedCutRows.aperture actual) x.formats.2.1
/-- A socket outside the reported support occupies zero bits and therefore has no
observable endpoint. On support the owner is the actual packed physical endpoint. -/
def FundedCutRows.port (side : Bool) (j : Fin (b).rows) : Fin ports :=
  if hj : 0< pieces (atScale positive (fun _=>0) 0 raw) x.w j
    then (anchor (⟨j,hj⟩,side)).2 else ⟨0,Nat.two_pow_pos _⟩

local notation "port" => FundedCutRows.port v x tapeSize π input unitCost raw geometry actual

theorem FundedCutRows.port_read (i : {j : Fin (b).rows // 0< pieces (atScale positive (fun _=>0) 0 raw) x.w j})
    (side : Bool) : (anchor (i,side)).2=port side i.val := by
  simp only [FundedCutRows.port,dite_eq_left i.property]

include actual in
/-- Each positive original edge occurs in its native dyadic class. Its measured
group fits the physical table because the original live socket already belongs
to that exact packed group. -/
theorem FundedCutRows.cover (i : Fin (b).rows) (on : positive i) (occupied : 0<(raw i).width) :
    ∃t : Fin (m+1), (geom).index t=(v.W,widthIndex m ((raw i).width/(x.w:ℝ))) ∧
      (raw i).group<(dir).groups := by
  have divisor : (0:ℝ)< x.w := by exact_mod_cast x.formats.2.1
  have atRow : 0< pieces (atScale positive (fun _=>0) 0 raw) x.w i := by
    unfold pieces TaggedShorterBudget.copies atScale
    simp only [on,true_and,ite_true]
    exact Nat.ceil_pos.mpr (div_pos (Nat.cast_pos.mpr occupied) divisor)
  refine ⟨activeType m ((raw i).width/(x.w:ℝ)),rfl,?_⟩
  exact ((FundedCutRows.owner actual) x.formats.2.1 ⟨i,atRow⟩ false) ▸ (anchor (⟨i,atRow⟩,false)).1.isLt

/-- Install the two actual bought compactors at every dyadic class, using the measured
widths, the hardware-reported IDs, and the price of this same kept computation. -/
def FundedCutRows.printed : Leaf.PrintedStage.Family F (dir).groups ports (2^ell) x.w m
    (fun _=>atScale positive (fun _=>0) 0 raw) := by
  intro t
  apply v.printed_installed m ell short v.stage_positive prices pricePos x t (buy t)
    groupsFit (metadata t) π (b) _ order rfl raw _ (FundedCutRows.alignment actual) (fun _=>rfl) reserve (FundedCutRows.invoice actual)
    _ (FundedCutRows.originalId actual) (fun j=>((FundedCutRows.widthBound actual) j).trans (Nat.mul_le_mul_right x.w lanesFit))
    port anchor ((FundedCutRows.owner actual) x.formats.2.1) (FundedCutRows.port_read v x tapeSize π input unitCost raw geometry actual)
  exact (congrArg (fun shape : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw =>
    shape.links.Keep (2^x.h)) (FundedCutRows.sameGeometry actual)).mpr kept

/-- The receipt labels every original positive edge with its actual public stage.
Both endpoints and all untouched private fields keep the installed bank's numbering. -/
def FundedCutRows.installed : ∀t:Fin (m+1), Leaf.Installed F (dir).groups ports (2^ell) x.w m
    ((geom).index t).2 (atScale positive (fun _=>v.W) ((geom).index t).1 raw) :=
  Leaf.PrintedStage.atStage v.W positive raw
    (FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
      prices pricePos buy groupsFit metadata kept lanesFit)

section Observed
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites ProtocolRAMSupergroupDirectory
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "buffer" => v.wideInstalledCap unitCost
local notation "rom" => v.wideInstalledRoot x
local notation "gr" => v.wideGroupROM x dated v.maxBits rom
local notation "words" => v.wideWindowWords («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom
local notation "dst" => TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
local notation "oldRows" => atScale positive (fun _=>0) 0 raw
local notation "s" => FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "real" => FundedCutRows.installed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
variable (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "gates" => v.wideFullGates x m ell short u δ ξ unitCost lim
local notation "paidCPU" => (gates).2
local notation "aperture" => v.wide_full_end x m ell short u δ ξ unitCost lim
/-- Both full signed gates use the real control-height grid, including the
appended spill and ballot program at its final observation extent. -/
theorem wideFullGates_word_room (large : v.programRoomHeight≤ x.h) :
    (gates).1.W+1≤4*(gates).1.m ∧ (paidCPU).W+1≤4*(paidCPU).m := by
  have smallWord : W+1≤4*x.h := by
    rw [Native.wordBits_linear]
    unfold programRoomHeight at large
    omega
  have height (rows : ℕ) : x.h≤Tagged.controlHeight x.h rows := by
    have le := Nat.clog_mono_right 2 (le_max_left (2^x.h) rows)
    simpa only [Tagged.controlHeight, Nat.clog_pow 2 x.h (by decide)] using le
  exact ⟨smallWord.trans (Nat.mul_le_mul_left 4 (height _)),
    smallWord.trans (Nat.mul_le_mul_left 4 (height _))⟩

include lim in
/-- The appended rank tape has a nonempty zero bank after the pruning
flag. Its last address bounds the strict word room of the old score scan. -/
theorem wideFullGates_prune_room :
    (l).pruneScratch+((l).pruneRows+1)<2^W := by
  let start:=(l).pruneScratch+(l).pruneRows+1
  let tape:=v.wideSpillRanks x.h x.w v.maxBits start
  let first:=v.wideSpillRankEnd x.h x.w v.maxBits start
  let z:=v.wideSpillDates x.h x.w ell unitCost v.maxBits start
  have beyond : start< first := by
    change start< start+tape.zero.size+(events v.mesh).length*tape.stride
    have nonempty : 0< tape.zero.size:=Nat.two_pow_pos _
    omega
  have sheets : first≤ z.endAt first := by
    unfold WideCPU.SpillDates.endAt WideCPU.Dated.maskStart WideCPU.Dated.controlStart
      WideCPU.Dated.rolesEnd WideCPU.SpillDates.roleRoot WideCPU.endOf
    omega
  let tapeEnd:=v.wideInstalledSize x m ell unitCost dated
  let last:=v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits rom tapeEnd
    ((dated).romEnd rom) ((dated).workEnd tapeEnd) start
  have final : z.endAt first≤ last := Nat.le_add_right _ _
  have within : last≤2^W:=(le_max_right start last).trans lim.upper
  have := beyond.trans_le (sheets.trans (final.trans within))
  simpa only [start,Nat.add_assoc] using this

attribute [local irreducible] Native.wordBits Nat.pow

variable (large : purchaseWordHeight v.W k jobs ell≤ x.h)
local notation "wordBits" => v.wideInstalledCap unitCost*x.w
include actual in
theorem FundedCutRows.masked_width (j : Fin (b).rows) : (oldRows j).width≤ wordBits := by
  change (if positive j ∧ (0:ℕ)=0 then (raw j).width else 0)≤ _
  split <;> first | exact (FundedCutRows.widthBound actual) j | exact Nat.zero_le _
local notation "wrap" => (show (l).floor<2^W from by
  have before : (l).floor≤(l).pruneScratch := Nat.le_add_right _ _
  have endAt := lim.original.upper
  omega)
local notation "fit" t => v.wideWindow_limits x m ell short u δ ξ unitCost dated large wrap t oldRows
  (fun j => show (raw j).link=j.val from FundedCutRows.originalId actual j) (FundedCutRows.masked_width v x tapeSize π input unitCost raw geometry actual)
variable (mem before initial out : Memory W)
  (retained : ∀j,gr≤ j → j< gr+2*span (dir).groups → before j=words mem j)
  (reported : ∀j,dst≤ j → j< dst+9*(b).rows → before j=ProtocolRAMEmit.emitted dst raw initial j)
local notation "rowsFit" => v.wideWindow_rows_fit x m ell short u δ ξ unitCost dated wrap
local notation "active" => fun i hi=> ((FundedCutRows.owner actual) x.formats.2.1 ⟨i,hi⟩ false) ▸ (anchor (⟨i,hi⟩,false)).1.isLt
local notation "group" t => fun j _=>v.wideWindow_owner_read («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom
  t raw initial before reported rowsFit j
variable (portWords : ∀t side (j:ProtocolRAMPackedPlacement.Live oldRows x.w),
  (if side then ((l).inputs t).right else ((l).inputs t).left).read before (j.val.val:Word W)=
    ((port side j.val).val*2^ell:ℕ))
local notation "live" t => v.wideCutAnchor x m ell short u δ ξ buffer dated v.maxBits rom t mem before
  oldRows (fit t) (s t) retained active (group t) (portWords t)
local notation "boughtCell" t:arg j:arg => ∃q,((l).windows t).address ((l).windowBase t) q=j
local notation "boughtValue" t:arg j:arg word:arg => ∀q,((l).windows t).address ((l).windowBase t) q=j →
  word=(live t).word oldRows q

/-- The four native observations used by an installed cut and its binary mask.
The input memory contains the original immutable words and the stage-entry
memory contains the actual dated mask and two slot banks. -/
structure FundedCutRows.WindowReceipt : Prop where
  directory : ∀j, gr ≤ j → j < gr+2*span (dir).groups → before j=words mem j
  emitted : ∀j, dst ≤ j → j < dst+9*(b).rows → before j=ProtocolRAMEmit.emitted dst raw initial j
  slotsAt : ∀t side (j : ProtocolRAMPackedPlacement.Live oldRows x.w),
    (if side then ((l).inputs t).right else ((l).inputs t).left).read before (j.val.val:Word W)=
      ((port side j.val).val*2^ell:ℕ)
  terminal : ∀ ok : geometry.links.Keep (2^x.h),∀t q,
    out (((l).windows t).address ((l).windowBase t) q)=
      (v.wideCutAnchor x m ell short u δ ξ buffer dated v.maxBits rom t mem before oldRows (fit t)
        (FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
          prices pricePos buy groupsFit metadata ok lanesFit t) directory active
        (fun j _=>v.wideWindow_owner_read («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom t raw initial
          before emitted rowsFit j) (slotsAt t)).word oldRows q


open ThreeFlat.RAM PhysicalProcedure

section NativeWindows
variable (imageROM : ∀t addr,((l).windows t).rom≤ addr → addr<((l).windows t).adviceEnd →
    @Eq (Word W) (before addr) (words mem addr))
  (masked : ∀t (j:Fin (b).rows),((l).inputs t).width.read before ((3*j.val:ℕ):Word W)=
    ((oldRows j).width:Word W))

include imageROM masked

/-- The actual ROM and masked-width bank prepare one installed format on the
memory left by all earlier formats. Its outputs are the words of both purchased
endpoint orders. -/
theorem FundedCutRows.window_step (t : Fin (m+1)) (current : Memory W)
    (low : ∀j<(l).floor,current j=before j) :
    ∃after : Memory W,((l).banks W t).Exec current after ((l).windowTicks t) ∧
      (∀j : ℕ,(boughtCell t j) → ∀q,((l).windows t).address ((l).windowBase t) q=j →
        @Eq (Word W) (after j) ((live t).word oldRows q)) ∧
      ∀j<(l).windowBase t,after j=current j := by
  have area : (l).pruneScratch<2^W := by
    have endAt : (l).pruneScratch+(l).pruneRows+1≤2^W:=lim.original.upper
    exact (Nat.lt_succ_of_le (Nat.le_add_right _ _)).trans_le endAt
  exact v.wideCutAnchor_step x m ell short u δ ξ buffer dated v.maxBits rom
    t mem before oldRows (fit t) (s t) retained active (group t) (portWords t)
    (v.wideWindow_resident («W» := W) x m ell short u δ ξ unitCost dated wrap t)
    (v.wideWindow_ready («W» := W) x m ell short u δ ξ unitCost dated area t)
    (v.wideWindow_input_words («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom t
      mem before oldRows (fit t) (imageROM t) (masked t)) current low

/-- Run the genuine indexed loop for all dyadic classes. Every word has its
original physical address, including the rows of unoccupied slots. -/
theorem FundedCutRows.window_run :
    ∃after : Memory W,(ProcedureBank.program m ((l).banks W)).Exec before after (∑t,(l).windowTicks t) ∧
      (∀t q,after (((l).windows t).address ((l).windowBase t) q)=(live t).word oldRows q) ∧
      ∀j<(l).floor,after j=before j := by
  obtain ⟨after,exec,table,frame⟩:=WindowSeries.run («W» := W) (l).floor (l).need ((l).banks W)
    (l).windowTicks before (fun t j=>boughtCell t j) (fun t j word=>boughtValue t j word)
    (by rintro t _ ⟨q,rfl⟩; exact ((l).windows t).cell_bound _ q)
    (fun t current low=>FundedCutRows.window_step v x tapeSize π input m ell short unitCost
      raw geometry actual prices pricePos buy groupsFit metadata kept lanesFit lim large mem before
      initial retained reported portWords imageROM masked t current low)
  exact ⟨after,exec,fun t q=>table t _ ⟨q,rfl⟩ q rfl,frame⟩
include actual lim large retained reported portWords lanesFit in
/-- Executing the same installed code needs the port injection and row tariff
for every admitted history. These imply safety even when pruning rejects the
history and the two priced cut semantics are unavailable. -/
theorem FundedCutRows.window_run_all :
    ∃after : Memory W,(ProcedureBank.program m ((l).banks W)).Exec before after (∑t,(l).windowTicks t) ∧
      ∀j<(l).floor,after j=before j := by
  have area : (l).pruneScratch<2^W := by
    have endAt : (l).pruneScratch+(l).pruneRows+1≤2^W:=lim.original.upper
    exact (Nat.lt_succ_of_le (Nat.le_add_right _ _)).trans_le endAt
  have coverPieces (i : Fin (b).rows) : pieces oldRows x.w i≤2^ell := by
    have width := (FundedCutRows.masked_width v x tapeSize π input unitCost raw geometry actual i).trans
      (Nat.mul_le_mul_right x.w lanesFit)
    unfold pieces TaggedShorterBudget.copies
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast x.formats.2.1 : (0:ℝ)< x.w)).mpr
    exact_mod_cast width
  obtain ⟨after,exec,_,frame⟩:=WindowSeries.run («W» := W) (l).floor (l).need ((l).banks W)
    (l).windowTicks before (fun _ _=>False) (fun _ _ _=>True) (by simp) (by
      intro t current low
      obtain ⟨result,ran,unchanged⟩:=v.wideCutAnchor_unpriced_step x m ell short u δ ξ buffer dated v.maxBits rom
        t mem before oldRows (fit t) port anchor ((FundedCutRows.owner actual) x.formats.2.1)
        (FundedCutRows.port_read v x tapeSize π input unitCost raw geometry actual) coverPieces retained
        (group t) (portWords t) (v.wideWindow_resident («W» := W) x m ell short u δ ξ unitCost dated wrap t)
        (v.wideWindow_ready («W» := W) x m ell short u δ ξ unitCost dated area t)
        (v.wideWindow_input_words («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom t
          mem before oldRows (fit t) (imageROM t) (masked t)) current low
      exact ⟨result,ran,by simp,unchanged⟩)
  exact ⟨after,exec,frame⟩

end NativeWindows

/-- The same cells survive pruning and the final spill publication, both above
all format windows. -/
theorem FundedCutRows.window_return (snapshot : Memory W)
    (cells : ∀t q,snapshot (((l).windows t).address ((l).windowBase t) q)=(live t).word oldRows q)
    (frame : ∀j,j<(l).pruneScratch → out j=snapshot j) :
    ∀t q,out (((l).windows t).address ((l).windowBase t) q)=(live t).word oldRows q := by
  intro t q
  have enclosed : (l).windowBase t+((l).windows t).window.stop 0≤(l).pruneScratch :=
    WindowSeries.within (l).floor (l).need t
  exact (frame _ ((((l).windows t).cell_bound _ q).trans_le enclosed)).trans (cells t q)

section NativePrune
open ThreeFlat.RAM PhysicalProcedure CorrectionFrame
local notation "bill" => PruneFlag.charge (v.widePruneLayout x)
local notation "scoreTime" => 4+((l).pruneRows+1)*(42+2*(l).prune.work)
variable (layerWords : ∀j,(l).layers.base≤ j → j<(l).layers.base+(l).layers.size → @Eq (Word W) (before j) (words mem j))
    (quote : v.PrunePrices x.h x.w raw)
include lim reported layerWords quote


/-- The literal final score scan reads the original row triples and the
original layer ROM in the snapshot after every format. Width-zero rows may
have arbitrary endpoint words. -/
theorem FundedCutRows.prune_run (snapshot : Memory W)
    (low : ∀j<(l).floor,snapshot j=before j) :
    let tail:=PruneFlag.output (v.widePruneLayout x) raw (l).pruneScratch (l).threshold snapshot
    (SumScores.procedure W (l).pruneScratch (l).pruneRows (l).threshold (l).prune).Exec
        snapshot tail scoreTime ∧
      tail ((l).pruneScratch+(l).pruneRows)=(if geometry.links.Keep (2^x.h) then 1 else 0) ∧
      ∀addr<(l).pruneScratch,tail addr=snapshot addr := by
  have mutableRoom:=v.wideFullGates_prune_room (u:=u) (δ:=δ) (ξ:=ξ) x m ell short unitCost lim
  have room : (l).floor<2^W := by
    have start : (l).floor≤(l).pruneScratch:=Nat.le_add_right _ _
    exact start.trans_lt ((Nat.le_add_right _ _).trans_lt mutableRoom)
  let space:=v.wideWindow_prune_banks («W» := W) x m ell short u δ ξ unitCost dated room
  have equivalent := TaggedShorterControlHistory.emitted_of_frame dst raw initial snapshot
    (fun j lo hi=>(low j (hi.trans_le space.1)).trans (reported j lo hi))
  have advice (i : Fin (b).rows) (hi : 0<(raw i).width) (site : ℕ)
      (endpoint : site∈[(raw i).endpoint,(raw i).opposite]) :
      (l).layers.read (emitted dst raw snapshot) (site:Word W)=
        (PruneFlag.layerCode (v.widePruneLayout x) site:Word W) := by
    rw [equivalent]
    obtain ⟨hl,hr⟩:=geometry.fits ⟨i,hi⟩
    have siteFits : site< siteLast x.h (2^v.W) k+1 := by
      change (raw i).endpoint≤ siteLast x.h (2^v.W) k at hl
      change (raw i).opposite≤ siteLast x.h (2^v.W) k at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at endpoint
      rcases endpoint with rfl|rfl <;> omega
    have top : (l).layers.size≤2^W := by
      exact (Nat.le_add_left _ _).trans ((space.2.1).trans room.le)
    refine Eq.trans ?_ (v.wideWindowWords_layer («W» := W) x m ell short u δ ξ buffer dated v.maxBits rom
      mem ⟨site,siteFits⟩ top)
    have inside := Nat.add_lt_add_left
      (Nat.mod_lt (site:Word W).val (Nat.two_pow_pos (l).layers.bits)) (l).layers.base
    exact (low _ (inside.trans_le space.2.1)).trans (layerWords _ (Nat.le_add_right _ _) inside)
  have native:=PruneFlag.run_exact_active geometry snapshot dst (l).lengthCode (l).pruneScratch
    (2^x.h) (l).ends (l).metrics (l).layers x.formats.2.1 (by decide) rfl rfl
    (ProtocolRAMPurchaseSampler.lt_span _).le (ProtocolRAMPurchaseSampler.lt_span _).le
    (v.wideWindow_rows_fit x m ell short u δ ξ unitCost dated room) quote.metric quote.codes quote.locations
    advice space.2.2 mutableRoom (by simpa only [Nat.mul_one] using quote.threshold) quote.score
  rw [equivalent] at native
  dsimp only at native ⊢
  simp only [Nat.mul_one] at native
  exact ⟨native.1,native.2,fun _ hi=>PruneFlag.output_below _ _ _ _ _ hi⟩

local notation "liveFor" ok:arg t:arg => v.wideCutAnchor x m ell short u δ ξ buffer dated v.maxBits rom
  t mem before oldRows (fit t)
  (FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
    prices pricePos buy groupsFit metadata ok lanesFit t) retained active (group t) (portWords t)
local notation "lastBank" => (v.wideWidthLayout x.h x.w (v.widePaidSlices x.h x.w v.maxBits)).bank
  (events v.mesh).length
local notation "tapeEnd" => v.wideInstalledSize x m ell unitCost dated
local notation "prefixCPU" => v.wideCountedPrefix x.h x.w v.maxBits
local notation "preceding" => v.wideCountedTime x.h x.w v.maxBits
local notation "U" => (l).pruneScratch+(l).pruneRows+1
local notation "spillCPU" => v.wideCorrectedSpillProgram x.h x.w ell unitCost v.maxBits rom tapeEnd
  ((dated).romEnd rom) ((dated).workEnd tapeEnd) U
local notation "spillFee" => v.wideCorrectedSpillTicks x.h x.w ell unitCost v.maxBits rom tapeEnd
  ((dated).romEnd rom) ((dated).workEnd tapeEnd) U

variable (imageROM : ∀t addr,((l).windows t).rom≤ addr → addr<((l).windows t).adviceEnd →
    @Eq (Word W) (before addr) (words mem addr))
  (masked : ∀t (j:Fin (b).rows),((l).inputs t).width.read before ((3*j.val:ℕ):Word W)=
    ((oldRows j).width:Word W))
include imageROM masked

/-- Execute every format, then the literal threshold scan, on the accepted
calendar output. When the scan keeps the report all purchased cells survive.
On rejection the same procedure still runs for its stated clock and sets its
flag to zero. -/

theorem FundedCutRows.priced_program (head : ℕ→ Word W) (inverted archived : Memory W)
    (inverse : (TagInverse.program W x.h (l).tagScratch).Exec
      (Computability.VPVNP.RAMMemory.initialMemory tapeEnd head) inverted (TagInverse.ticks x.h))
    (calendar : (prefixCPU).Exec inverted archived preceding)
    (fields : ((l).localCode W lastBank).Exec archived before ((l).localTicks lastBank)) :
    ∃final,(v.widePrograms x.h x.w v.maxBits l).2.Exec (Computability.VPVNP.RAMMemory.initialMemory tapeEnd head)
        final (v.wideProgramTicks x.h x.w v.maxBits l).2 ∧
      final ((l).pruneScratch+(l).pruneRows)=(if geometry.links.Keep (2^x.h) then 1 else 0) ∧
      (∀j<(l).floor,final j=before j) ∧
      ∀ok : geometry.links.Keep (2^x.h),∀t q,
        final (((l).windows t).address ((l).windowBase t) q)=(liveFor ok t).word oldRows q := by
  have run : ∃snapshot,(ProcedureBank.program m ((l).banks W)).Exec before snapshot (∑t,(l).windowTicks t) ∧
      (∀j<(l).floor,snapshot j=before j) ∧ ∀ok : geometry.links.Keep (2^x.h),∀t q,
        snapshot (((l).windows t).address ((l).windowBase t) q)=(liveFor ok t).word oldRows q := by
    by_cases ok : geometry.links.Keep (2^x.h)
    · obtain ⟨snapshot,ran,observedSlots,frame⟩:=FundedCutRows.window_run v x tapeSize π input m ell short unitCost
        raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit lim large mem before
        initial retained reported portWords imageROM masked
      exact ⟨snapshot,ran,frame,fun _=>observedSlots⟩
    · obtain ⟨snapshot,ran,frame⟩:=FundedCutRows.window_run_all v x tapeSize π input m ell short unitCost
        raw geometry actual lanesFit lim large mem before initial retained reported portWords imageROM masked
      exact ⟨snapshot,ran,frame,fun accepted=>(ok accepted).elim⟩
  obtain ⟨snapshot,run,frame,observedSlots⟩:=run
  let final:=PruneFlag.output (v.widePruneLayout x) raw (l).pruneScratch (l).threshold snapshot
  obtain ⟨pruned,flag,low⟩:=FundedCutRows.prune_run v x m ell short unitCost raw geometry lim mem before initial
    reported layerWords quote snapshot frame
  have floorLe : (l).floor≤(l).pruneScratch:=Nat.le_add_right _ _
  refine ⟨final,?_,flag,
    fun j hj=>(low j (hj.trans_le floorLe)).trans (frame j hj),?_⟩
  · change ((TagInverse.program W x.h (l).tagScratch).seq
      ((((prefixCPU).seq ((l).localCode W lastBank)).seq (ProcedureBank.program m ((l).banks W))).seq
        (SumScores.procedure W (l).pruneScratch (l).pruneRows (l).threshold (l).prune))).Exec _ final _
    intro pcs regs pubs machine
    exact Procedure.Exec.then (A:=TagInverse.program W x.h (l).tagScratch) inverse
      (Procedure.Exec.then (B:=SumScores.procedure W (l).pruneScratch (l).pruneRows (l).threshold (l).prune)
        (Procedure.Exec.then (B:=ProcedureBank.program m ((l).banks W))
          (Procedure.Exec.then (A:=prefixCPU) (B:=(l).localCode W lastBank) calendar fields) run)
        pruned) machine
  intro ok t q
  have room : (l).windowBase t+((l).windows t).window.stop 0≤(l).pruneScratch :=
    WindowSeries.within (l).floor (l).need t
  exact (low _ ((((l).windows t).cell_bound _ q).trans_le room)).trans (observedSlots ok t q)

/-- Append the actual spill CPU to the observed paid machine. Its native
lower-memory preservation keeps both the pruning indicator and each field
for the positive-cut and binary-mask readouts. -/
theorem FundedCutRows.full_program_with (Post : Memory W→Prop) (head : ℕ→ Word W) (inverted archived : Memory W)
    (inverse : (TagInverse.program W x.h (l).tagScratch).Exec
      (Computability.VPVNP.RAMMemory.initialMemory tapeEnd head) inverted (TagInverse.ticks x.h))
    (calendar : (prefixCPU).Exec inverted archived preceding)
    (fields : ((l).localCode W lastBank).Exec archived before ((l).localTicks lastBank))
    (spill : ∀mid,(∀j<(l).floor,mid j=before j) →
      ∃out,(spillCPU).Exec mid out spillFee ∧ (∀j< U,out j=mid j) ∧ Post out) :
    ∃out,Post out ∧ (paidCPU).Ran head out ∧
      out ((l).pruneScratch+(l).pruneRows)=(if geometry.links.Keep (2^x.h) then 1 else 0) ∧
      (∀j<(l).floor,out j=before j) ∧
      ∀ok : geometry.links.Keep (2^x.h),∀t q,
        out (((l).windows t).address ((l).windowBase t) q)=(liveFor ok t).word oldRows q := by
  obtain ⟨mid,priced,flag,low,observedSlots⟩:=FundedCutRows.priced_program v x tapeSize π input m ell short unitCost
    raw geometry actual prices pricePos buy groupsFit metadata lanesFit lim large mem before initial
    retained reported portWords layerWords quote imageROM masked head inverted archived inverse calendar fields
  obtain ⟨out,run,frame,seen⟩:=spill mid low
  have floorLe : (l).floor≤(l).pruneScratch:=Nat.le_add_right _ _
  refine ⟨out,seen,v.wide_full_run x m ell short u δ ξ unitCost lim head mid out priced run,
    (frame _ (Nat.lt_succ_self _)).trans flag,fun j hj=>(frame j (by omega)).trans (low j hj),?_⟩
  intro ok t q
  have room : (l).windowBase t+((l).windows t).window.stop 0≤(l).pruneScratch :=
    WindowSeries.within (l).floor (l).need t
  have inside:=(((l).windows t).cell_bound _ q).trans_le room
  exact (frame _ (by omega)).trans (observedSlots ok t q)

/-- The paid return without an additional claim about the emitted spill records. -/
theorem FundedCutRows.full_program (head : ℕ→ Word W) (inverted archived : Memory W)
    (inverse : (TagInverse.program W x.h (l).tagScratch).Exec
      (Computability.VPVNP.RAMMemory.initialMemory tapeEnd head) inverted (TagInverse.ticks x.h))
    (calendar : (prefixCPU).Exec inverted archived preceding)
    (fields : ((l).localCode W lastBank).Exec archived before ((l).localTicks lastBank))
    (spill : ∀mid,(∀j<(l).floor,mid j=before j) →
      ∃out,(spillCPU).Exec mid out spillFee ∧ ∀j< U,out j=mid j) :
    ∃out,(paidCPU).Ran head out ∧
      out ((l).pruneScratch+(l).pruneRows)=(if geometry.links.Keep (2^x.h) then 1 else 0) ∧
      (∀j<(l).floor,out j=before j) ∧
      ∀ok : geometry.links.Keep (2^x.h),∀t q,
        out (((l).windows t).address ((l).windowBase t) q)=(liveFor ok t).word oldRows q := by
  obtain ⟨out,_,run,flag,low,observedSlots⟩:=FundedCutRows.full_program_with v x tapeSize π input m ell short unitCost
    raw geometry actual prices pricePos buy groupsFit metadata lanesFit lim large mem before initial
    retained reported portWords layerWords quote imageROM masked (fun _=>True) head inverted archived
    inverse calendar fields (by
      intro mid keptLow
      obtain ⟨out,ran,frame⟩:=spill mid keptLow
      exact ⟨out,ran,frame,trivial⟩)
  exact ⟨out,run,flag,low,observedSlots⟩

end NativePrune

variable (terminal : ∀t q,out (((l).windows t).address ((l).windowBase t) q)=(live t).word oldRows q)

variable {X : Type} {d r M den : ℕ} {eventPin : Event → WireTelescope.CalendarTape.Slot X} {es : List Event}
    {state : Equiv.Perm (Row x.h)→ X}
    (Z : CalendarTerms F x.h d k x.w r M den eventPin es state)
    {Priv Hist : Type} [Fintype Priv] [Fintype Hist]
    (privateOrder : (b).Private order≃Priv) (privateCap : Priv→ℕ)
    (historyCap : Hist→ℕ) (dates view : ℕ)
local notation "N" => dates*Fintype.card ((j:Hist) × Fin (historyCap j))
local notation "ep" => (Fin (dir).groups×Fin ports)×Fin view
local notation "workspace" => CalendarTerms.Shared (geom).index privateCap historyCap (dir).groups ports
  (2^ell) dates view x.w
local notation "rout" => Z.nativeRouting workspace
local notation "ex" => OpenPins x.h x.w (rout).catalyst
local notation "sel" => Fin (rout).selectors
local notation "sites" => Fin (siteLast x.h d k+1)
local notation "V" => SitePins ex sel workspace paidCPU
variable (head : (gates).1.Head→(ex⊕sel)⊕Bool) (paidHead : (paidCPU).Head→(ex⊕sel)⊕Bool)
  (flag mask free plane timeline : Net F V)
  (enter finish : sites→ Net F V) (step : sites→ Fin es.length→ Net F V)
local notation "core" => v.wideWindowLocalProgramsAt x m ell short v.maxBits buffer dated rom Z privateCap
  historyCap dates view (gates).1 paidCPU head paidHead (0 : Fin 1) flag mask free plane timeline enter finish step
  aperture (le_rfl : W≤(paidCPU).W) large
local notation "num" => CalendarTerms.privateWorkspace (geom).index privateOrder privateCap historyCap
  (dir).groups ports (2^ell) dates view x.w
local notation "pCap" => privateCap ∘ privateOrder

include terminal in
/-- All four assignment components of the positive-cut receipt on the actual full
return gate, at the original physical stage and the original slot order. -/
theorem FundedCutRows.cuts (exterior : ex→ Bool) (selectors : sel→ Bool) :
    ∀ (a : ∀t,(Leaf.banks real t).Slots) (y : PrivatePorts pCap) (h : Fin N→ Bool) (p : ep→ Bool) t,
      ((buy t).cut ((core).read t)).closed (CalendarTerms.readPins num exterior selectors
        ((paidCPU).terminal out) (Leaf.write (Leaf.banks real) pCap a y h p))=
        (Leaf.banks real t).settings.close (a t) := by
  apply Leaf.PrintedStage.transport v.W positive raw s (fun _ installed=>
    ∀ (a : ∀t,(Leaf.banks installed t).Slots) (y : PrivatePorts pCap) (h : Fin N→ Bool) (p : ep→ Bool) t,
      ((buy t).cut ((core).read t)).closed (CalendarTerms.readPins num exterior selectors
        ((paidCPU).terminal out) (Leaf.write (Leaf.banks installed) pCap a y h p))=
        (Leaf.banks installed t).settings.close (a t))
  intro a y h p t
  exact wideWindow_receipt_cut_at (v:=v) (m:=m) (ell:=ell) (short:=short) (x:=x)
    (prices:=prices) («positive»:=pricePos) (buy:=buy) (groupsFit:=groupsFit) (metadata:=metadata)
    (π:=π) (marks:=_) (bits:=_) («order»:=order) (size:=rfl) (raw:=raw) (rec:=(FundedCutRows.alignment actual)) (read:=fun _=>rfl)
    (R:=reserve) (paid:=(FundedCutRows.invoice actual)) (keep:=(FundedCutRows.sameGeometry actual).symm ▸ kept)
    (idRead:=(FundedCutRows.originalId actual)) (widthRoom:=fun j=>((FundedCutRows.widthBound actual) j).trans
      (Nat.mul_le_mul_right x.w lanesFit)) («port»:=port) («anchor»:=anchor)
    (owner:=(FundedCutRows.owner actual) x.formats.2.1)
    (pin:=FundedCutRows.port_read v x tapeSize π input unitCost raw geometry actual)
    («buffer»:=buffer) («dated»:=dated) (wbits:=v.maxBits) (romStart:=rom) (t:=t)
    (mem:=mem) (before:=before) («fit»:=fit t) (retain:=retained) (initial:=initial)
    (reported:=reported) («rowsFit»:=rowsFit) (portsRead:=portWords t)
    (Z:=Z) (privateOrder:=privateOrder) (privateCap:=privateCap) (historyCap:=historyCap)
    (dates:=dates) (view:=view) (large:=large) (first:=(gates).1) (fullGate:=paidCPU)
    (firstHead:=head) (fullHead:=paidHead) (atFlag:=(0 : Fin 1)) (keepNet:=flag) (padNet:=mask)
    (freeNet:=free) (planeNet:=plane) (timelineNet:=timeline) (enterNet:=enter)
    (finishNet:=finish) (rowNet:=step) (upper:=aperture) (widthEq:=rfl)
    (dense:=v.wide_full_addr x m ell short u δ ξ unitCost lim) out (terminal t) exterior selectors a y h p

variable (low : WideParent.columnBits wordBits≤(paidCPU).W+1)
local notation "widthRow" => v.wideWindowWidthRow x m ell short u δ ξ buffer dated v.maxBits rom paidCPU aperture
local notation "maskWord" => Leaf.positiveWidthPin (groups:=(dir).groups) («ports»:=ports) (lanes:=2^ell) (E:=ex) (Se:=sel) (Dst:=workspace) paidCPU wordBits widthRow low
local notation "payload" => fun (t:Fin (m+1)) q=>Sum.inr (Sum.inr (Sum.inl (Sum.inl ⟨t,q.1,q.2⟩)))
local notation "maskNet" => Leaf.positiveMask (F:=F) (w:=x.w) Fin.val maskWord payload

include terminal in
/-- The matching mask uses the same installed family as the cut proof. In particular,
the empty part of the packed width table is still read on the full original report. -/
theorem FundedCutRows.masks (exterior : ex→ Bool) (selectors : sel→ Bool) :
    ∀ (a : ∀t,(Leaf.banks real t).Slots) (y : PrivatePorts pCap) (h : Fin N→ Bool) (p : ep→ Bool),
      TypedWiring.value maskNet (CalendarTerms.readPins num exterior selectors
        ((paidCPU).terminal out) (Leaf.write (Leaf.banks real) pCap a y h p)) =
        if Leaf.supported (Leaf.banks real) (Leaf.active real) a then 1 else 0 := by
  apply Leaf.PrintedStage.transport v.W positive raw s (fun _ installed=>
    ∀ (a : ∀t,(Leaf.banks installed t).Slots) (y : PrivatePorts pCap) (h : Fin N→ Bool) (p : ep→ Bool),
      TypedWiring.value maskNet (CalendarTerms.readPins num exterior selectors
        ((paidCPU).terminal out) (Leaf.write (Leaf.banks installed) pCap a y h p)) =
        if Leaf.supported (Leaf.banks installed) (Leaf.active installed) a then 1 else 0)
  intro a y h p
  let tailOrder := Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl Bool) (Equiv.sigmaCongrLeft (β:=fun e=>Fin (privateCap e)) privateOrder))
    (Equiv.refl (Fin N ⊕ ep))
  exact v.wideWindow_mask_value x m ell short u δ ξ buffer dated v.maxBits rom paidCPU aperture
    oldRows s mem before (fun t => fit t) retained active (fun t => group t) portWords rfl
    (v.wide_full_addr x m ell short u δ ξ unitCost lim) out (fun t slot=>terminal t (.inl slot))
    pCap tailOrder exterior selectors wordBits
    (FundedCutRows.masked_width v x tapeSize π input unitCost raw geometry actual) low a y h p

end Observed

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
