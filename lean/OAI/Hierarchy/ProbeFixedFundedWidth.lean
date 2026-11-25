import OAI.Hierarchy.ProbeFixedWideReportedWidth
import OAI.Hierarchy.ProbeFixedFundedBudget
import OAI.Hierarchy.TaggedWidePaidOrdinalWidth

namespace OAI
/-! # The emitted original catalogue widths equal the funded profiles on the calendar tape -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe

/-- The width which the actual reconciled sink reports at an original ordinal. -/
def Whole.Reconciliation.originalWidth {w r edges n count : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I → List (Fin edges)} {center : J → List (Fin edges)} {s : Sink r edges}
    {a : ReserveUse.Archive} {reserve : ℕ} {site : Fin n → Fin count} {debit : Fin n → ℕ}
    {e : Fin r ≃ RouteOccurrence core center} {ci : I → ℕ} {keys : J → Fin count} {m : Memory w}
    (_ : Whole.Reconciliation s a reserve site debit e ci keys m) (j : Fin edges) : ℕ :=
  (s.terminalRows (ReserveUse.output a s.banks reserve site debit m) e ci (fun c => (keys c).val) j).width
end Hierarchy.ProtocolRAM.Calendar

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
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
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => Boot.booted market size (v.wideSignedWords h width stock M π o raw)
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw



local notation "place" => siteNumber h D k
local notation "mountedBoard" => (P).catalogue.coreMount π place (v.wideOrder h width) chk
local notation "ord" => CoreRoute.enum mountedBoard o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i


include raw in
set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
/-- Every original live stock read in the settled bank equals the exact commodity
of the mathematical debit account at calendar completion. -/
theorem funded_width_at (bits : ℕ) {n : ℕ} (site : Fin n→Fin num) (debit : Fin n→ℕ)
    (keys : Columns h D×Fin k→Fin num)
    (physical : StockBound.Run C (v.stockBanks P h width) mid h N k (v.keepLimit*width))
    (stored : PaidWidths.Mounted (old).width rows (TerminalLayout.source page) (v.widePaidSlices h width bits) chk)
    (wordRoom : 28*2^page<2^w) :
    let ss:=v.widePaidSlices h width bits
    let lastPaid:=PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk
    let archive:=result routes (result ((L).scans v.mesh num) lastPaid)
    let out:=run C (events v.mesh) mid
    let marks:=v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
    let catalogue:=(P).catalogue.ordinal v.sampler π v.depth marks order rfl
    (∀e : Fin rows,PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) →
    (∀e : Fin rows,PaidWidths.total ss chk e=PaidWidths.total ss out e) →
    ∀receipt : Whole.Reconciliation sink original supply site debit ord ci keys archive,
    ∀e, ((receipt.originalWidth (catalogue e):ℕ):ℝ)/width =
      v.fundedProfile h width π mid bits receipt.usedAt e := by
  intro ss lastPaid archive out marks catalogue cost same receipt e
  let committed:=ReserveUse.output original old supply site debit archive
  let account:=v.billedAccount P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
    (TerminalLayout.destination page) (sinkBank start cnt r rows)
  let held:=(account.read (.outer (v.mesh.inject+v.mesh.cool) 0) out).bits
  have readStock (i : Commodity (Fin (2^h)) N k) :
      RouteSettlement.actual (old).stock committed (ci i)=held i := by
    let z:=PurchaseInventory.slot i
    let span:=2^page
    have sizeBound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<span:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at sizeBound
    have ok : z<(stock).size := (PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _)
    have addr : (stock).base+z<(A).endAddress v.mesh :=
      (Nat.add_lt_add_left ok (stock).base).trans_le (v.fixedTerminalStock_end P h width)
    have first : (A).endAddress v.mesh<span:=by omega
    have widthRoom : 28*span<2^w:=wordRoom
    have word : z<2^w:=by omega
    have copy:=v.committed_prefix h width size M π raw site debit ss ((stock).base+z) (by omega)
    have file:=PaidWidths.frame (old).width rows (TerminalLayout.source page) ss chk ((stock).base+z)
      (fun t ht=>(stored t ht).1) (by change (stock).base+z<1*span;omega)
    have image : chk ((stock).base+z)=out ((stock).base+z) :=
      ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl addr)
    have bankEq : ((stock).read committed (z:Word w)).val=((stock).read out (z:Word w)).val := by
      simp only [Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt ok]
      exact congrArg Fin.val (copy.trans (file.trans image))
    exact bankEq.trans (v.fixedTerminalStock_read P h width
      (v.issued P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
        (TerminalLayout.destination page) (sinkBank start cnt r rows)) out i word)
  have remainder (j : Columns h D×Fin k) : RouteSettlement.actual (old).reserved committed (keys j).val-
      RouteSettlement.actual (old).used committed (keys j).val=supply-receipt.usedAt j := by
    rw [(ReserveUse.reported original old supply site debit archive receipt.archive (keys j)
      receipt.usedSize receipt.reserveSize (receipt.funded _) receipt.word).2]
    rfl
  let path:=fun i : Commodity (Fin (2^h)) N k =>
    (commodityWalk (S:=v.sampler) π i).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
  let central:=fun j : Columns h D×Fin k =>
    (catalystWalk (S:=v.sampler) j).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
  let board := (P).catalogue.coreMount π (siteNumber h (2^v.W) k) (v.wideOrder h width) chk
  have walk (i : Commodity (Fin (2^h)) (Stages h (2^v.W)) k) : board.ordinary i=(path i).map catalogue := by
    rw [show board.ordinary i = _ from (P).catalogue.coreMount_ordinary π place order chk i]
    simp only [path,List.map_map]; rfl
  have center (j : Columns h (2^v.W)×Fin k) : board.centers j=(central j).map catalogue := by
    rw [show board.centers j = _ from (P).catalogue.coreMount_centers π place order chk j]
    simp only [central,List.map_map]; rfl
  have written := (v.wide_terminal_width_at h width size M π raw site debit keys ss physical stored
    wordRoom cost receipt (catalogue e)).1
  change receipt.originalWidth (catalogue e)=PaidWidths.total ss chk (catalogue e)+
    routeLoad (mountedBoard).ordinary (fun i=>RouteSettlement.actual (old).stock committed (ci i)) (catalogue e)+
    routeLoad (mountedBoard).centers (fun j=>RouteSettlement.actual (old).reserved committed (keys j).val-
      RouteSettlement.actual (old).used committed (keys j).val) (catalogue e) at written
  have stockMass : routeLoad board.ordinary
      (fun i => RouteSettlement.actual (old).stock committed (ci i)) (catalogue e) =
      routeLoad path held e := by
    exact (congrArg₂ (fun paths amounts => routeLoad paths amounts (catalogue e))
      (funext walk) (funext readStock)).trans (load_at_original catalogue path held e)
  have centerMass : routeLoad board.centers
      (fun j => RouteSettlement.actual (old).reserved committed (keys j).val -
        RouteSettlement.actual (old).used committed (keys j).val) (catalogue e) =
      routeLoad central (fun j => supply-receipt.usedAt j) e := by
    exact (congrArg₂ (fun paths amounts => routeLoad paths amounts (catalogue e))
      (funext center) (funext remainder)).trans
        (load_at_original catalogue central (fun j => supply-receipt.usedAt j) e)
  have total := written.trans (congrArg₂ Nat.add
    (congrArg₂ Nat.add (same (catalogue e)) stockMass) centerMass)
  exact congrArg (fun n : ℕ => (n:ℝ)/width) total

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
