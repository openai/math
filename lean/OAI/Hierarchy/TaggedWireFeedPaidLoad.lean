import OAI.Hierarchy.ProbeFixedPriorFeedReads
import OAI.Hierarchy.ProtocolRAMDateSpillBilled
import OAI.Hierarchy.TaggedWireWideGoodsChange
import OAI.Hierarchy.ProtocolRAMCatalogueCoreMount

namespace OAI
/-! # The entire native paid list of a feed is its ordinary clipping traffic -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride


/-- A single cutoff for the paid core edge and row readbacks at every feed. -/
def feedPaidHeight := Classical.choose (Filter.eventually_atTop.1 v.elapsed_boundary_reads)

/-- At the actual feed's immediate post-state, the sum over every paid lane
is exactly the ordinary route load of the spill words published in that state. -/
theorem wire_feed_paid_load (size bits : ℕ) (extent : floor≤ size) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h D) (readAge : v.feedPaidHeight≤h) (stockAge : v.wideStockHeight≤h)
    (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (t : Fin (es).length) (b : Boundary) (date : (es).get t=.feed b)
    {entry : Memory w} {prior tail : List Event}
    (cut : Slot C (v.wideSignedMidAt h width size stock v.radius π order raw) (.feed b) prior tail entry)
    (e : Fin (P).catalogue.rows) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let afterFeed:=after C (.feed b) entry
    let auth:=v.wide_paid_feed_stock h width size extent v.radius π raw stockAge budget small dimension
    let T:=v.dated_feed_transfer P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) owners mid auth b cut
    let board:=(P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) afterFeed
    PaidWidths.total (v.wideEventSlices h width bits (.feed b)) afterFeed e=routeLoad board.ordinary T.spill e := by
  intro mid afterFeed auth T board
  have ordinal : t.val=prior.length := by
    have located := position_at v.mesh t.isLt
    change position v.mesh ((es).get t)=t.val at located
    rw [date] at located
    exact located.symm.trans cut.ordinal
  have split : es=prior++(.feed b)::tail:=cut.events
  have entryAt : StockBound.state C mid t.val=entry := by
    change run C ((es).take t.val) mid=entry
    rw [ordinal,split,List.take_left]
    exact cut.entry
  have truedate : StockBound.state C mid (t.val+1)=afterFeed := by
    calc
      _ = after C ((es).get t) (StockBound.state C mid t.val) := StockBound.state_succ C mid t.val t.isLt
      _ = _ := by rw [date,entryAt]
  let choices:=PurchaseInventory.slotEquiv h N k
  let L:=lay b
  let paths:=v.paidFeedPath P h width route lay b
  let walk:=v.spillPath P h π (v.wideOrder h width)
  let recorded:=fun j : Fin (FeedLayout.lanes N k*2^h)=>(afterFeed (L.overflow+j.val)).val
  have inputs:=(Classical.choose_spec (Filter.eventually_atTop.1 v.elapsed_boundary_reads))
    h readAge width small budget size extent π raw t b date
  have reads (l : Fin (FeedLayout.lanes N k)) :
      (paths (L.column l)).Reads afterFeed (fun i=>walk (choices.symm (finProdFinEquiv (l,i)))) := by
    rw [←truedate]
    exact inputs l
  have entryWord (i : Commodity (Fin (2^h)) N k) : T.spill i=recorded (choices i) :=
    (v.dated_feed_reads P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) owners mid auth b cut i).2.2.2.2
  have paid:=L.installed_load paths afterFeed e (fun j=>walk (choices.symm j)) reads
  let price:=fun j=>(walk (choices.symm j)).count e*recorded j
  have convert : routeLoad walk (fun i=>recorded (choices i)) e=
      routeLoad (fun j=>walk (choices.symm j)) recorded e := by
    simpa only [routeLoad,price,Equiv.symm_apply_apply] using choices.sum_comp price
  change PaidWidths.total (L.columns.map (fun c=>c.paidSlice (paths c))) afterFeed e=routeLoad walk T.spill e
  rw [paid,funext entryWord]
  exact convert.symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
