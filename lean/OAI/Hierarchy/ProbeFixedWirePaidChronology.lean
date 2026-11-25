import OAI.Hierarchy.ProbeFixedWirePaidPrefix
import OAI.Hierarchy.ProbeFixedPriorPaidPair
import OAI.Hierarchy.ProbeFixedPriorForest
import OAI.Hierarchy.ProbeFixedWirePrefixPage

namespace OAI
/-! # Actual paid widths, including retained purchases, at every prefix -/
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

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

/-- Each elapsed native event has all its paid edge loads frozen at its own
slab end. This holds for the original prefix state, the final checkout, and
every raw input selection. -/
theorem elapsed_paid_at (π : Equiv.Perm (Fin (2^h))) (initial : Memory w) (bits : ℕ)
    (active : Calendar.mounted C es initial) (word : floor<2^w)
    (native : v.WideSpillSource h width π (chk initial))
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : rows<2^w) (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (j : ℕ) (last : j≤(es).length) (t : Fin (es).length) (past : t.val < j)
    (s : PaidWidths.Slice) (found : s∈v.wideEventSlices h width bits ((es).get t)) (e : Fin rows) :
    s.load (memAt initial j) e=s.load (chk initial) e :=
  v.wire_prior_paid_event h width π initial bits active word native menu goods edges.le lanes t j past last
    (v.prior_paid_pair h width initial active word edges t j past last)
    (v.wide_prior_forest h width initial active word edges bits t j past last)
    s found e

theorem wide_elapsed_paid :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh ≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ),
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
        let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
        let cal:=v.wideSignedChart h width paidStock
        ∀j≤(events v.mesh).length,∀t : Fin (events v.mesh).length,t.val < j→
          ∀s∈v.wideEventSlices h width bits ((events v.mesh).get t),∀e : Fin (placed).catalogue.rows,
            s.load (StockBound.state cal mid j) e=s.load checked e := by
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h words bound age
  intro width small budget placed arena paidStock paidOrder size extent π raw bits mid checked cal
  have word:=(v.wide_stock_sizes h width age budget small).words.addresses
  have whole:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have src:=(v.wide_spill_source h width size extent π raw word whole).2
  exact v.elapsed_paid_at h width π mid bits whole word src words.1 words.2.1 (bound width).1 words.2.2

theorem wide_wire_paid :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh ≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ),
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
        let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
        let cal:=v.wideSignedChart h width paidStock
        (∀j≤(events v.mesh).length,∀e : Fin (placed).catalogue.rows,
          v.wirePaidAt h width bits j (StockBound.state cal mid j) e=v.wirePaidAt h width bits j checked e) ∧
        (∀t : Fin (events v.mesh).length,∀e : Fin (placed).catalogue.rows,
          v.wirePaidAt h width bits (t.val+1) (StockBound.state cal mid (t.val+1)) e=
          v.wirePaidAt h width bits t.val (StockBound.state cal mid t.val) e+
            PaidWidths.total (v.wideEventSlices h width bits ((events v.mesh).get t)) (StockBound.state cal mid (t.val+1)) e) := by
  filter_upwards [v.wide_elapsed_paid] with h stable
  intro width small budget placed arena paidStock paidOrder size extent π raw bits mid checked cal
  have frozen:=stable width small budget size extent π raw bits
  exact ⟨fun j date=> v.wire_paid_preserved_of_events h width mid bits j date (frozen j date),
    fun j=> v.wire_paid_step h width mid bits j (frozen j.val j.isLt.le) (frozen (j.val+1) j.isLt)⟩

/-- Public threshold for preservation of every time-indexed paid record. -/
def wideWireHeight := Classical.choose (Filter.eventually_atTop.1 v.wide_elapsed_paid)

/-- Read all three replay pages in the memory actually written by the
funded native program. A single public height works for all dated rows,
raw choices, and permutations. -/
abbrev wide_wire_pages (size bits : ℕ) (extent : v.wideFundedSize h width bits ≤ size)
    (height : v.wideFundedHeight ≤ h) (late : v.wideWireHeight ≤ h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (state : Word w) (maxRows : ℕ)
    (limit : (v.wideReserveLayout h width (v.widePaidSlices h width bits)).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀s∈v.widePaidSlices h width bits,s.count ≤ maxRows)
    (widths : ∀e : Fin rows,PaidWidths.total (v.widePaidSlices h width bits)
      (v.wideSignedCheckoutAt h width size stock v.radius π order (v.wideFundedRaw h width bits raw)) e<2^w)
    :=
  let stable:=(Classical.choose_spec (Filter.eventually_atTop.1 v.wide_elapsed_paid)) h late width small budget
    size ((v.wide_funded_extent h width bits).trans extent) π (v.wideFundedRaw h width bits raw) bits
  let run:=v.wide_funded_prefix_at h width v.radius π raw bits size extent height budget small state maxRows limit lengths widths
  let debit:=v.wide_wire_prefix_page h width size bits extent height budget small π raw state maxRows limit lengths widths
  And.intro (fun j (hj : j≤(es).length) e=> v.wire_paid_page h width _ _ bits j hj (stable j hj) e (run.2.2.2.1 j hj e)) debit

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
