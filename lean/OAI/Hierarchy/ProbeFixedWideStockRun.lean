import OAI.Hierarchy.ProbeFixedWideStockLayout
import OAI.Hierarchy.ProbeFixedWideStockSizes
import OAI.Hierarchy.ProbeFixedWideFrozenReady
import OAI.Hierarchy.ProbeFixedPreparedTests
import OAI.Hierarchy.ProbeFixedTrialReady
import OAI.Hierarchy.ProbeFixedWidePurchasedBefore

namespace OAI
/-! # Stock admission and boundedness along the actual signed calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
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


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


/-- A single induction runs the full original schedule including arbitrary hidden
selectors. Replay tests use the purchased tape transported from the earlier parent.
Incoming and saved stock both start at their actual zero banks. -/
theorem wide_stock_at (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (height : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    StockBound.Run C (v.stockBanks P h width) (v.wideSignedMidAt h width size stock M π order raw)
      h N k (v.keepLimit*width) := by
  let init:=v.wideSignedMidAt h width size stock M π order raw
  have lim:=v.wide_stock_sizes h width height budget small
  have original:=v.wide_signed_boot_at h width size extent stock M π order raw lim.words.addresses
  have pages:=original.2.2.2.1
  have funds:=original.2.2.2.2.2.1
  have zeroes:=v.wide_initial_stock h width size extent stock M π order raw lim.words.addresses lim.strip
  have data:=v.wide_stock_layout h width size extent M π raw lim.words budget lim.width lim.alphabet lim.rowsMass lim.roles
  have sourcePrefix:=(v.wideGeometryPrefix h width).2.2
  apply v.native_stock P h width r banks source table target owners init init zeroes.1 zeroes.2
    (v.wide_initial_room h width) lim.words.addresses
    ((Nat.lt_of_succ_le budget).trans (v.date_prefix_fit h)) data
  intro a live j m mounted old _saved
  let prior:=(events v.mesh).take j
  let tail:=(events v.mesh).drop (j+1)
  have split : events v.mesh=prior++Event.attempt a::tail := by
    obtain ⟨bound,atIndex⟩:=event_at v.mesh live
    have rest:=(List.drop_eq_getElem_cons bound)
    rw [atIndex] at rest
    exact (List.take_append_drop j (events v.mesh)).symm.trans (congrArg (prior++·) rest)
  have fr:=v.wide_market_ready h width size extent M π raw a prior tail split lim.market lim.words.addresses mounted
  apply v.trial_ready h width r (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) 0 (P).joint (v.wideSources h width).2
    banks source table target owners a live sourcePrefix lim.words.addresses lim.words.cut lim.width lim.alphabet lim.rowsMass
    init init (data a live).2 mounted fr
  cases a with
  | outer phase trial =>
    exact v.payload_tests_before_of_bounded P h width r banks source table target owners phase trial
      prior tail init split mounted pages (fun _=>0) funds old lim.words fr
  | inner phase trial slice inner =>
    have low : (StripDirectory.stratumHeader h D k v.sampler.degree v.depth ((s).stratumHeader phase trial)).stop≤
        (A).base v.mesh (.attempt (.inner phase trial slice inner)) :=
      (v.wide_stratum_before h width).trans ((v.catalyst_initial_le_first P h width).trans (Nat.le_add_right ..))
    have purchased:=v.wide_purchased_before h width size extent stock M π order raw phase trial slice inner prior tail
      split mounted lim.words.addresses
    exact v.purchased_tests_before_of_bounded P h width r banks source table target owners phase trial slice inner
      prior tail init split mounted pages (fun _=>0) funds old lim.words fr π low purchased

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
