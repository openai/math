import OAI.Hierarchy.TaggedWireFundedMiddle
import OAI.Hierarchy.ProbeFixedDatedWireLedger

import OAI.Hierarchy.TaggedWireFundedMiddleReplay
import OAI.Hierarchy.TaggedWireFundedSpillAmount
import OAI.Hierarchy.TaggedWireFeedTransferCongr

namespace OAI
/-! # Settling an admitted attempt in the original checked spill chart -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
attribute [local irreducible] Nat.pow
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
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


local notation "signedPage" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "signedBits" => signedPage stock
local notation "banks" => TerminalLayout.settlement signedBits stock
local notation "source" => TerminalLayout.source signedBits
local notation "table" => TerminalLayout.table signedBits
local notation "target" => TerminalLayout.destination signedBits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
namespace FundedDate
variable {v h width size π seed age budget small} {tail : List Event} {x : Memory w} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "ev" => Event.attempt a
local notation "u" => (es).length-(ev::tail).length
local notation "native" => origin H.code
local notation "tape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "entry" => run C H.prior native
local notation "out" => after C ev entry
local notation "t₀" => v.taskCommit P h width a
local notation "st" => v.stage P h width r banks source table target owners a entry
local notation "tag" => RepairHistogram.kind (goods:=(t₀).goods) (t₀).plan.bank (t₀).columns st
local notation "o" => v.nativeSlots P h width a
local notation "inputGoods" => fun i=>v.wireGoodsAt h width u x ((o).symm i)
local notation "ar" => ((f) a).pricedArea
local notation "axes" => Columns h D×Fin k
local notation "supply" => fuel v.mesh*width
local notation "origReserve" => fun pair=>supply-v.wireUsedAt h width u x pair

local notation "place" => siteNumber h D k
local notation "rows" => (P).catalogue.rows
local notation "paid0" => v.wirePaidAt h width v.maxBits u x
local notation "oldMount" => (P).catalogue.coreMount π.symm place (v.wideOrder h width) x
local notation "afterValue" => Sum.elim H.afterPaid (Sum.elim (H.afterGoods ∘ o) H.nextReserve)
local notation "leftover" => fun z=>(origReserve) z-H.reserveDebit z
local notation "carry" => (oldMount).actual.chordWidths paid0+H.afterMount.actual.chordWidths H.paid+
  (catalystGraph place).chordWidths leftover
local notation "cap" => (show FeedTransfer.Transfer h D k from
  ⟨fun _=>0,fun i=>H.afterGoods ((o) i)+H.spill ((o) i),fun _=>0,fun i=>H.afterGoods ((o) i),
    fun i=>H.spill ((o) i),fun _=>by simp⟩)

local notation "checked" J:arg => checkedOut C ((A).endAddress v.mesh) (origin (FundedDate.code J))
local notation "finalMount" J:arg => (P).catalogue.coreMount π.symm place (v.wideOrder h width) (checked J)
local notation "remainder" => carry+(commodityGraph π.symm place).chordWidths (H.afterGoods ∘ o)

/-- Both chronological matrix domains are identified on this funded attempt by its
actual retained goods and original overflow cells, including paid repeated hops. -/
theorem spill_charts (J : v.FundedDate h width size π seed age budget small t c)
    (bits first : ℕ) (j : Fin (es).length) (day : (es).get j=.attempt a) (image : Memory w)
    (archived : ∀n<(A).endAddress v.mesh,image n=(checked J) n) :
    let page:=v.wideSpillPage h width bits first j.val
    let amounts:=fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual page.overflow image (PurchaseInventory.slot i)
    let dir:=finalMount J
    let G:=commodityGraph π.symm place
    (FeedTransfer.input (π:=π.symm) («place»:=place) carry cap=remainder+G.chordWidths amounts) ∧
      FeedTransfer.output H.afterMount carry cap=remainder+dir.actual.chordWidths (routeLoad dir.ordinary amounts) := by
  intro page amounts dir G
  have equity : amounts=(cap).spill := funext fun i=>
    (J.spill_page bits first j day image archived i).trans (congrFun (H.spill_replay J) ((o) i)).symm
  let paid := Classical.choose (H.afterMount.onlySpill_congr (F:=F) dir (place).injective (publicChord h D k)
    (wideRouteOrder h D k) (cap).spill rfl)
  have spare:=FeedTransfer.afterVote_rest (π:=π.symm) («place»:=place) carry (H.afterGoods ∘ o) (H.spill ∘ o)
  rw [equity]
  constructor
  · exact (LedgerStep.feedShape G carry (cap).old (cap).active (cap).held (cap).kept
      (cap).spill (cap).balanced).symm.trans (congrArg (·+G.chordWidths (cap).spill) spare)
  · exact congrArg₂ (·+·) spare paid

/-- The clipping operand uses actual overflow words of this attempt, while the
private route indices come from the saved final directory of the same run. -/
theorem spill_transfer (J : v.FundedDate h width size π seed age budget small t c)
    (bits first : ℕ) (j : Fin (es).length) (day : (es).get j=.attempt a) (image : Memory w)
    (archived : ∀n<(A).endAddress v.mesh,image n=(checked J) n) :
    let page:=v.wideSpillPage h width bits first j.val
    let amounts:=fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual page.overflow image (PurchaseInventory.slot i)
    let dir:=finalMount J
    let G:=commodityGraph π.symm place
    ∀site (before : State (FeedTransfer.input (π:=π.symm) («place»:=place) carry cap) site)
      (after : State (FeedTransfer.output H.afterMount carry cap) site)
      (left : State (remainder+G.chordWidths amounts) site)
      (right : State (remainder+dir.actual.chordWidths (routeLoad dir.ordinary amounts)) site),
      HEq before left→HEq after right→
      LedgerStep.carry (dir.onlySpill (F:=F) (place).injective (publicChord h D k) amounts
        (ProtocolRAMDateSpillRank.spillEnum dir (wideRouteOrder h D k))) remainder site left right=
      FeedTransfer.matrix H.afterMount (place).injective (publicChord h D k)
        (ProtocolRAMDateSpillRank.spillEnum H.afterMount (wideRouteOrder h D k)) carry cap site before after := by
  intro page amounts dir G site before after left right leftCast rightCast
  have equity : amounts=(cap).spill := funext fun i=>
    (J.spill_page bits first j day image archived i).trans (congrFun (H.spill_replay J) ((o) i)).symm
  have head : HEq (LedgerStep.repartition G carry (cap).old (cap).active (cap).held (cap).kept
      (cap).spill (cap).balanced site before) left :=
    (cast_heq _ before).trans leftCast
  exact FeedTransfer.checked_carry (F:=F) H.afterMount dir (place).injective (publicChord h D k)
    (wideRouteOrder h D k) carry cap rfl amounts equity remainder
    (FeedTransfer.afterVote_rest (π:=π.symm) («place»:=place) carry (H.afterGoods ∘ o) (H.spill ∘ o)).symm
    site before after left right head rightCast

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
