import OAI.Hierarchy.TaggedWireFeedAgreement

namespace OAI
/-! # Original dated cap gate on any specified funded continuation -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
private theorem feedOrdinalSlot {wordBits choices degrees : ℕ} (chart : Chart wordBits choices degrees)
    (mem : Memory wordBits) (u : Fin (events chart.mesh).length) (boundary : Boundary)
    (eventAt : (events chart.mesh)[u.val]=.feed boundary) (whole : Calendar.mounted chart (events chart.mesh) mem) :
    Slot chart mem (.feed boundary) ((events chart.mesh).take u.val) ((events chart.mesh).drop (u.val+1))
      (StockBound.state chart mem u.val) := by
  have raw := ordinal_slot chart mem u whole
  dsimp only at raw
  rw [eventAt] at raw
  exact raw

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
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape


namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {b : Boundary}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.feed b::tail) x} {c : (slots (.feed b)).choice x}
    (J : v.FundedDate h width size π seed age budget small t c)
local notation "place" => siteNumber h D k
local notation "post" => after C (.feed b) (run C J.prior (origin J.code))
local notation "B₀" => (P).catalogue.coreMount π.symm place (v.wideOrder h width)
local notation "out" => after C (.feed b) x

theorem feed_mount : B₀ out=B₀ post := by
  have sameMount:=v.wide_mount_eq h width π.symm place out post (fun u hu=>by
    have first:=(v.catalyst_initial_le_first P h width)
    have low : u<(A).base v.mesh (.feed b)+(A).stride :=
      (hu.trans_le first).trans_le ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
    exact J.next u low) (fun birth i u lo hi=>by
    apply J.nextOff u
    exact v.actual_shelf_public h width age budget small birth i tail u lo hi)
  have ext {B₁ B₂ : CoreBoard.Mount (S:=v.sampler) π.symm place (P).catalogue.rows}
      (same : B₁.actual=B₂.actual) (rows : B₁.row=B₂.row) : B₁=B₂:=by
    cases B₁;cases B₂;cases same;cases rows;rfl
  exact ext sameMount rfl

end FundedDate

include extent in
/-- The physical feed gate for the exact funded continuation supplied by the
caller. Every operand, including the geometry of padded future purchase rows,
agrees with the gate chosen once for this cursor. -/
theorem cursor_feed_at {b : Boundary} {tail x}
    (t : WireTelescope.CalendarTape.Prefix slots es base (.feed b::tail) x) (c : (slots (.feed b)).choice x)
    (J : v.FundedDate h width size π seed age budget small t c)
    (late : v.feedOperatorHeight≤h)
    (causal : Classical.choose (eventually_atTop.1 v.wide_past_agreement)≤h) :
    v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits ((L).header es J.code seed))
      late budget small v.maxBits J.index b J.index_event
      ((v.wide_cursor_feed h width size extent π seed age budget small t late).1 c) := by
  obtain ⟨code,past,cut,date,tag,hdate,pre,post,presents⟩:=
    v.cursor_feed_presents h width size extent π seed age budget small t late
  have dates : date=J.index:=by
    apply Fin.ext
    have eventList : es = past ++ .feed b :: tail := cut.events
    have schedule : (es).length=past.length+(tail.length+1) := by
      simpa only [List.length_append,List.length_cons] using congrArg List.length eventList
    have elapsed : (es).length-(tail.length+1)=J.prior.length := J.clock.1
    change date.val=J.prior.length
    omega
  subst date
  let code₀:=v.wideFundedRaw h width v.maxBits ((L).header es code seed)
  let code₁:=v.wideFundedRaw h width v.maxBits ((L).header es J.code seed)
  have large:=max_le_iff.mp late
  have dim:=large.2
  let auth₀:=v.wide_paid_feed_stock h width size extent v.radius π.symm code₀
    ((max_le_iff.mp large.1).1) budget small (((max_le_iff.mp dim).2).trans (Nat.lt_two_pow_self (n:=h)).le)
  let auth₁:=v.wide_paid_feed_stock h width size extent v.radius π.symm code₁
    ((max_le_iff.mp large.1).1) budget small (((max_le_iff.mp dim).2).trans (Nat.lt_two_pow_self (n:=h)).le)
  let before₀:=StockBound.state C (origin code) J.index.val
  let before₁:=StockBound.state C (origin J.code) J.index.val
  let after₀:=StockBound.state C (origin code) (J.index.val+1)
  let after₁:=StockBound.state C (origin J.code) (J.index.val+1)
  let cut₀ : Slot C (origin code) (.feed b) ((es).take J.index.val) ((es).drop (J.index.val+1)) before₀ :=
    feedOrdinalSlot C (origin code) J.index b tag auth₀.nativeStock.mounted_all
  let cut₁ : Slot C (origin J.code) (.feed b) ((es).take J.index.val) ((es).drop (J.index.val+1)) before₁ :=
    feedOrdinalSlot C (origin J.code) J.index b J.index_event auth₁.nativeStock.mounted_all
  have left : PrefixAgreement.Low ((A).base v.mesh (.feed b)) before₀ before₁:=by
    rw [show before₀=x from pre,show before₁=_ from J.prior_state]
    exact J.before
  have right : PrefixAgreement.Low ((A).base v.mesh (.feed b)+(A).stride)
      (after C (.feed b) before₀) (after C (.feed b) before₁):=by
    rw [show before₀=x from pre,show before₁=_ from J.prior_state]
    exact J.next
  have data : v.dated_feed_transfer P h width r banks source table target owners (origin code) auth₀ b cut₀ =
      v.dated_feed_transfer P h width r banks source table target owners (origin J.code) auth₁ b cut₁ :=
    v.dated_transfer_agrees P h width r banks source table target owners b auth₀ auth₁ cut₀ cut₁ left right
  let mount:=((P).catalogue.coreMount («w»:=w) π.symm (siteNumber h D k) (v.wideOrder h width))
  have geometry : mount after₀=mount after₁:=by
    rw [show after₀=_ from post,show after₁=_ from J.next_state]
    exact J.feed_mount
  have paid : v.wirePaidAt h width v.maxBits J.index.val before₀=v.wirePaidAt h width v.maxBits J.index.val before₁:=by
    rw [show before₀=x from pre,show before₁=_ from J.prior_state]
    exact J.raw_past extent (max_le_iff.mp large.1).2 causal
  have used : v.wireUsedAt h width J.index.val before₀=v.wireUsedAt h width J.index.val before₁:=by
    rw [show before₀=x from pre,show before₁=_ from J.prior_state]
    exact J.before_used
  have receipt:=presents c
  dsimp only [wireFeedPresentation] at receipt ⊢
  change FeedTransfer.Presents (mount after₀) _ _ (ProtocolRAMDateSpillRank.spillEnum (mount after₀) order)
    (FeedTransfer.passWidth (mount after₀) (v.wirePaidAt h width v.maxBits J.index.val before₀) _
      (fun a=>fuel v.mesh*width-v.wireUsedAt h width J.index.val before₀ a))
    (v.dated_feed_transfer P h width r banks source table target owners (origin code) auth₀ b cut₀) _ at receipt
  rw [geometry,data,paid,used] at receipt
  exact receipt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
