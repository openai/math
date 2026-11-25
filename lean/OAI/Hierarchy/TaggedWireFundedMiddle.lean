import OAI.Hierarchy.TaggedWireFundedPurchasedLedger
import OAI.Hierarchy.TaggedWireDatedMiddle

namespace OAI
/-! # The literal native intermediate widths at a signed attempt, just before cap routing -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
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
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
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

theorem middle_width (extent : (A).endAddress v.mesh≤ size) (paidAge : v.paidBallotHeight≤h)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) :
    FeedTransfer.amountsWidth H.afterMount (FeedTransfer.middleAmounts H.afterMount afterValue (H.spill ∘ o))=
      FeedTransfer.input (π:=π.symm) («place» := place) carry cap := by
  let beforePaid:=fun i=>paid0 i+H.paid i
  have useful:=FeedTransfer.middle_input H.afterMount cap beforePaid (fun _=>0) H.nextReserve afterValue
    (fun i=>H.paid_account extent paidAge i) (fun _=>by simp) (fun _=>rfl)
  refine useful.trans (congrArg (fun widths => FeedTransfer.input (π := π.symm) («place» := place) widths cap) ?_)
  have geometry := FeedTransfer.paid_geometry (oldMount).actual H.afterMount.actual paid0 (H.prior_ends extent paidAge)
  have remaining : H.nextReserve=leftover:=funext fun z=>(H.reserve_account extent expanse capAge z).2
  simp only [beforePaid, chordWidths_add, chordWidths_empty, add_zero, geometry, remaining]

theorem next_paid (extent : (A).endAddress v.mesh≤ size) (paidAge : v.paidBallotHeight≤h) :
    v.wirePaidAt h width v.maxBits (H.prior.length+1) ((slots ev).next x c)=H.afterPaid:=by
  let n:=H.prior.length+1
  have ages:=max_le_iff.mp (max_le_iff.mp paidAge).1
  have ready:=(v.wide_stock_at h width size extent v.radius π.symm tape age budget small).mounted_all
  have before:=v.wide_prestate_low h width size π.symm tape v.radius n H.index.isLt ready
  change PrefixAgreement.Low ((A).first+n*(A).stride) (StockBound.state C native (H.prior.length+1)) _ at before
  rw [H.next_state] at before
  have lower:=fun k hk=>((H.next_low k hk).trans (before k hk)).symm
  have other:=Classical.choose_spec (eventually_atTop.1 v.wide_past_agreement) h ages.2 width small budget size extent
    π.symm tape v.maxBits n ((slots ev).next x c) lower
  have eqn:=(Classical.choose_spec (eventually_atTop.1 v.wide_wire_paid) h ages.1 width small budget size extent
    π.symm tape v.maxBits).1 n H.index.isLt
  change ∀i,v.wirePaidAt h width v.maxBits n (StockBound.state C native (H.prior.length+1)) i=_ at eqn
  rw [H.next_state] at eqn
  exact funext (fun i=>(other i).symm.trans (eqn i).symm)

theorem spill_read (i : Fin (ar).goods) :
    (((slots ev).next x c) ((ar).output+(ar).goods+(ar).goods+i.val)).val=H.spill i:=by
  have space:=v.attempt_room P h width a
  change (ar).output+3*(ar).goods≤(A).base v.mesh ev+(A).stride at space
  have fit:=i.isLt
  have inside : (ar).output+(ar).goods+(ar).goods+i.val < (A).base v.mesh ev+(A).stride := by omega
  exact congrArg Fin.val (H.next _ inside)

theorem after_values (extent : (A).endAddress v.mesh≤ size) (paidAge : v.paidBallotHeight≤h) :
    afterValue=Sum.elim (v.wirePaidAt h width v.maxBits ((es).length-tail.length) ((slots ev).next x c))
      (Sum.elim (v.wireGoodsAt h width ((es).length-tail.length) ((slots ev).next x c))
        (fun z=>supply-v.wireUsedAt h width ((es).length-tail.length) ((slots ev).next x c) z)) := by
  rw [H.clock.2,H.next_paid extent paidAge,H.next_goods,H.next_used]
  funext v
  rcases v with e|(i|z)
  · rfl
  · simp only [Sum.elim_inr,Sum.elim_inl,Function.comp_apply,afterGoods,Equiv.symm_apply_apply]
  · rfl

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
