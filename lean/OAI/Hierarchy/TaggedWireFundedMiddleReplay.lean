import OAI.Hierarchy.TaggedWireFundedMiddle
import OAI.Hierarchy.ProbeFixedDatedWireLedger

namespace OAI
/-! # Named intermediate widths on a fully dated branch -/

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

local notation "rawOf" J:arg => (L).header es (FundedDate.code J) seed

attribute [local irreducible] wideDatedValue StockBound.state

open Lean Elab Term in
local elab "issuedAt " date:ident : term => do
  let proof ← Meta.getFVarFromUserName date.getId
  let eqn ← Meta.whnf (← Meta.inferType proof)
  let some (_, left, _) := eqn.eq? | throwError "expected the funded date equality"
  unless left.getAppFn.isConstOf ``wideDatedValue do
    throwError "expected the amounts of the funded date"
  let args := left.getAppArgs
  return args[args.size - 2]!

private def replayRecords (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size)
    (height : v.wideDatedLedgerHeight ≤ h) (state : Word w) :
    Attempt → Entry (Fintype.card (Columns h D) * k) width :=
  let _date := v.wide_dated_amounts h width size π.symm (rawOf J) expanse height small budget state
    (J.prior.length+1) J.index.isLt
  issuedAt _date

/-- The values of the signed-before-cap operator on H are the original paid, stock
and reserve ordinals on any complete continuation J with this actual choice. -/
theorem middle_replay (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (height : v.wideDatedLedgerHeight≤h)
    (paidAge : v.paidBallotHeight≤h) (state : Word w) :
    afterValue=v.wideDatedValue h width v.maxBits (origin J.code) (checkedOut C ((A).endAddress v.mesh) (origin J.code))
      (replayRecords J expanse height state) ((es).length-tail.length) := by
  let j := J.prior.length+1
  let physical (mem : Memory w) := Sum.elim (v.wirePaidAt h width v.maxBits j mem)
    (Sum.elim (v.wireGoodsAt h width j mem) (fun z => supply-v.wireUsedAt h width j mem z))
  let valuation := v.wideDatedValue h width v.maxBits (origin J.code)
    (checkedOut C ((A).endAddress v.mesh) (origin J.code)) (replayRecords J expanse height state)
  have extent := (v.wide_funded_extent h width v.maxBits).trans expanse
  have common := (H.after_values extent paidAge).trans (J.after_values extent paidAge).symm
  have date : valuation j = physical (StockBound.state C (origin J.code) j) :=
    v.wide_dated_amounts h width size π.symm (rawOf J) expanse height small budget state j J.index.isLt
  have fields : Sum.elim J.afterPaid (Sum.elim (J.afterGoods ∘ o) J.nextReserve) =
      physical (after C ev (run C J.prior (origin J.code))) := by
    funext sourceRow
    rcases sourceRow with e|(i|z)
    · rfl
    · simp only [physical, j, Sum.elim_inr, Sum.elim_inl, Function.comp_apply, afterGoods, Equiv.symm_apply_apply]
    · rfl
  exact common.trans (fields.trans ((congrArg physical J.next_state.symm).trans
    (date.symm.trans (congrArg valuation J.clock.2.symm))))

theorem spill_replay (J : v.FundedDate h width size π seed age budget small t c) :
    H.spill=J.spill:=funext (fun i=>(H.spill_read i).symm.trans (J.spill_read i))

local notation "checked" J:arg => checkedOut C ((A).endAddress v.mesh) (origin (FundedDate.code J))
local notation "finalMount" J:arg => (P).catalogue.coreMount π.symm place (v.wideOrder h width) (checked J)

theorem middle_ends (J : v.FundedDate h width size π seed age budget small t c)
    (extent : (A).endAddress v.mesh≤ size) (paidAge : v.paidBallotHeight≤h)
    (e : Fin rows) (active : 0<H.afterPaid e) :
    H.afterMount.actual.tail e=(finalMount J).actual.tail e ∧
      H.afterMount.actual.head e=(finalMount J).actual.head e := by
  let Jtape:=v.wideFundedRaw h width v.maxBits (rawOf J)
  have dates:=H.clock.2.symm.trans J.clock.2
  have ready:=(v.wide_stock_at h width size extent v.radius π.symm Jtape age budget small).mounted_all
  have left:=H.next_low
  rw [dates] at left
  have endLow:=v.wide_prestate_low h width size π.symm Jtape v.radius (J.prior.length+1) J.index.isLt ready
  change PrefixAgreement.Low ((A).first+(J.prior.length+1)*(A).stride)
    (StockBound.state C (origin J.code) (J.prior.length+1)) (checked J) at endLow
  rw [J.next_state] at endLow
  have low:=fun z hz=>((left z hz).symm.trans (J.next_low z hz)).trans (endLow z hz)
  have positive : 0<v.wirePaidAt h width v.maxBits (J.prior.length+1) out e:=by rw [←dates];exact active
  have ages:=max_le_iff.mp (max_le_iff.mp (max_le_iff.mp paidAge).2).2
  exact Classical.choose_spec (eventually_atTop.1 v.wide_past_paid_ends) h ages.1 width small budget
    size extent π.symm Jtape v.maxBits (J.prior.length+1) out low e positive

theorem middle_mount (J : v.FundedDate h width size π seed age budget small t c)
    (extent : (A).endAddress v.mesh≤ size) (paidAge : v.paidBallotHeight≤h) :
    FeedTransfer.amountsWidth (finalMount J) (FeedTransfer.middleAmounts (finalMount J) afterValue (J.spill ∘ o))=
      FeedTransfer.amountsWidth H.afterMount (FeedTransfer.middleAmounts H.afterMount afterValue (H.spill ∘ o)) := by
  have walks : (finalMount J).ordinary=H.afterMount.ordinary:=by
    funext i
    simp only [afterMount,CatalogueRows.Board.coreMount_ordinary]
  rw [←H.spill_replay J]
  have middle : FeedTransfer.middleAmounts (finalMount J) afterValue (H.spill ∘ o)=
      FeedTransfer.middleAmounts H.afterMount afterValue (H.spill ∘ o):=by
    simp only [FeedTransfer.middleAmounts,walks]
  rw [middle]
  let values := FeedTransfer.middleAmounts H.afterMount afterValue (H.spill ∘ o)
  have paid := FeedTransfer.paid_geometry H.afterMount.actual (finalMount J).actual
    (fun e => values (.inl e)) (fun e active => H.middle_ends J extent paidAge e
      (lt_of_lt_of_le active (Nat.sub_le (H.afterPaid e) _)))
  exact congrArg (fun chords => chords +
    (commodityGraph (k:=k) π.symm place).chordWidths (fun i => values (.inr (.inl i))) +
    (catalystGraph place).chordWidths (fun a => values (.inr (.inr a)))) paid.symm

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
