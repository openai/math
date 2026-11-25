import OAI.Hierarchy.TaggedWireFundedBoundaryData
import OAI.Hierarchy.TaggedWireFundedPreDebit
import OAI.Hierarchy.TaggedWireFixedAttemptBalance
import OAI.Hierarchy.TaggedWireWidePreDebit

namespace OAI
/-! # The received, spent and clipped quantities of a real chosen histogram -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
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
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "ev" => Event.attempt a
local notation "u" => (es).length-(ev::tail).length
local notation "native" => origin (H.code)
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

def debit : Fin (ar).goods→ℕ:=OuterBank.resourceBits tag (consumedBits (n:=(t₀).occurrences) (t₀).columns st)
def gain : Fin (ar).goods→ℕ:=OuterBank.resourceBits tag (installedBits (n:=(t₀).occurrences) (t₀).columns st)
def spill (i : Fin (ar).goods) := (out ((ar).output+(ar).goods+(ar).goods+i.val)).val
def afterGoods (i : Fin (ar).goods) := v.wireGoodsAt h width (H.prior.length+1) out ((o).symm i)
def reserveDebit : axes→ℕ:=v.wireWithdrawal h width ev out
def nextReserve (pair : axes) := supply-v.wireUsedAt h width (H.prior.length+1) out pair

variable (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
  (numeric : Classical.choose (eventually_atTop.1 v.repair_word_room)≤h)

include extent tall floor numeric in
theorem input_funds (i : Fin (ar).goods) : H.debit i≤(inputGoods) i:=by
  let good:=(o).symm i
  have read:=H.wide_pre_debit extent tall floor numeric H.prior.length H.index.isLt H.index_event good
  have active:=v.wire_attempt_stock_le h width H.prior.length H.index.isLt a H.index_event H.cut good
  have atBank : (v.stockBanks P h width).previous v.mesh ev =
      DatedGoods.previous v.mesh (v.stockBanks P h width) H.prior.length := by
    exact congrArg (DatedGoods.previous v.mesh (v.stockBanks P h width))
      (show position v.mesh ev = H.prior.length from H.cut.ordinal)
  rw [atBank] at active
  have paid : H.debit ((o) good) ≤ v.wireGoodsAt h width H.prior.length entry good :=
    read.trans active
  rw [H.clock.1,H.before_goods]
  simpa only [good,Equiv.apply_symm_apply] using paid

include extent tall floor numeric in
theorem account (i : Fin (ar).goods) :
    (inputGoods) i+H.gain i=H.afterGoods i+H.spill i+H.debit i:=by
  let good:=(o).symm i
  let readback:=H.readbackRun extent tall floor
  have fits:=Classical.choose_spec (eventually_atTop.1 v.repair_word_room) h numeric P width small
  let R : RepairWordBounds v P h width:=
    ⟨fits.1,fits.2.1,fits.2.2.1,fits.2.2.2.1,fits.2.2.2.2.1,fits.2.2.2.2.2⟩
  have measured:=readback.dated_attempt_ledger R H.prior.length H.index.isLt a H.index_event H.cut good
  have word : PurchaseInventory.slot good=i.val:=by
    change ((o) ((o).symm i)).val=i.val
    rw [Equiv.apply_symm_apply]
  change v.datedQuantity P h width r banks source table target owners H.prior.length entry good + H.gain ((o) good)=
    v.datedQuantity P h width r banks source table target owners (H.prior.length+1) out good+
      (out ((ar).output+(ar).goods+(ar).goods+PurchaseInventory.slot good)).val+H.debit ((o) good) at measured
  rw [← v.wire_quantity_at h width H.prior.length entry good,
    ← v.wire_quantity_at h width (H.prior.length + 1) out good, word] at measured
  simpa only [H.clock.1,H.before_goods,good,Equiv.apply_symm_apply,afterGoods,spill] using measured

variable (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h)

include extent expanse capAge in
theorem reserve_account (pair : axes) :
    H.reserveDebit pair≤(origReserve) pair ∧ H.nextReserve pair=(origReserve) pair-H.reserveDebit pair:=by
  have mounted:=(v.wide_stock_at h width size extent v.radius π.symm tape age budget small).mounted_all
  have delta:=v.wire_used_retired_step h width native mounted (dims).words.addresses H.index pair
  have bound:=(v.wide_wire_reserve h width size v.maxBits expanse capAge budget small π.symm
    ((L).header es H.code seed) (0:Word w) pair).1 (H.prior.length+1) H.index.isLt
  change v.wireUsedAt h width (H.prior.length+1) (StockBound.state C native (H.prior.length+1)) pair=
    v.wireUsedAt h width H.prior.length (StockBound.state C native H.prior.length) pair+
      v.wireWithdrawal h width ((es).get H.index) (StockBound.state C native (H.prior.length+1)) pair at delta
  rw [H.prior_state,H.next_state,H.index_event] at delta
  change v.wireUsedAt h width (H.prior.length+1)
    (StockBound.state C native (H.prior.length+1)) pair ≤ supply at bound
  rw [H.next_state] at bound
  simp only [H.clock.1,H.before_used,nextReserve,reserveDebit]
  omega

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
