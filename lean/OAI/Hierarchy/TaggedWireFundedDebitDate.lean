import OAI.Hierarchy.TaggedWireFundedAttemptLedger
import OAI.Hierarchy.TaggedWireElectedDebitRole

namespace OAI
/-! # Recover the original per-occurrence catalyst receipt of a chosen native ballot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive.Date
open Computability.VPVNP.BurstRAM PrivateRAM Calendar
variable {w q ports base size num pay : ℕ} {C : Chart w q ports} {a : Attempt}
    {before : Memory w} {owner : Expr}

def reindex {m : Memory w} {b n : ℕ} (d : Date C a before owner base size num pay)
    (time : before=m) (start : base=b) (length : size=n) : Date C a m owner b n num pay :=
  time ▸ start ▸ length ▸ d

theorem reindex_entry {m : Memory w} {b n : ℕ} (d : Date C a before owner base size num pay)
    (time : before=m) (start : base=b) (length : size=n) : (d.reindex time start length).entry=d.entry := by
  subst m b n
  rfl

end Hierarchy.ProtocolRAM.CatalystArchive.Date
end

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open StripDirectory CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
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

local notation "account" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea bits stride)
local notation "key" => pairKeys (Columns h D) k
local notation "raw" => (L).header es H.code seed
local notation "nativeRun" expense:arg cap:arg => v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expense cap budget small (0 : Word w)
include H in
private theorem scheduledDebit : ev ∈ es := by
  have split : es = H.prior ++ ev :: tail := H.cut.events
  rw [split]
  simp

local notation "scheduled" => scheduledDebit H

attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

/- Read the dated record family from the reconciliation delivered by the original run. -/
open Lean Elab Term in
local elab "datesOf" receipt:ident : term => do
  let evidence ← Meta.getFVarFromUserName receipt.getId
  let reconciliation ← Meta.whnf (← Meta.inferType evidence)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the original reserve reconciliation"
  let some count := reconciliation.getAppArgs[7]? | throwError "missing dated record count"
  let rowCount ← Meta.whnf count
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected a count of dated records"
  let records ← Meta.whnf rowCount.getAppArgs.back!
  unless records.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected issued records"
  return records.getAppArgs.back!

private def originalDebitHistory (expanse : v.wideFundedSize h width v.maxBits ≤ size) (capAge : v.wideFundedHeight ≤ h) :
    Dates C native account (v.releasedBase P h width) num width :=
  let _receipt := (Classical.choose_spec (nativeRun expanse capAge)).1
  datesOf _receipt

/-- This receipt is selected by the original reconciliation of the genuine coded execution. -/
def originalDebitDate (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) :
    Date C a entry ((account).term ev) ((ar).direct+(ar).occurrences) (ar).occurrences num width := by
  let history := originalDebitHistory H expanse capAge
  let receipt:=history a scheduled
  have time : entryMemory C native a=entry:=by
    have ord : position v.mesh ev = H.prior.length := H.cut.ordinal
    change run C ((es).take (position v.mesh ev)) native = entry
    rw [ord]
    exact H.prior_state
  exact receipt.reindex time (by cases a <;> rfl) (by cases a <;> rfl)

theorem originalDebitDate_entry (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) :
    (H.originalDebitDate expanse capAge).entry=((originalDebitHistory H expanse capAge) a scheduled).entry :=
  Date.reindex_entry _ _ _ _

include H in
theorem pair_room (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) : num<2^w := by
  have receipt:=Classical.choose_spec (nativeRun expanse capAge)
  have pageRoom:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans capAge) budget).1
  have capacity : num≤2^bits:=receipt.1.usedSize
  omega

/-- Aggregating the original owner IDs recovers this branch's actual per-pair withdrawal. -/
theorem reserve_terms (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) :
    let day:=H.originalDebitDate expanse capAge
    OuterBank.resourceBits (day.physicalCatalystKey key) (fun i=>day.entry.bits (Fin.cast day.shape.symm i))=H.reserveDebit := by
  let history := originalDebitHistory H expanse capAge
  have receipt:=Classical.choose_spec (nativeRun expanse capAge)
  have ready:=(v.wide_funded_stock_at_size h width v.radius π.symm raw v.maxBits size expanse capAge budget small).mounted_all
  have pageRoom:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans capAge) budget).1
  have countRoom : num<2^w:=by
    have capacity : num≤2^bits:=receipt.1.usedSize
    omega
  intro day
  funext z
  rw [day.physicalCatalystKey_sum key z]
  have audit:=v.wire_selected_delta h width native ready (dims).words.addresses countRoom
    (small.trans_lt (v.date_prefix_fit h)) history H.index z
  change v.wireWithdrawal h width ((es).get H.index) (StockBound.state C native (H.prior.length+1)) z=
    ∑i : Fin (atTime v.mesh (CatalystArchive.issued history) H.index).rows,
      if (atTime v.mesh (CatalystArchive.issued history) H.index).owner i=key z then
        (atTime v.mesh (CatalystArchive.issued history) H.index).bits i else 0 at audit
  have picked : atTime v.mesh (CatalystArchive.issued history) H.index=day.entry:=by
    rw [H.originalDebitDate_entry expanse capAge]
    have onChart : ev ∈ events (C).mesh := scheduled
    simp only [atTime, H.index_event, eventEntry, CatalystArchive.issued, dite_eq_left onChart, history]
  rw [picked,H.index_event,H.next_state] at audit
  exact audit.symm

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
