import OAI.Hierarchy.TaggedWireFundedCounterDigits
import OAI.Hierarchy.ProbeFixedPaidFit
import OAI.Hierarchy.ProbeFixedPaidArchiveWord
import OAI.Hierarchy.ProbeFixedEarnedBirthFlag
import OAI.Hierarchy.ProbeFixedTerminalMask
import OAI.Hierarchy.TaggedWireFundedAttemptLedger

namespace OAI
/-! # The actually elected strip compiler, credit words and original header at a funded event -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open CalendarTape StockCommit ProtocolRAM.PurchaseStage ThreeFlat.Diagonal.MotifOuterTerms
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

local notation "slab" => v.slab (v.seed P h width) P width
local notation "EF" => Slab.effects slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh


namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail : List Event}
    {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "entry" => run C H.prior (origin H.code)
local notation "b" => PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" y => HistogramShelf.snapshot C a y
local notation "paid" => v.stage P h width r banks source table target owners a entry
local notation "format" => (reader).format
local notation "signal" i => (b).selected (snap x) ((i).val:Word w)
local notation "I" => Fin ((C).layout a).candidates


local notation "ar" => (v.nativeFormats P h width a).pricedArea
local notation "s₀" => (v.nativeFormats P h width a).stockSource
local notation "st" => v.taskCommit P h width a
local notation "tag" => RepairHistogram.kind (goods:=(ar).goods) (st).plan.bank (st).columns paid
local notation "credits" => RepairHistogram.installedBits (n:=(ar).occurrences) (st).columns paid
local notation "currentReadback" => H.readbackRun extent tall floor
local notation "co" => checkedOut C ((A).endAddress v.mesh) (origin H.code)
local notation "ids" => (repair C a).keys
local notation "head" => StripChart.header F (v.nativeBoards P h width) a
local notation "bought" => v.nativeFormats P h width

include extent tall floor in
theorem checkout_credits (i : Fin (ar).occurrences) :
    (co ((ar).direct+i.val)).val=if tag i=none then credits i else 0 := by
  have live : Event.attempt a∈events v.mesh := by
    have eqn : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  exact v.checkout_direct_credit P h width r banks source table target owners (origin H.code) entry a H.prior _ H.cut
    (((currentReadback).boards a live).1) ((A).endAddress v.mesh) le_rfl i

include extent tall floor in
theorem checkout_ports : (head).Loaded co :=
  (v.terminal_port_header P h width r banks source table target owners a (origin H.code) ((A).endAddress v.mesh)
    (currentReadback).resident (currentReadback).nativeStock.mounted_all (Nat.le_add_right ..)).2

include extent tall floor in
theorem priced_row_iff (i : I) :
    i∈liveRows (b) paid ((C).layout a).candidates ↔ signal i := by
  have present : Event.attempt a∈events v.mesh := by
    have eqn : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have layout:=((currentReadback).boards a present).1
  have bound:=v.ballot_before P h width r banks source table target owners a
  have same:=priced_liveRows ((C).layout a) (repair C a) (ar) (s₀) (v.stamp P h width r banks source table target owners a)
    (prepared C a entry) H.cut.currentReady.2.2.2.2.2.2.1 H.cut.currentReady.2.2.2.2.2.2.2.1
    ((by decide : 1<4).trans_le layout.window.wide) bound (bound.trans (Nat.le_succ _)) layout.window.label
  have rowsEq : liveRows (b) paid ((C).layout a).candidates =
      liveRows (b) (snap entry) ((C).layout a).candidates := same
  rw [rowsEq]
  simp only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h=>(H.ballot extent i).2.2.mpr h.1,H.committed_at extent i⟩

variable (late : v.stripHeight≤h)
local notation "inputPlan" => PortPlan (st) (b) paid ((C).layout a).candidates

include extent tall floor late in
/-- The installed symbol on either branch is compiled against its physically
mounted row directory, also when the trial has no elected ballot entries. -/
def stripPlan : inputPlan := by
  letI : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  cases a with
  | outer phase trial=>
    let fit:=v.payload_paid_fit P h width r banks source table target owners phase trial (origin H.code)
      entry H.prior _ H.cut (currentReadback).resident late small
    exact v.payloadStage_compile P h width r banks source table target owners phase trial entry fit
  | inner phase trial j iter=>
    let fit:=v.purchased_paid_fit P h width r banks source table target owners phase trial j iter (origin H.code)
      entry H.prior _ H.cut (currentReadback).resident late small
    exact v.purchasedStage_compile P h width r banks source table target owners phase trial j iter entry fit


section Inner
variable {phase : Fin (v.mesh.inject+v.mesh.cool)} {trial : Fin v.mesh.outerFuel}
    {j : Fin v.mesh.reserveSteps} {n : Fin v.mesh.innerFuel}
local notation "ev" => Attempt.inner phase.val trial.val j.val n.val
variable {t' : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt (.inner phase.val trial.val j.val n.val)::tail) x}
    {z : ((v.wideSelector h width age budget small).format.slot (.attempt (.inner phase.val trial.val j.val n.val))).choice x}
    (J : v.FundedDate h width size π seed age budget small t' z)
local notation "actual" => origin J.code
local notation "out" => checkedOut C ((A).endAddress v.mesh) actual
local notation "form" => v.nativeBoards P h width
local notation "port" => StripChart.header F form ev
local notation "ballot" => PurchaseStage.enabledBatch ((C).layout ev) (repair C ev)

include extent tall floor in
theorem retained_role (i : Fin ((C).layout ev).candidates)
    (active : (ballot).selected (HistogramShelf.snapshot C ev x) (i.val:Word w))
    (portIndex : Fin (port).ports) :
    (StripChart.retainedAt F form ev).eval out ((v.roleOccurrence P h width ev i portIndex).val:Word w)≠0  := by
  let _ : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let readback:=J.readbackRun extent tall floor
  let raw:=v.wideFundedRaw h width v.maxBits ((L).header es J.code seed)
  have boot:=(v.wide_signed_boot_at h width size extent stock v.radius π.symm order raw readback.endFits).2.2.1
  have present : Event.attempt ev∈events v.mesh := by
    have eqn : events v.mesh = J.prior ++ .attempt ev :: tail := J.cut.events
    rw [eqn]
    simp
  have limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h:=
    (Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (dims).market)
  have live:=(J.priced_row_iff extent tall floor i).2 active
  have entryEq : CatalystArchive.entryMemory C actual ev = run C J.prior actual := J.cut.entryMemory
  have originalRow : i ∈ liveRows (ballot)
      (v.stage P h width r banks source table target owners ev (CatalystArchive.entryMemory C actual ev))
      ((C).layout ev).candidates := entryEq.symm ▸ live
  exact v.wide_elected_retained h width r banks source table target owners π.symm actual out phase trial j n
    boot readback.resident readback.endFits readback.nativeStock.mounted_all (dims).strip small limit (readback.boards ev present).1
    readback.archives (fun _ _=>rfl) i originalRow portIndex
    (J.checkout_ports extent tall floor)

end Inner
end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
