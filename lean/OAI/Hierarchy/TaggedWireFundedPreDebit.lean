import OAI.Hierarchy.TaggedWireFundedBallots
import OAI.Hierarchy.TaggedWirePreDebit

namespace OAI
/-! # Pre-funding of every actual ordinary width on a completed funded continuation -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option hygiene false
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
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h D)
  (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
open Filter CalendarTape
open Native
namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail x}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "native" => origin H.code
include extent tall floor in
/-- The active predecessor word alone funds the whole measured debit. This
applies at the real calendar cut on the chosen completed continuation. -/
theorem wide_pre_debit
    (numeric : Classical.choose (eventually_atTop.1 v.repair_word_room) ≤ h)
    (n : ℕ) (on : n < (es).length) (atTrial : (es)[n] = .attempt a)
    (i : FeedLayout.Good h N k) :
    let evt := run C H.prior native
    let t := v.taskCommit P h width a
    let u := v.stage P h width r banks source table target owners a evt
    let tag := RepairHistogram.kind (goods:=t.goods) t.plan.bank t.columns u
    AdaptiveProbe.OuterBank.resourceBits tag (RepairHistogram.consumedBits (n:=t.occurrences) t.columns u)
      (v.nativeSlots P h width a i) ≤
      PurchaseInventory.stock (DatedGoods.previous v.mesh (v.stockBanks P h width) n) evt i := by
  let runData := H.readbackRun extent tall floor
  have fits := Classical.choose_spec (eventually_atTop.1 v.repair_word_room) h numeric P width runData.payload
  let B : RepairWordBounds v P h width :=
    ⟨fits.1,fits.2.1,fits.2.2.1,fits.2.2.2.1,fits.2.2.2.2.1,fits.2.2.2.2.2⟩
  exact runData.dated_pre_debit B n on a atTrial H.cut i

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
