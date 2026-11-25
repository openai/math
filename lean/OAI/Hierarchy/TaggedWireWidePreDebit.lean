import OAI.Hierarchy.TaggedWireWideGoodsChange
import OAI.Hierarchy.TaggedWirePreDebit
import OAI.Hierarchy.ProbeFixedReadbackProducer
import OAI.Hierarchy.ProbeFixedRepairWordRoom

namespace OAI
/-! # Dated debit of each original physically available commodity -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tbl" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "C" => v.wideSignedChart h width stock
local notation "bs" => v.stockBanks P h width
local notation "es" => events v.mesh
local notation "order" => wideRouteOrder h D k
local notation "good" => Commodity (Fin (2^h)) N k

open StockCommit RepairHistogram
def DatedDebitsFit (initial : Memory w) : Prop :=
  ∀u : ℕ,∀on : u<(es).length,∀a : Attempt,(es)[u]=.attempt a→
    ∀{prior tail : List Event} {entry : Memory w},Slot C initial (.attempt a) prior tail entry→∀i : good,
      let t:=v.taskCommit P h width a
      let stage:=v.stage P h width r old src tbl dst owners a entry
      let tags:=RepairHistogram.kind (goods:=t.goods) t.plan.bank t.columns stage
      AdaptiveProbe.OuterBank.resourceBits tags (consumedBits (n:=t.occurrences) t.columns stage) (v.nativeSlots P h width a i)≤
        v.wireGoodsAt h width u entry i

theorem wire_pre_debit (π : Equiv.Perm (Fin (2^h))) (initial fixture : Memory w)
    (runRead : v.ReadbackRun P h width r old src tbl dst owners π initial fixture)
    (room : RepairWordBounds v P h width) : v.DatedDebitsFit h width initial := by
  unfold DatedDebitsFit
  intro n current a date prior tail entry cut i
  have paid:=runRead.dated_pre_debit room n current a date cut i
  have banks : (bs).previous v.mesh (.attempt a)=DatedGoods.previous v.mesh bs n := by
    rw [←date]
    simp only [StockBound.Banks.previous,previousStock,position_at v.mesh current,DatedGoods.previous]
  dsimp only at paid
  rw [←banks] at paid
  exact paid.trans (v.wire_attempt_stock_le h width n current a date cut i)

theorem wide_pre_debit :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.widthFloor≤width→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let original:=v.fixedTerminalStock placed h width
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let o:=wideRouteOrder h (2^v.W) k
        let mid:=v.wideSignedMidAt h width size original v.radius π o raw
        v.wideSignedCheckoutAt h width size original v.radius π o raw ((arena).endAddress v.mesh)=0→
          v.DatedDebitsFit h width mid := by
  filter_upwards [v.readback_run,v.repair_word_room] with h receipt numeric
  intro width small floor budget placed arena original size extent π raw o mid accepted
  obtain ⟨legit⟩:=receipt width small floor budget size extent π raw accepted
  have n:=numeric placed width small
  exact v.wire_pre_debit h width π mid mid legit ⟨n.1,n.2.1,n.2.2.1,n.2.2.2.1,n.2.2.2.2.1,n.2.2.2.2.2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
