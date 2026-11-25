import OAI.Hierarchy.TaggedWireFundedMiddleReplay
import OAI.Hierarchy.ProbeFixedWideSpillRank

namespace OAI
/-! # Recovery of an elected attempt's exact spill from its dated physical rank page -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 250000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.FundedDate

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalystArchive StripChart
open WireTelescope WireTelescope.CalendarTape ReportSockets CoreRoute
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
  {h width size : ℕ} {π : Equiv.Perm (Fin (2^h))}
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "s" => v.nativeBoards P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "owners" => sinkBank (v.catalystStaticStart P h width) cnt r (P).catalogue.rows
local notation "es" => events v.mesh
local notation "C" => v.wideSignedChart h width stock
variable {seed : Boot.Tape h D} {age : v.wideStockHeight≤h}
  {budget : v.keepLimit*width+1≤2^h} {small : width≤2^h}
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" key:arg => v.wideOrigin h width size ((reader).format.windows.header es key seed) π

variable {a : Attempt} {tail : List Event} {x : Memory w}
  {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}

/-- The group's counter input uses the original committed attempt's third
stock column. All subsequent calendar slots and the final acceptance word
preserve that cell on the same funded continuation. -/
theorem spill_page (J : v.FundedDate h width size π seed age budget small t c)
    (bits first : ℕ) (j : Fin (es).length) (day : (es).get j=.attempt a) (input : Memory w)
    (archived : ∀u<(A).endAddress v.mesh,input u=checkedOut C ((A).endAddress v.mesh) (origin J.code) u)
    (i : Commodity (Fin (2^h)) N k) :
    RouteSettlement.actual (v.wideSpillPage h width bits first j.val).overflow input (PurchaseInventory.slot i)=
      J.spill (v.nativeSlots P h width a i) := by
  let ar := (v.nativeFormats P h width a).pricedArea
  let addr := ar.output+2*ar.goods+PurchaseInventory.slot i
  have present : Event.attempt a∈es := day ▸ (es).get_mem j
  have entire := (A).within v.mesh (.attempt a) present
  have allocated := v.attempt_room P h width a
  change ar.output+3*ar.goods≤(A).base v.mesh (.attempt a)+(A).stride at allocated
  have goods : ar.goods=PurchaseInventory.footprint h N k := v.stock_goods P h width a
  have inside : PurchaseInventory.slot i<ar.goods := (v.nativeSlots P h width a i).isLt
  have low : addr<(A).base v.mesh (.attempt a)+(A).stride := by dsimp only [addr];omega
  have room := (v.wide_stock_sizes h width age budget small).words.addresses
  have cells : PurchaseInventory.footprint h N k≤2^w := by omega
  rw [v.wide_spill_overflow h width bits first j,day]
  change RouteSettlement.actual (ProtocolRAMDateSpillRank.attemptBank h N k ar) input (PurchaseInventory.slot i)=_
  rw [ProtocolRAMDateSpillRank.attempt_read ar input i cells]
  change (input addr).val=_
  have seen := J.cut.word addr (fun e later =>
    (v.event_prefix P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) owners e addr (low.trans_le ((A).apart v.mesh (J.cut.later e later)))).1)
  have receipt : (input addr).val=
      (after C (.attempt a) (run C J.prior (origin J.code)) addr).val :=
    congrArg Fin.val ((archived addr (low.trans_le entire)).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (low.trans_le entire))).trans seen))
  change (input addr).val=
    (after C (.attempt a) (run C J.prior (origin J.code))
      (ar.output+ar.goods+ar.goods+(v.nativeSlots P h width a i).val)).val
  rw [v.slot_index P h width a i]
  simpa only [addr,two_mul,Nat.add_assoc] using receipt


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.FundedDate

end
end OAI
