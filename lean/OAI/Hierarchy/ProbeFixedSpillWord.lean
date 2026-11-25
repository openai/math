import OAI.Hierarchy.ProbeFixedFailureEconomy
import OAI.Hierarchy.ProbeFixedRepairSlot
import OAI.Hierarchy.ProbeFixedStripFunds

namespace OAI
/-! # Exact unsigned overflow readback and its source-credit bound at a failed attempt -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native StripChart
open StockCommit PurchaseStage RepairHistogram
open scoped BigOperators Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
local notation "layoutType" => StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
  ((v.privateArena P z width).base v.mesh (.attempt a))

variable (S : v.RepairSlot P z width r banks src tab dst owners a entry)

local notation "u" => input a entry
local notation "s" => st a
local notation "ar" => (f a).pricedArea
local notation "tag" => RepairHistogram.kind (goods:=(s).goods) (s).plan.bank (s).columns u
local notation "add" => installedBits (n:=(s).occurrences) (s).columns u
local notation "sub" => consumedBits (n:=(s).occurrences) (s).columns u

/-- The signed histogram first reads the active, unsigned predecessor from the
physical stock bank, then adds its issued widths and subtracts the paid debits. -/
def repairRaw (i : Fin (ar).goods) : ℕ :=
  RepairHistogram.raw (s).plan.bank (s).columns (s).plan.src (s).occurrences
    ((s).beforeApply (b a) (f a).market.rows u) i

set_option maxHeartbeats 1000000 in
include S in
/-- Both the literal cell identity and its per-coordinate bound. The signed
scatter's debit is funded, and at most the prescribed ordinary committed width
is ever credited to this resource. -/
theorem repair_spill_word (i : Fin (ar).goods)
    (funded : resourceBits tag sub i≤(u ((s).plan.bank.base+i.val)).val)
    (credit : resourceBits tag add i≤v.menu.maximum*v.menu.copiesAt v.copyScale width) :
    let out:=after C (.attempt a) entry
    (out ((ar).output+(ar).goods+(ar).goods+i.val)).val=
      v.repairRaw P z width r banks src tab dst owners a entry i-(out ((ar).output+i.val)).val ∧
      (out ((ar).output+(ar).goods+(ar).goods+i.val)).val≤v.menu.maximum*width := by
  intro out
  let layout:=S.layout
  have run:=S.slot.currentReady
  have before:=(v.repair_stock P z width r banks src tab dst owners a entry S.event run layout).1 i
  have held : (u ((s).plan.bank.base+i.val)).val≤v.keepLimit*width:=
    before.symm.le.trans (S.held ((v.nativeSlots P z width a).symm i))
  have upper:=(Nat.add_le_add held credit).trans_lt S.rateRoom
  have mode:=(v.repair_words P z width r banks src tab dst owners a entry run layout.board
    layout.positive layout.window S.failed).1 i
  have room:=fresh_stockRoom ar (f a).stockSource (b a) layout.inputs width v.keepLimit layout.window.wide
    layout.window.room layout.window.budget (layout.window.budget.le.trans_lt layout.window.wordRoom)
  have ord:=(eventBoard ar (f a).stockSource (b a) layout.inputs layout.window.room).order
  have direct_le : (s).direct ≤ (s).broadcast :=
    (Nat.le_add_right (s).direct (s).occurrences).trans
      ((Nat.le_add_right ((s).direct + (s).occurrences) (s).occurrences).trans ord)
  obtain ⟨balance,kept,spill⟩:=(s).repair_receipt (b a) u i
    (v.entered P z width r banks src tab dst owners a entry run) direct_le room.address room.credit room.debit
    room.seed room.space room.wide width v.keepLimit room.limit room.room room.excess
    room.clipCap room.excessCap room.bankCap funded upper mode
  let raw:=v.repairRaw P z width r banks src tab dst owners a entry i
  change (u ((s).plan.bank.base+i.val)).val+resourceBits tag add i=raw+resourceBits tag sub i at balance
  change (out ((ar).output+i.val)).val=min raw (v.keepLimit*width) at kept
  change (out ((ar).output+(ar).goods+(ar).goods+i.val)).val=raw-min raw (v.keepLimit*width) at spill
  have pay : v.menu.maximum*v.menu.copiesAt v.copyScale width≤v.menu.maximum*width:=
    Nat.mul_le_mul_left _ (Nat.div_le_self ..)
  refine ⟨?_,?_⟩
  · rw [kept,spill]
  · omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
