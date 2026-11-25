import OAI.Hierarchy.ProbeFixedBroadcastPages
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedPaidDirectCells
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice

namespace OAI
/-! # What the chronological price commit actually writes to its broadcast bank -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit StockBound CatalystArchive PurchaseStage RepairHistogram DiscrepancyROM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)

local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "fee" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop

theorem broadcast_date (a : Attempt) (mem entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((G).base v.mesh (.attempt a))) (age : v.stripHeight≤z) (small : width≤2^z)
    (left : ∀x,(fee).payload.base≤x → x<(fee).payload.stop → (mem x).val≤v.maxBits)
    (right : ∀x,(fee).purchase.base≤x → x<(fee).purchase.stop → (mem x).val≤v.maxBits)
    (i : Fin (f a).pricedArea.rows) :
    let addr := (f a).pricedArea.broadcast+i.val
    ((run C (events v.mesh) mem) addr).val≤v.maxBits ∧
    ((checkedOut C ((G).endAddress v.mesh) mem) addr).val≤v.maxBits := by
  intro addr
  have upper : (fee).stop≤(G).first := (Nat.le_add_right ..).trans (v.emptyReserve_end_le_first P z width)
  have leftEnd : (fee).payload.stop≤(fee).stop := Nat.le_add_right ..
  have baseRead (x : ℕ) (cheap : x<(fee).stop) : input a entry x=mem x :=
    (v.slot_rows_low P z width r banks src tab dst owners a prior tail mem entry cut x (cheap.trans_le upper)).2.2
  have price (key : Word W) : ((st a).price.read (input a entry) key).val≤v.maxBits := by
    cases a with
    | outer phase trial =>
      apply DiscrepancyROM.Table.Capped.lookup (t:=(fee).payload)
      apply (show (fee).payload.Capped v.maxBits mem from left).transport
      exact fun x _ hi=>baseRead x (hi.trans_le leftEnd)
    | inner phase trial slice j =>
      apply DiscrepancyROM.Table.Capped.lookup (t:=(fee).purchase)
      apply (show (fee).purchase.Capped v.maxBits mem from right).transport
      exact fun x _ hi=>baseRead x hi
  have dims := (v.ordinary_dimensions P z width a).2
  have rates := v.strip_scalar_room P z width age small
  have copiesEq : (b a).copies=v.menu.copiesAt v.copyScale width := dims
  have bc:=fresh_broadcastRoom _ _ (b a) layout.inputs layout.window.room
  have read:= (st a).read_broadcast (b a) (input a entry) i
    (v.entered P z width r banks src tab dst owners a entry cut.currentReady) bc.fits rates.termFit
    (by simpa only [copiesEq] using rates.copyFit) (by simpa only [copiesEq] using rates.sumFit) (bc.keeps i)
  have installed : ((after C (.attempt a) entry) addr).val≤v.maxBits := by
    change ((((st a).native W (f a).pricedArea.rows (b a)).after (input a entry)) ((st a).broadcast+i.val)).val≤_
    rw [read]
    split
    · exact price _
    · exact Nat.zero_le _
  have row : addr<(f a).pricedArea.stop := by
    have h:=i.isLt
    dsimp only [addr]
    unfold Area.stop Area.output Area.excess Area.clip Area.src
    omega
  have before:=row.trans_le (v.attempt_room P z width a)
  have live : Event.attempt a∈events v.mesh := by
    change Event.attempt a ∈ events (C).mesh
    rw [cut.events]
    simp
  have late := v.paid_slab_cell P z width r banks src tab dst owners _ mem entry prior tail cut addr before
  have off : addr<(G).endAddress v.mesh:=before.trans_le ((G).within v.mesh _ live)
  have done := late
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl off)] at done
  constructor
  · change (run C (events (C).mesh) mem addr).val ≤ v.maxBits
    rw [done]
    exact installed
  · rw [late]; exact installed

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
