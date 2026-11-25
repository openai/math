import OAI.Hierarchy.ProbeFixedBroadcastPages
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedPaidDirectCells
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice

import OAI.Hierarchy.ProbeFixedCatalystDateFrames
import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedOrigin

namespace OAI
/-! # What the chronological price commit actually writes to its broadcast bank -/

noncomputable section
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

/-- A positive final selector width was committed at its own dated input. -/
theorem forest_committed (a : Attempt) (mem entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((G).base v.mesh (.attempt a))) (age : v.stripHeight≤z) (small : width≤2^z)
    (i : Fin (f a).pricedArea.rows)
    (charged : ((run C (events v.mesh) mem) ((f a).pricedArea.broadcast+i.val)).val≠0) :
    committed (b a) (input a entry) (i.val:Word W) := by
  let addr:=(f a).pricedArea.broadcast+i.val
  have dims := (v.ordinary_dimensions P z width a).2
  have rates := v.strip_scalar_room P z width age small
  have copiesEq : (b a).copies=v.menu.copiesAt v.copyScale width := dims
  have bc:=fresh_broadcastRoom _ _ (b a) layout.inputs layout.window.room
  have read:= (st a).read_broadcast (b a) (input a entry) i
    (v.entered P z width r banks src tab dst owners a entry cut.currentReady) bc.fits rates.termFit
    (by simpa only [copiesEq] using rates.copyFit) (by simpa only [copiesEq] using rates.sumFit) (bc.keeps i)
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
  by_contra missing
  apply charged
  change ((run C (events (C).mesh) mem) addr).val=0
  rw [done]
  change ((((st a).native W (f a).pricedArea.rows (b a)).after (input a entry)) ((st a).broadcast+i.val)).val=0
  rw [read,ite_eq_right missing]
  rfl

set_option cleanup.letToHave false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The final paid record implies that this same root passed its live test. -/
theorem forest_candidate_live (a : Attempt) (mem entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((G).base v.mesh (.attempt a))) (age : v.stripHeight≤z) (small : width≤2^z)
    (_mounted : Calendar.mounted C (events v.mesh) mem) (limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z)
    (i : Fin (f a).pricedArea.rows)
    (charged : ((run C (events v.mesh) mem) ((f a).pricedArea.broadcast+i.val)).val≠0) :
    (f a).market.failures.live.eval ((guard C a).apply entry) (i.val:Word W)≠0 := by
  have yes:=v.forest_committed P z width r banks src tab dst owners a mem entry prior tail cut layout age small i charged
  let market := (f a).atTime v.mesh v.finish (v.basePhase width) a
  have high : (repair C a).repairBits.base+market.rows < 2^W := cut.currentReady.2.2.2.2.2.1
  have owner : (repair C a).batch.owner=.row :=
    StripChart.ballot_owner F v.mesh G P.joint.initial (v.nativeBoards P z width) a
  have limits := v.catalystMaskBounds_at_height P z width r banks src tab dst owners limit a
  have room := limits.at_ready («C» := C) (e := a) entry cut.currentReady rfl rfl owner rfl
    ((Nat.le_add_left ..).trans high.le)
  have selected : i ∈ StockCommit.liveRows (b a) (input a entry) (f a).pricedArea.rows :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, yes⟩
  exact room.live (f a).stockSource i selected

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
