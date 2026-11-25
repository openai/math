import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeFixedCatalystDateFrames
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Actual width-debit cells of every event at the end of the native calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StockCommit RepairHistogram StockBound
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "st" => v.taskCommit P z width
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "A" => v.privateArena P z width
private theorem direct_before_stop (area : Area) (i : Fin area.occurrences) : area.direct+i.val<area.stop := by
  dsimp only [Area.stop,Area.output,Area.excess,Area.clip,Area.src,Area.broadcast]
  omega

private theorem committed_credit {w rows q₀ d₀ : ℕ} (stock : StockCommit) (batch : Batch q₀ d₀)
    (m : Memory w) (i : Fin stock.occurrences) (paid : (stock.native w rows batch).ready m)
    (board : EventBoard stock w) :
    ((stock.native w rows batch).after m (stock.direct+i.val)).val =
      if kind (goods:=stock.goods) stock.plan.bank stock.columns m i=none then installedBits stock.columns m i else 0 :=
  (stock.read_direct (rows:=rows) batch m i paid board.chargeFits board.order
    (board.hit (rows:=rows) batch m paid i) board.bound (board.keep i)).1

set_option maxRecDepth 4096
theorem run_direct_credit (initial entry : Memory W) (a : Attempt) (pre later : List Event)
    (slot : Slot C initial (.attempt a) pre later entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (i : Fin (f a).pricedArea.occurrences) :
    (show Word W from run (w:=W) C (events (C).mesh) initial ((f a).pricedArea.direct+i.val)).val=
      if kind (goods:=(f a).pricedArea.goods) (st a).plan.bank (st a).columns (input a entry) i=none then
        installedBits (st a).columns (input a entry) i else 0 := by
  let addr := (f a).pricedArea.direct+i.val
  have read := v.attempt_word P z width r banks src tab dst owners initial entry a pre later slot addr
    (direct_before_stop (f a).pricedArea i)
  have updated := congrFun (v.native_end P z width r banks src tab dst owners a entry).symm addr
  have paid := v.entered P z width r banks src tab dst owners a entry slot.currentReady
  have board : EventBoard (st a) W := eventBoard (w:=W) (f a).pricedArea (f a).stockSource (b a)
    layout.inputs layout.window.room
  exact (congrArg (fun x : Word W => x.val) (read.trans updated)).trans
    (committed_credit (w:=W) (rows:=(f a).market.rows) (st a) (b a) (input a entry) i paid board)

theorem checkout_direct_credit (initial entry : Memory W) (a : Attempt) (pre later : List Event)
    (slot : Slot C initial (.attempt a) pre later entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (flag : ℕ) (after : (A).endAddress v.mesh≤flag) (i : Fin (f a).pricedArea.occurrences) :
    (show Word W from checkedOut (w:=W) C flag initial ((f a).pricedArea.direct+i.val)).val=
      if kind (goods:=(f a).pricedArea.goods) (st a).plan.bank (st a).columns (input a entry) i=none then
        installedBits (st a).columns (input a entry) i else 0 := by
  have occurs : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events (C).mesh
    rw [slot.events];simp
  have low:=(direct_before_stop (f a).pricedArea i).trans_le ((v.attempt_room P z width a).trans
    (((A).within v.mesh (.attempt a) occurs).trans after))
  let addr := (f a).pricedArea.direct+i.val
  have same := ProtocolRAMGeneratedWrite.frame_image flag 1 (historyFlag C (events (C).mesh))
    (run (w:=W) C (events (C).mesh) initial) addr (.inl low)
  exact (congrArg (fun x : Word W => x.val) same).trans
    (v.run_direct_credit P z width r banks src tab dst owners initial entry a pre later slot layout i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
