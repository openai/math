import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProbeFixedNativeStockRun

namespace OAI
/-! # The two fixed strip frames come from the same scheduled instruction -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CatalystArchive CoreBoard StripChart
open StockCommit StockBound PurchaseStage RepairHistogram StripDirectory
open scoped Fin.CommRing Classical

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
  (src tab dst : ℕ) (owners : Bank)
local notation "w" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "mkt" => (fun a=>(f a).atTime v.mesh v.finish (v.basePhase width) a)
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "incoming" => resolvedStock v.mesh A P.joint.initial (build F s)

/-- The successful placement of the public row windows also proves that all
signed mask inputs fit the current word at every attempt that actually ran. -/
theorem catalyst_date_mask (initial : Memory w) (a : Attempt)
    (whole : Calendar.mounted C (events v.mesh) initial) (date : Event.attempt a∈events v.mesh)
    (limit : (mkt a).MaskBounds (repair C a) (f a).pricedArea (g a)) :
    (mkt a).DateMaskRoom (repair C a) ((guard C a).apply (entryMemory C initial a)) (f a).pricedArea (g a) := by
  have now:=entryMemory_ready C initial a whole date
  have high : (repair C a).repairBits.base+(mkt a).rows < 2^w:=now.2.2.2.2.2.1
  have owner : (repair C a).batch.owner=.row :=
    StripChart.ballot_owner F v.mesh A P.joint.initial s a
  exact limit.at_ready (entryMemory C initial a) now rfl rfl owner rfl
    ((Nat.le_add_left ..).trans high.le)

theorem catalyst_cash_board (a : Attempt)
    (geometry : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((A).base v.mesh (.attempt a))) :
    EventBoard (fresh (f a).pricedArea (f a).stockSource) w :=
  eventBoard _ _ _ geometry.inputs geometry.window.room

set_option cleanup.letToHave false in
theorem catalyst_purchased_frame [Nonempty (Fin k)] (initial : Memory w)
    (p : Fin (v.mesh.inject+v.mesh.cool)) (a : Fin v.mesh.outerFuel) (j t : ℕ)
    (whole : Calendar.mounted C (events v.mesh) initial) (date : Event.attempt (.inner p a j t)∈events v.mesh)
    (limit : (mkt (.inner p a j t)).MaskBounds (repair C (.inner p a j t)) (f (.inner p a j t)).pricedArea
      (g (.inner p a j t)))
    (flag : let B:=StripDirectory.flagBank ((s).outer p a).market.shelf (s).sampler z (2^v.W) k v.depth
      B.base+B.size≤(C).stopAt (.inner p a j t)) :
    let e:=Attempt.inner p.val a.val j t
    PurchasedFrame F s v.mesh P.catalogue P.routes p a j t (incoming e) (deadline v.mesh v.finish (v.basePhase width) e)
      C (entryMemory C initial e) (g e) := by
  let e:=Attempt.inner p.val a.val j t
  let board:=build F (withPorts s v.mesh P.catalogue P.routes) e (incoming e)
  have identified : board=f e :=
    congrArg (fun b=>build F b e (incoming e)) (v.catalyst_boards P z width)
  let market:=board.atTime v.mesh v.finish (v.basePhase width) e
  have charged : market.MaskBounds (repair C e) board.pricedArea (g e) := by
    change (board.atTime v.mesh v.finish (v.basePhase width) e).MaskBounds _ board.pricedArea _
    rw [identified]
    exact limit
  have raw : (C).raw e=testedBoard market.failures board.board := by
    change (C).raw e=testedBoard (board.atTime v.mesh v.finish (v.basePhase width) e).failures board.board
    rw [identified]; rfl
  have layout : (C).layout e=market.layout := by
    change (C).layout e=(board.atTime v.mesh v.finish (v.basePhase width) e).layout
    rw [identified]; rfl
  have frozen : (C).frozen e=market.prefix := by
    change (C).frozen e=(board.atTime v.mesh v.finish (v.basePhase width) e).prefix
    rw [identified]; rfl
  exact ⟨raw,layout,frozen,entryMemory_ready C initial e whole date,charged.rows,charged.cap,
    charged.bits,charged.cut,charged.prior,charged.mask,charged.low,charged.ordered,flag⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
