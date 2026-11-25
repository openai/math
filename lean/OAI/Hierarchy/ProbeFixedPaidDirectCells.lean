import OAI.Hierarchy.ProbePaidNativeRowBounds
import OAI.Hierarchy.ProbeFixedPaidSlabCell
import OAI.Hierarchy.ProbeFixedCatalystDateFrames
import OAI.Hierarchy.ProbeFixedStripSizes

namespace OAI
/-! # Per-cell ceilings of the actual paid direct and catalyst mate records -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit StockBound
open CatalystArchive PurchaseStage RepairHistogram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "w" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "gs" => v.stamp P z width r banks src tab dst owners
local notation "s" => v.nativeBoards P z width

set_option maxHeartbeats 2000000 in
private theorem paid_commit_segment (a : Attempt) :
    (C).commit a = pricedSegment (fmt a).pricedArea (fmt a).stockSource (gs a) w
      (enabledBatch (fmt a).market.layout (fmt a).board) := by
  cases a with
  | outer phase trial => rfl
  | inner phase trial layer tick => rfl

set_option maxHeartbeats 2000000 in
theorem paid_direct_cell (a : Attempt) (mem entry : Memory w) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : TrialLayout C a (fmt a).pricedArea (fmt a).stockSource (gs a) v.keepLimit width
      ((A).base v.mesh (.attempt a)))
    (age : v.stripHeight≤z) (small : width≤2^z) (j : Fin (fmt a).pricedArea.occurrences) :
    (checkedOut C ((A).endAddress v.mesh) mem ((fmt a).pricedArea.direct+j.val)).val≤v.menu.maximum*width := by
  let f:=fmt a
  let st:=fresh f.pricedArea f.stockSource
  let b:=enabledBatch f.market.layout f.board
  let u:=stageInput f.pricedArea f.stockSource (gs a) (postOutput ((C).layout a) (repair C a) (prepared C a entry))
  have installed := paid_commit_segment v P z width r banks src tab dst owners a
  have read:=CatalystArchive.priced_installation C a entry f.pricedArea f.stockSource (gs a) b
    installed cut.currentReady (v.catalyst_cash_board P z width r banks src tab dst owners a layout) j
  have tailRoom : f.pricedArea.direct+f.pricedArea.occurrences≤f.pricedArea.stop := by
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast
    omega
  have early : f.pricedArea.direct+j.val<(A).base v.mesh (.attempt a)+(A).stride :=
    (Nat.add_lt_add_left j.isLt _).trans_le (tailRoom.trans (v.attempt_room P z width a))
  rw [v.paid_slab_cell P z width r banks src tab dst owners (.attempt a) mem entry prior tail cut _ early]
  have dims:=v.ordinary_dimensions P z width a
  have copiesEq : f.board.batch.copies=v.menu.copiesAt v.copyScale width:=dims.2
  have maxEq : f.board.batch.maxWidth=v.menu.maximum:=dims.1
  have numer:=v.strip_scalar_room P z width age small
  have native:=f.sealed_installation_bound (StripChart.start s a)
    (by
      have sealHeader {z₀ d₀ k₀ q₀ ports : ℕ} (profile : Calendar.Format z₀ d₀ k₀ q₀ ports) (base : ℕ) :
          (profile.withOccurrenceHeader base).withOccurrenceHeader base = profile.withOccurrenceHeader base := rfl
      have sealGeometry {z₀ d₀ k₀ q₀ p₀ t₀ : ℕ} (geom : PortPadding.Geometry z₀ d₀ k₀ q₀ p₀ t₀)
          (base active : ℕ) : (geom.build base active).withOccurrenceHeader base = geom.build base active := by
        cases geom <;> exact sealHeader _ _
      exact sealGeometry (StripChart.shape F s a) (StripChart.start s a)
        (resolvedStock v.mesh A P.joint.initial (StripChart.build F s) a)) u j numer.termFit
    (by simpa only [copiesEq] using numer.copyFit) (by simpa only [copiesEq] using numer.sumFit)
  have remain : v.menu.copiesAt v.copyScale width≤width:=Nat.div_le_self ..
  have price : f.board.batch.maxWidth*f.board.batch.copies≤v.menu.maximum*width := by
    rw [copiesEq,maxEq]
    exact Nat.mul_le_mul_left _ remain
  have ordinary : (if kind (goods:=f.pricedArea.goods) st.plan.bank st.columns u j=none
      then installedBits st.columns u j else 0)≤f.board.batch.maxWidth*f.board.batch.copies := by
    split
    · exact native
    · exact Nat.zero_le _
  exact read.le.trans (ordinary.trans price)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
