import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedBroadcastPages

namespace OAI
/-! # Both full charge pages on the physical signed boot output -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open CoreRoute StripChart CatalystArchive
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D Native.copies
local notation "A" => v.privateArena P h width
local notation "H" => v.publicHeader P h width
local notation "fees" => StripChart.charges F (v.sized (v.seed P h width) width) v.cost (H).stop
local notation "freq" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)

theorem wide_charge_image (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) :
    ∃ rest : Boot.Tape h D,∀x,(H).stop≤x→x<(fees).stop→
      v.wideSignedMidAt h width size stock M π o raw x=(fees).words rest x := by
  let origin:=v.wideSignedWords h width stock M π o raw
  let low:=CoreRoute.low (v.wideOrder h width) M (WideMemory.groups h v.W)
    (WideMemory.dir h v.W k v.wideJobs) v.depth
  obtain ⟨rest,eq⟩ : ∃rest : Boot.Tape h D,origin=JointHeader.words (P).joint h D N k freq π
      (fun _=>0) ((H).ports.words (low ((H).scalar.words ((H).vectorMemory ((fees).words rest))))) := ⟨_,rfl⟩
  have geometry:=v.wideGeometryPrefix h width
  have ord : (H).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh
    (P).joint (P).catalogue (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have joint : (P).joint.initial≤JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh) :=
    (Nat.le_add_right ..).trans ((JointHeader.order (P).joint h N k).trans (Nat.le_add_right ..))
  have score : JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh)=(H).ports.base := rfl
  have board : (P).joint.initial≤(H).ports.base:=joint.trans score.le
  have scalar : (P).joint.initial≤(H).scalar.base:=
    board.trans ((Nat.le_add_right .. : (H).ports.base≤(H).ports.stop).trans ord.scalarBase.le)
  have first : (fees).stop≤(A).first :=
    (Nat.le_add_right .. : (v.emptyReserve P h width).base≤_).trans (v.emptyReserve_end_le_first P h width)
  refine ⟨rest,?_⟩
  intro x left right
  change Boot.booted (v.catalystMarkets P h width) size origin x=_
  rw [eq]
  exact (H).original_tail ord (P).joint freq π (fun _=>0) ((fees).words rest) (v.catalystMarkets P h width)
    (v.catalyst_market_layout_at P h width size geometry.2.1 extent) Nat.one_le_two_pow
    geometry.1 score.le (geometry.2.1.trans board) x left
    (fun i=>right.trans_le (first.trans (v.catalyst_market_low P h width i)))
    (right.trans_le (first.trans ((Nat.le_add_right .. : (A).first≤(A).endAddress v.mesh).trans extent)))
    low (fun m y hy=>CoreRoute.low_above _ _ _ _ _ m y (geometry.2.2.trans (scalar.trans hy)))

/-- The two initialized full banks are bounded even at unused and padded addresses. -/
theorem wide_broadcast_origin (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) :
    let mem:=v.wideSignedMidAt h width size stock M π o raw
    (∀x,(fees).payload.base≤x→x<(fees).payload.stop→(mem x).val≤v.maxBits) ∧
    (∀x,(fees).purchase.base≤x→x<(fees).purchase.stop→(mem x).val≤v.maxBits) := by
  intro mem
  obtain ⟨rest,same⟩:=v.wide_charge_image h width size extent stock M π o raw
  obtain ⟨first,second⟩:=v.broadcast_charge_image P h width rest
  have middle : (fees).payload.stop=(fees).purchase.base:=rfl
  have bridge : (fees).payload.stop≤(fees).stop:=middle.le.trans (Nat.le_add_right ..)
  constructor
  · intro x lo hi
    change (v.wideSignedMidAt h width size stock M π o raw x).val≤_
    rw [same x lo (hi.trans_le bridge)]
    exact first x lo hi
  · intro x lo hi
    have lower : (H).stop≤(fees).payload.stop:=Nat.le_add_right ..
    change (v.wideSignedMidAt h width size stock M π o raw x).val≤_
    rw [same x (lower.trans (middle.le.trans lo)) hi]
    exact second x lo hi

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
