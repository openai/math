import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedElectionRange
import OAI.Hierarchy.ProtocolRAMCalendarRecommendationCap

namespace OAI
/-! # Physical packet-code bounds on every phase and padded key at the actual wide boot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D

theorem wide_menu_range_at (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D) :
    (E).menus.left.Capped (Fintype.card (v.payloadPacketMenu N).index) (v.wideSignedMidAt h width size stock M π o raw) ∧
    (E).menus.right.Capped (Fintype.card v.purchasePacketMenu.index) (v.wideSignedMidAt h width size stock M π o raw) := by
  have ord : (E).Ordered := economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh (P).joint
    (P).catalogue (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have geometry:=v.wideGeometryPrefix h width
  have economic : (E).stop≤(A).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)
  have score : JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh)=(E).ports.base := rfl
  have atJoint : (P).joint.initial≤JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh) :=
    (Nat.le_add_right ..).trans ((JointHeader.order (P).joint h N k).trans (Nat.le_add_right ..))
  have ports : (E).ports.base≤(E).scalar.base := (Nat.le_add_right ..).trans ord.scalarBase.le
  have bounds:=v.recommendation_words P h width
  unfold wideSignedMidAt wideSignedWords chargedMasterWords
  apply (E).recommendation_origin ord (P).joint (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) π
    (fun _=>0) _ (v.catalystMarkets P h width) (v.catalyst_market_layout_at P h width size geometry.2.1 extent)
    (Nat.two_pow_pos _) geometry.1 score.le (geometry.2.1.trans (atJoint.trans score.le))
    (economic.trans ((Nat.le_add_right ..).trans extent))
    (fun j=>economic.trans (v.catalyst_market_low P h width j))
    (CoreRoute.low (v.wideOrder h width) M (WideMemory.groups h v.W)
      (WideMemory.dir h v.W k v.wideJobs) v.depth) _ bounds.1 bounds.2
  intro m x scalar
  apply CoreRoute.low_above
  exact geometry.2.2.trans (atJoint.trans (score.le.trans (ports.trans scalar)))


/-- The complete menu header is resident on the same finite boot whenever its physical word addresses fit. -/
theorem wide_menu_resident_at (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh < 2^Native.wordBits h D Native.copies) :
    (E).menus.Resident (v.wideSignedMidAt h width size stock M π o raw) := by
  obtain ⟨_,_,_,economic,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π o raw room
  exact economic.menus

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
