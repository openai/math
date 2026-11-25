import OAI.Hierarchy.ProbeFixedCalendarParameters
import OAI.Hierarchy.ProtocolRAMCalendarRouteRange
import OAI.Hierarchy.ProbeCommodityBounds
import OAI.Hierarchy.ProbeOuterCharges
import OAI.Hierarchy.ProbeRepairReplayAccount

namespace OAI
/-! # The public cost and mesh bounds for replay at an actual outer calendar time -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem phase_clock (j : ℕ) :
    outerTime v.mesh v.finish j=phaseTime v.finish v.mesh.inject j := by
  unfold outerTime phaseTime clockTime
  rw [v.clock.same_mesh]
  ring

theorem replay_clock (j u : ℕ) :
    reserveTime v.mesh v.finish j u=replayTime (phaseTime v.finish v.mesh.inject j) v.mesh.reserveSteps u := by
  unfold reserveTime replayTime
  rw [v.phase_clock]

theorem inject_clock {j : ℕ} (hj : j≤v.mesh.inject) : phaseTime v.finish v.mesh.inject j=1 :=
  (v.phase_clock j).symm.trans (injection_time _ _ hj)

theorem acquisition_dimension (z : ℕ) :
    (Fintype.card (Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k):ℝ)=
      (1+2*(publicStages v.W)*k:ℕ)*(2^z:ℕ) := by
  have stages : CoreBoard.Stages z (2^v.W) = publicStages v.W := fixed_stage_count z v.W
  rw [commodity_count,Fintype.card_fin,stages,Nat.cast_mul,mul_comm]

theorem acquisition_box (z : ℕ) (i : Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k) :
    routeCap (CoreBoard.Stages z (2^v.W)) v.radius (PurchaseInventory.lane i) ∈
      Set.Icc 0 (upperBox (publicStages v.W) v.radius) := by
  simpa only [←fixed_stage_count z v.W,upperBox] using
    routeCap_range (k:=k) (h:=z) (d:=2^v.W) v.radius (Nat.cast_nonneg _) i

theorem acquisition_fee {z count : ℕ} (size : count≤2^z) :
    (count:ℝ)*(Λ*(dyadicScale v.W)^p)≤(2^z:ℕ)*(Λ*(dyadicScale v.W)^p) := by
  have factor : 0≤(dyadicScale v.W)^p := Real.rpow_nonneg (by unfold dyadicScale; positivity) _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast size) (mul_nonneg v.capacityPrice.le factor)

theorem acquisition_fuel :
    Λ*(dyadicScale v.W)^p+(1+2*(publicStages v.W)*k:ℕ)*(v.limit:ℝ)*upperBox (publicStages v.W) v.radius+
      probeDensity k v.W*purchaseReward k v.W/8≤
    (v.mesh.innerFuel:ℝ)*(v.loss*v.menu.margin/(8*(v.actualK:ℝ))) := v.clock.saturated

theorem acquisition_mesh (z width phase : ℕ) (wide : v.widthFloor≤width)
    (scheduled : phase≤v.mesh.inject+v.mesh.cool) :
    let n:=Fintype.card (Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k)
    let U:=upperBox (publicStages v.W) v.radius
    let s:=phaseTime v.finish v.mesh.inject phase
    (v.mesh.reserveSteps:ℝ)*((n:ℝ)*(2*U/width+
      (((v.limit:ℝ)+2+v.limit)/v.mesh.reserveSteps)^2/(2*s*v.a)))≤
      (2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/8 := by
  dsimp only
  exact v.clock.replay width wide _ ((v.real_times scheduled).1.trans_eq (v.phase_clock phase))
    (2^z) _ (v.acquisition_dimension z).le

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
