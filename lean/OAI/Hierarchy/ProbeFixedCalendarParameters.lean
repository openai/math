import OAI.Hierarchy.ProbeFixedFormatCore
import OAI.Hierarchy.ProtocolRAMCalendarTime

namespace OAI
/-! # Public calendar parameters and the temperatures of its two meshes -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage StripDirectory
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

abbrev depth := publicTiles k v.W-1
abbrev toleranceAt := failureTolerance (publicStages v.W) v.tolerance (probeDensity k v.W)
abbrev cost := boardCost (publicStages v.W) v.depth k v.radius

abbrev payloadPackets := payloadMenu F (publicStages v.W) k v.positive v.radius (Nat.cast_nonneg _)
  v.toleranceAt v.geometry.cutoff.1 v.cost.payload v.cost.payload_nonneg 0
abbrev boughtPackets := purchasedMenu F v.depth k v.positive v.radius (Nat.cast_nonneg _)
  v.toleranceAt v.geometry.cutoff.1 v.cost.purchase v.cost.purchase_nonneg 0

def menu := menuOfShape F (publicStages v.W) v.depth k v.positive v.radius v.toleranceAt v.geometry.cutoff.1

def keepLimit := ⌈2*((v.a:ℝ)+probeBonus v.W)*upperBox (publicStages v.W) v.radius⌉₊

abbrev limit := ⌈2*((v.a:ℝ)+probeBonus v.W)*upperBox (publicStages v.W) v.radius⌉₊
abbrev actualK := v.copyScale*commonWidth v.menu.width
abbrev loss := repairShare (publicStages v.W) v.radius v.toleranceAt

theorem real_times {p : ℕ} (date : p≤v.mesh.inject+v.mesh.cool) :
    (v.finish:ℝ)≤outerTime v.mesh v.finish p ∧ ∀j,(v.finish:ℝ)/2 ≤ reserveTime v.mesh v.finish p j := by
  have f : (v.finish:ℝ)≤1:=by exact_mod_cast v.clock.finish_le
  have f₀ : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
  have c₀ : 0<v.mesh.cool := by rw [v.clock.same_mesh];exact v.clock.inject_pos
  have c : 0<(v.mesh.cool:ℝ):=by exact_mod_cast c₀
  have u₀ : p-v.mesh.inject≤v.mesh.cool:=by omega
  have u : ((p-v.mesh.inject:ℕ):ℝ)≤v.mesh.cool:=by exact_mod_cast u₀
  have zero : 0≤1-(v.finish:ℝ):=by linarith
  have advance : ((p-v.mesh.inject:ℕ):ℝ)*(1-(v.finish:ℝ))/(v.mesh.cool:ℝ)≤1-(v.finish:ℝ) := by
    apply (div_le_iff₀ c).mpr
    exact (mul_le_mul_of_nonneg_right u zero).trans_eq (mul_comm ..)
  have pay : (v.finish:ℝ)≤outerTime v.mesh v.finish p:=by unfold outerTime;linarith
  refine ⟨pay,fun j=>?_⟩
  have live : 0≤outerTime v.mesh v.finish p:=f₀.le.trans pay
  unfold reserveTime
  have nonneg : 0≤(j:ℝ)*(outerTime v.mesh v.finish p/(2*v.mesh.reserveSteps)):=by positivity
  linarith

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
