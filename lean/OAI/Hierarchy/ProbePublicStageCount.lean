import OAI.Hierarchy.ProbePublicCalibration

namespace OAI
namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe ProbeStage

/-- The actual dyadic subdivision used by the paid board has the public stage count. -/
theorem fixed_stage_count (z W : ℕ) : (permutationFabric z (2^W)).shapes.length=publicStages W := by
  rw [show (permutationFabric z (2^W)).shapes.length=2*rounds (2^W)+1 from template_length ..]
  unfold publicStages rounds; omega

/-- The chosen paid chain visits at least as many distinct tiles as there are
stages. Thus the occupancy of all confirmed bought-path tests is at most n. -/
theorem stages_le_purchased_tiles {F : Type*} [Field F] {k W M : ℕ} {p σ Λ ε : ℝ}
    (cfg : PublicCalibration F k p σ Λ W M ε) (hk : 0<k) (z : ℕ) :
    (permutationFabric z (2^W)).shapes.length ≤ publicTiles k W-1+1 := by
  rw [fixed_stage_count,Nat.sub_add_cancel cfg.tiles]
  have heat : 0<(dyadicScale W)^2 := by unfold dyadicScale;positivity
  have steps:=cfg.motion_mass
  have kk : 1≤(k:ℝ) := by exact_mod_cast (show 1≤k from hk)
  have bound : (publicStages W:ℝ)≤32*(k:ℝ)/(dyadicScale W)^2 := by
    apply (le_div_iff₀ heat).2
    change (publicStages W:ℝ)*(dyadicScale W)^2≤1/4 at steps
    linarith
  apply (Nat.cast_le (α:=ℝ)).mp
  exact bound.trans (Nat.le_ceil (32*(k:ℝ)/(dyadicScale W)^2))

end Hierarchy.ProtocolRAM.Calendar

end OAI
