import OAI.Hierarchy.TaggedWideControl
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # Physical input-word and look-up footprint along the allowed polynomial payload range -/
noncomputable section
namespace Hierarchy.Tagged.WideParent
open Filter

theorem fixed_mul_width {κ A : ℝ} (C : ℕ) :
    ∀ᶠ x : WideParent κ A in large κ A,C*x.w+1≤2^x.h := by
  let B:=max 0 A
  have hB : 0≤B:=le_max_left ..
  have poly:=GapScale.eventual_polynomial 0 ((C:ℝ)+1) B hB
  have heights : Tendsto (h (κ:=κ) (A:=A)) (large κ A) atTop:=tendsto_comap
  filter_upwards [heights.eventually poly] with x price
  have F:=x.formats
  have wbound : (x.w:ℝ)≤(x.h:ℝ)^A:=x.property.1.2.2
  have hpos : 0≤(x.h:ℝ):=Nat.cast_nonneg _
  have wide : (x.w:ℝ)≤(2*(x.h:ℝ))^B :=
    wbound.trans ((Real.rpow_le_rpow_of_exponent_le F.1.le (le_max_right ..)).trans
      (Real.rpow_le_rpow hpos (by linarith) hB))
  have one : (1:ℝ)≤(2*(x.h:ℝ))^B:=Real.one_le_rpow (by linarith [F.1]) hB
  have room : ((C:ℝ)+1)*(2*(x.h:ℝ))^B ≤ (2:ℝ)^x.h := by
    simpa [gap] using price
  rw [add_mul,one_mul] at room
  have bound := (add_le_add (mul_le_mul_of_nonneg_left wide (Nat.cast_nonneg C)) one).trans room
  exact_mod_cast bound

end Hierarchy.Tagged.WideParent

end
end OAI
