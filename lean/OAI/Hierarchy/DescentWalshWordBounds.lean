import OAI.Hierarchy.DescentWalshPrecisionNumbers
import OAI.Hierarchy.DescentPackedWalshLanes
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Scalar bounds for the dyadic Walsh packing word -/
namespace Hierarchy.DescentWalshPrecision
open DescentPackedWalsh

theorem gain_le (m f K u : ℕ) : gainBits m f K u≤bits m f K u := by unfold bits;omega

theorem packed_key {m h b g : ℕ} (pos : 0<b) (wide : 8*b≤h/2) (gb : g≤b) :
    g+b*2^laneBits m h b≤h/2 := by
  have room : 8*b≤h := wide.trans (Nat.div_le_self ..)
  have terms : 0<h/(8*b) := Nat.div_pos room (by omega)
  have lanes : 2^laneBits m h b≤h/(8*b) :=
    (Nat.pow_le_pow_right (by decide) (Nat.min_le_right ..)).trans (Nat.pow_log_le_self 2 terms.ne')
  have small := (Nat.le_div_iff_mul_le (by omega : 0<8*b)).mp lanes
  have comm : 2^laneBits m h b*(8*b)=8*(b*2^laneBits m h b) := by ring
  rw [comm] at small
  omega

/-- Every fixed quadratic polynomial in the binary logarithm is eventually
below the external payload height. -/
theorem eventually_log_square (C : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,C*(Nat.log 2 h+1)^2≤h :=
  DescentCompiler.dyadic_log_room C 2

end Hierarchy.DescentWalshPrecision

end OAI
