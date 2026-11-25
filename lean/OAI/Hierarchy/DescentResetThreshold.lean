import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The clipped threshold for one measured grazing contact -/
namespace Hierarchy.DescentPlainTerminal.Suffix
/-- A single traffic total for the entire directed physical host edge. -/
def threshold (K scale j total cap : ℕ) : ℕ := min cap ((K*total+scale*2^j)/(K*2^j))

theorem crossed (K scale j total bound n : ℕ) (positive : 0<K) (fits : n≤bound) :
    threshold K scale j total bound<n ↔ K*total+scale*2^j<K*2^j*n := by
  have nonempty : 0<K*2^j:=Nat.mul_pos positive (Nat.two_pow_pos _)
  simp only [threshold,min_lt_iff,not_lt.mpr fits,false_or]
  rw [Nat.div_lt_iff_lt_mul nonempty,Nat.mul_comm n (K*2^j)]

end Hierarchy.DescentPlainTerminal.Suffix

end OAI
