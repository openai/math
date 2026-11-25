import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentCopyLog

namespace OAI
/-! # The logarithmic copy bound including the terminal group of a physical schedule -/

namespace Hierarchy.DescentCompiler

theorem AtomSchedule.open_copy_count (S : AtomSchedule) (τ κ k h p₀ : ℕ)
    (outer : S.baseGroups=2^(τ*(S.height+1))) (radix : S.radix=2^k)
    (bits : k≤κ*(S.height+1)) (positive : 0<p₀) (width : p₀≤h)
    (age : 2^S.height≤h) :
    0<S.copies*p₀ ∧ Real.logb 2 (S.copies*p₀:ℕ) ≤
      ((τ+κ)*(S.rounds+2)+1:ℕ)*(Real.logb 2 (2*(h:ℝ)))^2 := by
  have window : τ*(S.height+1)+k ≤ (τ+κ)*(S.height+1) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_left bits _
  have group : k≤(τ+κ)*(S.height+1) := window.trans' (Nat.le_add_left ..)
  have rate := package_log (t:=S.rounds) positive width age window group
  have whole : S.copies=2^(τ*(S.height+1)+k)*(2^k)^((S.rounds+1)*S.height) := by
    rw [copies,outer,radix,length,pow_succ,pow_add]
    ring
  simpa only [whole] using rate

end Hierarchy.DescentCompiler

end OAI
