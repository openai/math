import OAI.Hierarchy.DescentCompilerIteration
import OAI.Hierarchy.DescentStackScale

namespace OAI
/-! # The actual package chooses a quasipolynomial number of copies -/

namespace Hierarchy.DescentCompiler

/-- The number of copies has the bit budget of OpenNetworks, including
the raw width of each stack, uniformly before replacement or query data. -/
theorem package_log {h J t C outer group stack : ℕ} (positive : 0<stack)
    (maxWidth : stack≤h) (age : 2^J≤h)
    (capOuter : outer≤C*(J+1)) (capGroup : group≤C*(J+1)) :
    let d := 2^outer*(2^group)^((t+1)*J)*stack
    0<d ∧ Real.logb 2 (d:ℝ) ≤ (C*(t+2)+1:ℕ)*(Real.logb 2 (2*(h:ℝ)))^2 := by
  obtain ⟨e,limit,rows⟩ := stack_exponent capOuter capGroup (t:=t)
  dsimp only
  rw [rows]
  refine ⟨Nat.mul_pos (Nat.two_pow_pos _) positive,?_⟩
  have hh : (0:ℝ)<h := by exact_mod_cast positive.trans_le maxWidth
  have hs : (0:ℝ)<stack := by exact_mod_cast positive
  have hbase : (1:ℝ)<2 := by norm_num
  have hm : (stack:ℝ)≤h := by exact_mod_cast maxWidth
  have hj : (2:ℝ)^J≤h := by exact_mod_cast age
  have lb := Real.logb_le_logb_of_le hbase (by positivity : 0<(2:ℝ)^J) hj
  rw [Real.logb_pow,Real.logb_self_eq_one hbase,mul_one] at lb
  have ls := Real.logb_le_logb_of_le hbase hs hm
  have lpos := Real.logb_nonneg hbase (show 1≤(h:ℝ) by exact_mod_cast positive.trans_le maxWidth)
  have big := Real.logb_mul (b:=2) (by norm_num : (2:ℝ)≠0) hh.ne'
  rw [Real.logb_self_eq_one hbase] at big
  have powBound := sq_le_sq' (by linarith : -(1+Real.logb 2 h)≤(J:ℝ)+1) (by linarith : (J:ℝ)+1≤1+Real.logb 2 h)
  have cost : (e:ℝ)≤((C:ℝ)*(t+2))*(J+1)^2 := by exact_mod_cast limit
  have cb := mul_le_mul_of_nonneg_left powBound (show 0≤(C:ℝ)*(t+2) by positivity)
  push_cast
  rw [Real.logb_mul (by positivity : (2:ℝ)^e≠0) hs.ne',Real.logb_pow,
    Real.logb_self_eq_one hbase,mul_one,big]
  nlinarith only [cost,cb,ls,sq_nonneg (Real.logb 2 h),lpos]

end Hierarchy.DescentCompiler

end OAI
