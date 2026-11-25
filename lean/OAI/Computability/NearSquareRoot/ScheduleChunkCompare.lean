import OAI.Computability.NearSquareRoot.ScheduleChunkWrapper
import OAI.Computability.NearSquareRoot.ScheduleAsymptotic

/-!
# Comparison clocks for a fixed split

A single eventual cutoff puts every short multiplication at or above the
candidate's threshold. For this split, the controller scans, the trial's
halt test and all digit multiplications satisfy its original logarithmic
exponent on the full length.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open Filter ChunkTask

theorem fixed_deadline (C k : ℕ) (T : ℕ → ℕ) (e A : ℝ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (time : ∀ᶠ u : ℕ in atTop, (T u : ℝ) ≤ A*u*logScale u^e) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, ∀ p : Input, p.n = n → p.k = k →
      (((6*C+16)*((p.count+1)*(p.n+T p.u+1))+1 : ℕ) : ℝ) ≤ H*n*logScale n^e := by
  let r := 2^k
  let f := (6*C+16)*(r*r+1)
  refine ⟨(f:ℝ)*(A+2)+1,by positivity,?_⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp time
  filter_upwards [eventually_ge_atTop (1:ℕ), eventually_ge_atTop (r*M)] with n hn hc
  intro p hp hk
  have hr : p.r = r := by simp only [Input.r,r,hk]
  have hc' : p.r*M ≤ p.n := by simpa only [hr,hp] using hc
  have hu := hM p.u (Uniform.cutoff_le_chunkWidth p.positive hc')
  have ulo : (0:ℝ) < p.u := by exact_mod_cast p.width_pos
  have ule : (p.u:ℝ) ≤ n := by exact_mod_cast hp ▸ p.width_le
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have nl : 1 ≤ logScale n := by simp only [logScale]; linarith [Real.log_nonneg n1]
  have wn : 1 ≤ logScale n ^ e := Real.one_le_rpow nl he
  have ul : 0 ≤ logScale p.u := by
    have h1 : (1:ℝ) ≤ p.u := by exact_mod_cast p.width_pos
    simp only [logScale]
    linarith [Real.log_nonneg h1]
  have lelog : logScale p.u ≤ logScale n := by
    unfold logScale; exact add_le_add_right (Real.log_le_log ulo ule) _
  have wle : logScale p.u ^ e ≤ logScale n ^ e := Real.rpow_le_rpow ul lelog he
  let w := (n:ℝ)*logScale n^e
  have hnu : (n:ℝ) ≤ w := by dsimp [w]; nlinarith
  have w1 : 1 ≤ w := n1.trans hnu
  have htu : (T p.u : ℝ) ≤ A*w :=
    hu.trans (by dsimp [w]; rw [← mul_assoc]; gcongr)
  have count : p.count = r*r := by simp only [Input.count,hr]
  rw [hp,count]
  push_cast [f]
  change _ ≤ (((6:ℝ)*C+16)*((r:ℝ)*r+1)*(A+2)+1) * n * logScale n^e
  rw [mul_assoc _ (n:ℝ)]
  change _ ≤ (((6:ℝ)*C+16)*((r:ℝ)*r+1)*(A+2)+1)*w
  have x : (n:ℝ)+T p.u+1 ≤ (A+2)*w := by nlinarith
  calc
    _ = ((6:ℝ)*C+16)*((r:ℝ)*r+1)*(n+T p.u+1)+1 := by ring
    _ ≤ ((6:ℝ)*C+16)*((r:ℝ)*r+1)*((A+2)*w)+w := by gcongr
    _ = _ := by ring

end ChunkControl

end NearSquareRoot
end Computability
end OAI
