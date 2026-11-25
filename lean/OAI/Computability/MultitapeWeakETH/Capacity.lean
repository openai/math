import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Quantitative upper estimate for a small folded graph -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork
noncomputable section

def costCoefficient (W D K R F : ℝ) :=
  2*W*Real.sqrt D*Real.sqrt K + Real.sqrt (8*(1+F)*K) + Real.sqrt (12*K*R)

/-- If P / √log P is at most x² m, the three placement costs together
are at most a constant times x n. The constants use only the fixed fold
ratio, degree, width factor and entropy budget. -/
theorem small_graph_cost {W D K R F x n b m N P H : ℝ}
    (hW : 0 ≤ W) (hD : 0 ≤ D) (hK : 0 ≤ K) (hR : 0 ≤ R) (hF : 0 ≤ F)
    (hx : 0 ≤ x) (xle : x ≤ 1) (hn : 0 ≤ n) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hN : 0 < N) (hP : 0 ≤ P) (hH : 0 ≤ H) (hlog : 1 ≤ Real.log P)
    (graph : P/Real.sqrt (Real.log P) ≤ x^2*m)
    (fold : m ≤ R*N) (pad : m*b ≤ 2*n) (mask : H ≤ F*n) :
    let E := K*P/Real.log P
    W*b*Real.sqrt (D*P)*Real.sqrt E + Real.sqrt (4*b*(n+H))*Real.sqrt E +
      n*Real.sqrt (12*E/N) ≤ costCoefficient W D K R F*x*n := by
  intro E
  have logpos : 0 < Real.log P := by linarith
  have den : 0 < Real.sqrt (Real.log P) := Real.sqrt_pos.mpr logpos
  have Epos : 0 ≤ E := by dsimp [E]; positivity
  have sq : x^2 ≤ x := by nlinarith only [mul_nonneg hx (sub_nonneg.mpr xle)]
  have cap : E ≤ K*x^2*m := by
    rw [mul_assoc]
    apply (show E = K*(P/Real.log P) by dsimp [E]; ring).le.trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply le_trans _ graph
    exact div_le_div_of_nonneg_left hP den (Real.sqrt_le_self_iff.mpr (Or.inr hlog))
  have supply : W*b*Real.sqrt (D*P)*Real.sqrt E ≤ (2*W*Real.sqrt D*Real.sqrt K)*x*n := by
    have identity : Real.sqrt (D*P)*Real.sqrt E =
        Real.sqrt D*Real.sqrt K*(P/Real.sqrt (Real.log P)) := by
      rw [Real.sqrt_mul hD,show E = K*P/Real.log P by rfl,Real.sqrt_div (mul_nonneg hK hP),Real.sqrt_mul hK]
      field_simp
      rw [Real.sq_sqrt hP]
      ring
    calc
      _ = (W*Real.sqrt D*Real.sqrt K)*b*(P/Real.sqrt (Real.log P)) := by
        rw [mul_assoc (W*b),identity]; ring
      _ ≤ (W*Real.sqrt D*Real.sqrt K)*b*(x^2*m) := by gcongr
      _ = (W*Real.sqrt D*Real.sqrt K)*x^2*(m*b) := by ring
      _ ≤ (W*Real.sqrt D*Real.sqrt K)*x*(2*n) := by gcongr
      _ = _ := by ring
  have center : Real.sqrt (4*b*(n+H))*Real.sqrt E ≤ Real.sqrt (8*(1+F)*K)*x*n := by
    rw [← Real.sqrt_mul (by positivity)]
    calc
      _ ≤ Real.sqrt ((4*b*(n+F*n))*(K*x^2*m)) := by gcongr
      _ = Real.sqrt ((4*(1+F)*K*x^2*n)*(m*b)) := by congr 1; ring
      _ ≤ Real.sqrt ((4*(1+F)*K*x^2*n)*(2*n)) := by gcongr
      _ = Real.sqrt ((8*(1+F)*K)*(x*n)^2) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]; ring
  have terminals : Real.sqrt (12*E/N) ≤ Real.sqrt (12*K*R)*x := by
    have top : 12*E ≤ (12*K*R*x^2)*N := by
      calc
        _ ≤ 12*(K*x^2*m) := by gcongr
        _ ≤ 12*(K*x^2*(R*N)) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ Real.sqrt ((12*K*R)*x^2) := Real.sqrt_le_sqrt ((div_le_iff₀ hN).mpr top)
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hx]
  have last := mul_le_mul_of_nonneg_left terminals hn
  unfold costCoefficient
  linarith only [supply,center,last]

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
