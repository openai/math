import OAI.Hierarchy.DescentDyadicMixing

namespace OAI
/-! # Choosing one dyadic factor for all exceptional load and padding -/

namespace Hierarchy.DescentColonies
open Filter DescentBaseVariance
open scoped Topology

/-- Independent of all input sizes and loads, choose f large enough for the
actual exceptional-base factor and for the required rotor padding capacity. -/
theorem choose_grouping_factor (K δ : ℝ) (tolerance : 0<δ) (padding : ℕ) :
    let r := (2:ℝ)^(1/8:ℝ)
    let c := 1/(r-1)+1/(1-r/2)
    ∃ f : ℕ,padding≤2^f ∧ 128*c*((2:ℝ)^f)^(-(7/8):ℝ) + 4*K^2/(2:ℝ)^f ≤δ := by
  let r := (2:ℝ)^(1/8:ℝ)
  let c := 1/(r-1)+1/(1-r/2)
  have pos : 0<r := by dsimp [r];positivity
  have lt : r<2 := by
    dsimp [r]
    conv_rhs => rw [←Real.rpow_one (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have first := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0≤r/2) (by linarith : r/2<1)).const_mul (128*c)
  have second := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)).const_mul (4*K^2)
  have total : Tendsto (fun f : ℕ => 128*c*(r/2)^f+4*K^2*(1/2:ℝ)^f) atTop (𝓝 0) := by
    simpa using first.add second
  obtain ⟨f,small,large⟩ := ((total.eventually_lt_const tolerance).and (eventually_ge_atTop padding)).exists
  refine ⟨f,large.trans Nat.lt_two_pow_self.le,?_⟩
  rw [←root_eighth_decay f]
  change 128*c*(r/2)^f+4*K^2/2^f≤δ
  simpa only [div_pow (1:ℝ) 2 f,one_pow,mul_one_div] using small.le

/-- If the native base allocation and original core both obey their budgets,
the absolute exceptional load can be made a δ fraction of the total mass and
packing allowance by using the previously chosen grouping exponent. -/
theorem bad_fraction {mass span core bad K θ δ : ℝ} {f : ℕ}
    (massPos : 0≤mass) (budget : span≤4*mass) (oldCore : core≤mass) (hθ : 0≤θ)
    (paid : bad≤4*(span*(8*θ)+K^2*core/(2:ℝ)^f))
    (factor : 128*θ+4*K^2/(2:ℝ)^f ≤δ) : bad≤δ*mass := by
  have spans := mul_le_mul_of_nonneg_right budget (by positivity : 0≤8*θ)
  have cores := mul_le_mul_of_nonneg_left oldCore (by positivity : 0≤K^2/(2:ℝ)^f)
  have main := mul_le_mul_of_nonneg_right factor massPos
  simp only [div_eq_mul_inv] at paid cores main
  nlinarith only [paid,spans,cores,main]

end Hierarchy.DescentColonies

end OAI
