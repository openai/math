import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI
/-! # Parameters and iteration of the wire-saving compiler -/

namespace Hierarchy.DescentCompiler
open Filter
open scoped Topology

/-- The count of shrink stages is fixed using only the uniform attachment
constant. The degree reservation is evaluated afterwards, so the dyadic rotor
order can be chosen without any circular parameter dependence. -/
theorem choose_phases {ρ A : ℝ} (hρ : 0≤ρ) (strict : ρ<1) (K : ℕ → ℕ) :
    ∃ t : ℕ, 0<t ∧ A*ρ^t≤1/2 ∧ ∃ n₀ : ℕ, ∀ n≥n₀, 4*K t≤2^n := by
  have tends : Tendsto (fun t : ℕ => A*ρ^t) atTop (𝓝 (A*0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ strict)
  have eventual := tends.eventually_lt_const (show A*0<1/2 by ring_nf; norm_num)
  obtain ⟨t,ht,large⟩ := (eventual.and (eventually_gt_atTop 0)).exists
  refine ⟨t,large,ht.le,4*K t,fun n hn => hn.trans ?_⟩
  exact Nat.lt_two_pow_self.le

/-- An affine geometric contraction iterated any number of times. Its additive
error is charged only once per stage and remains bounded by a convergent
geometric series. -/
theorem run_steps {ρ c : ℝ} (hρ : 0≤ρ) (strict : ρ<1) (hc : 0≤c)
    (X : ℕ → ℝ) (step : ∀ i, X (i+1)≤ρ*X i+c) (i : ℕ) :
    X i≤ρ^i*X 0+c/(1-ρ) := by
  have gap : 0<1-ρ := by linarith
  have pay : ρ*(c/(1-ρ))+c=c/(1-ρ) := by
    field_simp [gap.ne']
   ; ring
  induction i with
  | zero => simp only [pow_zero,one_mul]; linarith [div_nonneg hc gap.le]
  | succ i ih =>
    calc
      X (i+1) ≤ ρ*X i+c := step i
      _ ≤ ρ*(ρ^i*X 0+c/(1-ρ))+c := by gcongr
      _ = ρ^(i+1)*X 0+c/(1-ρ) := by rw [pow_succ]; linarith only [pay]

/-- The end-of-epoch wire estimate after J half-contractions from the initial
core mS, including the exterior and packing allowances throughout. -/
theorem end_core {J : ℕ} {mS E c : ℝ} (he : 0≤E) (hc : 0≤c) (hm : 0≤mS)
    (X : ℕ → ℝ) (initial : X 0≤mS)
    (step : ∀ i,X (i+1)≤X i/2+c*(E+mS/(2:ℝ)^J)) :
    X J≤(1+2*c)*(mS/(2:ℝ)^J+E) := by
  have xstep (i : ℕ) : X (i+1)≤(1/2)*X i+c*(E+mS/(2:ℝ)^J) := by linarith only [step i]
  have bound := run_steps (ρ:=1/2) (by norm_num) (by norm_num) (by positivity) X xstep J
  have changePow : (1/2:ℝ)^J=1/(2:ℝ)^J := by rw [div_pow,one_pow]
  rw [changePow] at bound
  have main := mul_le_mul_of_nonneg_left initial (by positivity : (0:ℝ)≤1/(2:ℝ)^J)
  norm_num at bound
  simp only [div_eq_mul_inv,one_mul] at bound main ⊢
  linarith only [bound,main,he]

/-- With R=2^d, r=2^k and (t+1)J stacking steps, the final number of copies
has an explicit quadratic bound on its binary logarithm. -/
theorem stack_exponent {Rexp rexp t J C : ℕ} (hR : Rexp≤C*(J+1)) (hr : rexp≤C*(J+1)) :
    ∃ e≤C*(t+2)*(J+1)^2, (2^Rexp:ℕ)*(2^rexp)^((t+1)*J)=2^e := by
  refine ⟨Rexp+rexp*((t+1)*J),?_,by rw [←pow_mul,←pow_add]⟩
  have a := Nat.mul_le_mul_right ((t+1)*J) hr
  calc
    _ ≤ C*(J+1)+(C*(J+1))*((t+1)*J) := Nat.add_le_add hR a
    _ ≤ _ := by nlinarith only [Nat.zero_le C,Nat.zero_le J,Nat.zero_le t,Nat.zero_le (C*t),Nat.zero_le (C*J^2),Nat.zero_le (C*t*J),Nat.zero_le (C*J)]

end Hierarchy.DescentCompiler

end OAI
