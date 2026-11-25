import OAI.Hierarchy.DescentSeedTokenNumbers
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
/-! # The shared lookup for the initially packed role fits below the number of hosts -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup DescentPackedSeed DescentSeedRoot Filter
open DescentPackedSeed.Primitive

theorem source_token_exponent (h s : ℕ) :
    4*(roleBits s*pieces h s) ≤ 3*h :=by
  let d:=digitsNeeded s
  have bound:=role_bound_short s
  have pos : 1 ≤ d :=Nat.zero_lt_succ _
  have small : roleBits s ≤ 12*d :=by dsimp only [d] at *;omega
  have half : 2*(pieces h s*(8*d)) ≤ h :=by
    apply (Nat.mul_le_mul_left 2 (lanes_fit h (8*d))).trans
    simpa only [Nat.mul_comm 2] using Nat.div_mul_le_self h 2
  have b:=Nat.mul_le_mul_right (pieces h s) small
  nlinarith only [b,half]

/-- A polynomial number of fixed short truth tables is covered by the initial
public vertex capacity. The degree is independent of the input height. -/
theorem small_role_tables (K d : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀e:ℕ,4*e ≤ 3*h → K*(h+3)^d*2^e ≤ 2^h :=by
  let C:=K*10^d
  have limit := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) d
    (by norm_num : (1:ℝ) < 2)).const_mul_left (C:ℝ)
  have cost : ∀ᶠ x : ℕ in atTop,C*x^d ≤ 2^x :=by
    filter_upwards [limit.def zero_lt_one] with x bound
    have bound' : (C:ℝ)*(x:ℝ)^d ≤ (2:ℝ)^x :=by
      simpa [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (C:ℝ)*(x:ℝ)^d by positivity),
        abs_of_nonneg (show 0 ≤ (2:ℝ)^x by positivity)] using bound
    exact_mod_cast bound'
  obtain ⟨n,past⟩:=eventually_atTop.mp cost
  filter_upwards [eventually_ge_atTop (4*(n+1))] with h large
  intro e covered
  let age:=h/4
  have nle : n ≤ age:=by dsimp [age];omega
  have sides : h+3 ≤ 10*age :=by dsimp [age];omega
  have ex : age+e ≤ h :=by dsimp [age];omega
  calc
    K*(h+3)^d*2^e ≤ K*(10*age)^d*2^e :=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sides _))
    _=C*age^d*2^e :=by rw [mul_pow];dsimp [C];ring
    _ ≤ 2^age*2^e:=Nat.mul_le_mul_right _ (past _ nle)
    _ ≤ 2^h :=by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) ex

end Hierarchy.DescentDatedSeedStartup

end OAI
