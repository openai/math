import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI
/-! # Dyadic loss in the expected number of propagated colony splits -/

namespace Hierarchy.DescentColonies
open scoped BigOperators

private theorem reciprocal_sum (m : ℕ) : (∑ j∈Finset.range m, (1/2:ℝ)^j)≤2 := by
  have h := geom_sum_mul_neg (1/2:ℝ) m
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) m]

/-- Splitting at the first dyadic level above x bounds the minimum of the
increasing position-count cap and the decreasing pair-collision cap. -/
theorem crossing_sum (x : ℝ) (hx : 0≤x) (m : ℕ) :
    (∑ j∈Finset.range m, min ((2:ℝ)^j) (x^2 / 2^j)) ≤4*x := by
  have count_cap (j : ℕ) : min ((2:ℝ)^j) (x^2/2^j)≤2^j := min_le_left _ _
  have tail (n : ℕ) :
      (∑ j∈Finset.range m, min ((2:ℝ)^(n+j)) (x^2 / 2^(n+j))) ≤ 2*(x^2/2^n) := by
    calc
      _ ≤ ∑ j∈Finset.range m, (x^2/2^n)*(1/2:ℝ)^j := by
        apply Finset.sum_le_sum
        intro j _
        apply (min_le_right _ _).trans_eq
        rw [pow_add,div_pow,one_pow]
        ring
      _ = (x^2/2^n)*∑j∈Finset.range m,(1/2:ℝ)^j := (Finset.mul_sum ..).symm
      _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_left (reciprocal_sum m) (by positivity : 0≤x^2/2^n)
  by_cases small : x≤1
  · have h := tail 0
    simp only [zero_add,pow_zero,div_one] at h
    nlinarith [mul_nonneg hx (sub_nonneg.mpr small)]
  obtain ⟨r,hr⟩ := exists_nat_ge x
  have up : ∃ n : ℕ,x≤(2:ℝ)^n := ⟨r,hr.trans (by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le)⟩
  let n := Nat.find up
  have hi : x≤(2:ℝ)^n := Nat.find_spec up
  have nz : n≠0 := fun h => small (by simpa [h] using hi)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero nz
  have low : (2:ℝ)^n≤2*x := by
    have tooSmall : ¬x≤(2:ℝ)^k := Nat.find_min up (show k<n by omega)
    rw [hk,pow_succ]
    linarith
  have left : (∑ j∈Finset.range n, min ((2:ℝ)^j) (x^2 / 2^j))≤2*x := by
    apply (Finset.sum_le_sum (s:=Finset.range n) fun j _ => count_cap j).trans
    have g := geom_sum_mul (2:ℝ) n
    linarith
  have right := tail n
  have t : x^2/(2:ℝ)^n≤x := (div_le_iff₀ (by positivity)).2 (by nlinarith [mul_nonneg hx (sub_nonneg.mpr hi)])
  have extend : (∑ j∈Finset.range m, min ((2:ℝ)^j) (x^2 / 2^j)) ≤
      ∑ j∈Finset.range (n+m), min ((2:ℝ)^j) (x^2 / 2^j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => le_min (by positivity) (by positivity))
  rw [Finset.sum_range_add] at extend
  linarith

/-- The actual bound at propagation gap s is linear in the total mass x and
decays as (√2)^(-s), uniformly in the height of the interval tree. -/
theorem depth_gap_sum (x : ℝ) (hx : 0≤x) (s m : ℕ) :
    (∑ t∈Finset.range m, min ((2:ℝ)^t) (2*x^2/2^(s+t))) ≤
      4*Real.sqrt 2*x/(Real.sqrt 2)^s := by
  let z := Real.sqrt 2*x/(Real.sqrt 2)^s
  have h := crossing_sum z (by dsimp [z]; positivity) m
  have sqrtSq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have denom : ((Real.sqrt 2)^s)^2 = 2^s := by rw [← pow_mul,mul_comm,pow_mul,sqrtSq]
  have identity (t : ℕ) : z^2/(2:ℝ)^t=2*x^2/2^(s+t) := by
    dsimp [z]
    rw [div_pow,mul_pow,sqrtSq,denom,pow_add]
    field_simp
  simp_rw [identity] at h
  calc
    _ ≤ 4*z := h
    _ = _ := by dsimp [z];ring

end Hierarchy.DescentColonies

end OAI
