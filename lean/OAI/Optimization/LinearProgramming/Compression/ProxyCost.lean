import OAI.Optimization.LinearProgramming.Compression.ProxyBounds
import OAI.Optimization.LinearProgramming.Compression.PowerBits

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

private theorem size_le_log2_succ (n : ℕ) : n.size ≤ n.log2+1 := by
  cases Nat.eq_zero_or_pos n with
  | inl h => simp [h]
  | inr h => exact Nat.size_le.mpr ((Nat.log2_lt h.ne').mp (Nat.lt_succ_self _))

theorem magnitude_size_le_ratBits (q : ℚ) : q.num.natAbs.size + q.den.size ≤ ratBits q := by
  have h₁ := size_le_log2_succ q.num.natAbs
  have h₂ := size_le_log2_succ q.den
  unfold ratBits
  omega

theorem proxyThreshold_le_ratBits {fuel k : ℕ} {q : ℚ} (hq : 0 < q)
    (hsym : logProxyNumerator fuel k q = none) : 2 ^ fuel ≤ ratBits q :=
  (threshold_le_rat_bits_of_symbolic hq hsym).trans (magnitude_size_le_ratBits q)

private theorem natAbs_le_of_abs_le {x : ℤ} {b : ℕ} (h : |x| ≤ (b : ℤ)) : x.natAbs ≤ b := by
  have hh : (x.natAbs : ℤ) ≤ b := by simpa only [Int.natCast_natAbs] using h
  exact_mod_cast hh

/-- On a nonempty large-log branch, the rational compared to one has bit length polynomial
in the number of terms and the maximum bit length of an input magnitude. The bound
remains independent of the potentially enormous numerical cutoff. -/
theorem computedProxyProduct_registerBounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fuel k B : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^k * A ≤ 2^fuel)
    (hsym : ∃ j, logProxyNumerator fuel k (mag j) = none) :
    let data i := logProxyNumerator fuel k (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let bound := 9 + 4 * (4 * B^2) + Fintype.card ι * (3 + (4*B)*B)
    ratBits (proxyProduct large (2^(k+2)) c a (fun i => (data i).getD 0) mag) ≤ bound ∧
    ∀ w ∈ (proxyPowerTrace large (2^(k+2)) c a (fun i => (data i).getD 0) mag).2,
      ratBits w ≤ bound := by
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  obtain ⟨j, hj⟩ := hsym
  have hT : (2 : ℤ)^fuel ≤ B := by exact_mod_cast (proxyThreshold_le_ratBits (hm j) hj).trans (hbits j)
  have hT2 : ((2 : ℤ)^fuel)^2 ≤ (B : ℤ)^2 := by gcongr
  obtain ⟨hoff, hexp⟩ := logProxy_exponent_bounds fuel k c a mag hm hform hcut
  have hk : (clearedProxyOffset large (2^(k+2)) c a (fun i => (data i).getD 0)).natAbs ≤
      4*B^2 := by
    apply natAbs_le_of_abs_le
    push_cast
    exact hoff.trans (mul_le_mul_of_nonneg_left hT2 (by norm_num))
  have he (i) (_ : i ∈ large) : (((2^(k+2) : ℕ) : ℤ) * a i).natAbs ≤ 4*B := by
    apply natAbs_le_of_abs_le
    push_cast
    exact (hexp i).trans (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hcard := Nat.mul_le_mul_right (3 + (4*B)*B) (Finset.card_le_univ large)
  constructor
  · exact (ratBits_proxyProduct_le large (2^(k+2)) c a (fun i => (data i).getD 0) mag
      (4*B^2) (4*B) B hk he (fun i _ => hbits i)).trans (Nat.add_le_add_left hcard _)
  · intro w hw
    have hn := proxyPowerTrace_intermediate large (2^(k+2)) c a (fun i => (data i).getD 0) mag
      (4*B^2) (4*B) B hk he (fun i _ => hbits i) w hw
    omega

/-- The number of arithmetic operations in the mixed product uses only the logarithm of
the cutoff. This bound is independent of the bit lengths of the supplied magnitudes. -/
theorem computedProxyProduct_steps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fuel k : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ) (hm : ∀ i, 0 < mag i)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^k * A ≤ 2^fuel) :
    let data i := logProxyNumerator fuel k (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    (proxyPowerTrace large (2^(k+2)) c a (fun i => (data i).getD 0) mag).2.length ≤
      2 * (2*fuel+3) + 2 + Fintype.card ι * (2*(fuel+3)+2) := by
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  obtain ⟨hoff, hexp⟩ := logProxy_exponent_bounds fuel k c a mag hm hform hcut
  have ho : (clearedProxyOffset large (2^(k+2)) c a (fun i => (data i).getD 0)).natAbs ≤
      2^(2*fuel+2) := by
    apply natAbs_le_of_abs_le
    push_cast
    calc
      _ ≤ 4*((2 : ℤ)^fuel)^2 := hoff
      _ = (2 : ℤ)^(2*fuel+2) := by rw [pow_add, Nat.mul_comm 2 fuel, pow_mul]; ring
  have he (i) : (((2^(k+2) : ℕ) : ℤ)*a i).natAbs ≤ 2^(fuel+2) := by
    apply natAbs_le_of_abs_le
    push_cast
    calc
      _ ≤ 4*(2 : ℤ)^fuel := hexp i
      _ = (2 : ℤ)^(fuel+2) := by rw [pow_add]; ring
  have hs : ∑ i ∈ large, (2*(((2^(k+2) : ℕ) : ℤ)*a i).natAbs.size+2) ≤
      Fintype.card ι * (2*(fuel+3)+2) := calc
    _ ≤ ∑ _i ∈ large, (2*(fuel+3)+2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := Nat.size_le_size (he i)
      rw [Nat.size_pow] at h
      omega
    _ ≤ _ := by
      simpa using Nat.mul_le_mul_right (2*(fuel+3)+2) (Finset.card_le_univ large)
  have hh := Nat.size_le_size ho
  rw [Nat.size_pow] at hh
  have hl := proxyPowerTrace_length large (2^(k+2)) c a (fun i => (data i).getD 0) mag
  change (proxyPowerTrace large (2^(k+2)) c a (fun i => (data i).getD 0) mag).2.length ≤ _
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
