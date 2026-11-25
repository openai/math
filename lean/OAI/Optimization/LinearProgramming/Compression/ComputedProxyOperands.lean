import OAI.Optimization.LinearProgramming.Compression.ProxyPowerOperands
import OAI.Optimization.LinearProgramming.Compression.ProxyCost

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

private theorem natAbs_le_of_abs_bound {x : ℤ} {b : ℕ} (h : |x| ≤ (b : ℤ)) : x.natAbs ≤ b := by
  have h' : (x.natAbs : ℤ) ≤ b := by simpa only [Int.natCast_natAbs] using h
  exact_mod_cast h'

/-- The cleared constant and each individual power exponent fit the source's
dimension-controlled bit budget, including queries without any symbolic terms. -/
theorem logProxy_exponent_natAbs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fuel prec : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (hform : |c| + ∑ i, |a i| ≤ A)
    (hcut : (2 : ℤ)^prec * A ≤ 2^fuel) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let offset := clearedProxyOffset large D c a (fun i => (data i).getD 0)
    offset.natAbs ≤ 2^(2*fuel+2) ∧ ∀ i, ((D : ℤ)*a i).natAbs ≤ 2^(fuel+2) := by
  obtain ⟨hoff,hexp⟩ := logProxy_exponent_bounds fuel prec c a mag hm hform hcut
  constructor
  · apply natAbs_le_of_abs_bound
    push_cast
    calc
      _ ≤ 4*((2 : ℤ)^fuel)^2 := hoff
      _ = 2^(2*fuel+2) := by rw [pow_add, Nat.mul_comm 2 fuel, pow_mul]; ring
  · intro i
    apply natAbs_le_of_abs_bound
    push_cast
    calc
      _ ≤ 4*(2 : ℤ)^fuel := hexp i
      _ = 2^(fuel+2) := by rw [pow_add]; ring

/-- Numeric exponent bounds in input length, and a separate bit-tape bound in the
dimension-controlled cutoff, for the actual selected terms. -/
theorem computedProxy_operand_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fuel prec B : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel)
    (hsym : ∃ j, logProxyNumerator fuel prec (mag j) = none) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := 2^(prec+2)
    let offset := clearedProxyOffset large D c a (fun i => (data i).getD 0)
    let ps := proxyPowerOperands large.toList offset D a mag
    offset.natAbs ≤ 4*B^2 ∧ (∀ i, ((D : ℤ)*a i).natAbs ≤ 4*B) ∧
      (ps.map fun p => 2*p.2.natAbs.size+3).sum ≤
        2*(2*fuel+3)+3+Fintype.card ι*(2*(fuel+3)+3) := by
  let data i := logProxyNumerator fuel prec (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  let D : ℕ := 2^(prec+2)
  let grid i := (data i).getD 0
  let offset := clearedProxyOffset large D c a grid
  let ps := proxyPowerOperands large.toList offset D a mag
  obtain ⟨j,hj⟩ := hsym
  have hT : (2 : ℤ)^fuel ≤ B := by exact_mod_cast (proxyThreshold_le_ratBits (hm j) hj).trans (hbits j)
  have hT₂ : ((2 : ℤ)^fuel)^2 ≤ (B : ℤ)^2 := by gcongr
  obtain ⟨hoff,hexp⟩ := logProxy_exponent_bounds fuel prec c a mag hm hform hcut
  have hoB : offset.natAbs ≤ 4*B^2 := by
    apply natAbs_le_of_abs_bound
    push_cast
    exact hoff.trans (mul_le_mul_of_nonneg_left hT₂ (by norm_num))
  have heB (i : ι) : ((D : ℤ)*a i).natAbs ≤ 4*B := by
    apply natAbs_le_of_abs_bound
    dsimp [D]
    exact (hexp i).trans (mul_le_mul_of_nonneg_left hT (by norm_num))
  obtain ⟨hoT,heT⟩ := logProxy_exponent_natAbs_le fuel prec c a mag hm hform hcut
  have hosize : offset.natAbs.size ≤ 2*fuel+3 := by
    simpa only [Nat.size_pow] using Nat.size_le_size hoT
  have hesize (i : ι) : ((D : ℤ)*a i).natAbs.size ≤ fuel+3 := by
    simpa only [Nat.size_pow] using Nat.size_le_size (heT i)
  have htime : (ps.map fun p => 2*p.2.natAbs.size+3).sum ≤
      2*(2*fuel+3)+3+Fintype.card ι*(2*(fuel+3)+3) := by
    have h := proxyPowerOperands_time large large.toList (.refl _) offset D a mag hosize (fun i _ => hesize i)
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Finset.card_le_univ large)) _)
  exact ⟨hoB,heB,htime⟩

end Compression
end LinearProgramming
end Optimization
end OAI
