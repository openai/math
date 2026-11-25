import OAI.Computability.NearSquareRoot.KernelComputableAddress
import OAI.Computability.NearSquareRoot.PrecisionRecursiveWalsh

/-! # A computable working-range threshold for a recursive Walsh template

The input is a natural upper bound on the template's one-level growth factor.
Above the threshold every level reached at address width `k` has enough
rounding precision and the fanout padding exponent fits in half of `k`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

/-- A width threshold obtained directly from a template's one-level bound. -/
def precisionCutoff (M : ℕ) : ℕ := 2^(4*(M+1))

theorem precisionCutoff_primrec : Primrec precisionCutoff :=
  KernelComputableAddress.primrec_pow (.const 2)
    (Primrec.nat_mul.comp (.const 4) (Primrec.nat_add.comp .id (.const 1)))

private theorem square_le_pow {q : ℕ} (hq : 4 ≤ q) : q*q ≤ 2^q := by
  induction q, hq using Nat.le_induction with
  | base => decide
  | succ q hq ih =>
    rw [pow_succ]
    calc
      (q+1)*(q+1) ≤ 2*(q*q) := by nlinarith
      _ ≤ 2^q*2 := by omega

theorem precisionCutoff_pos (M : ℕ) : 0 < precisionCutoff M := Nat.pow_pos (by decide)

theorem half_budget_of_cutoff {M k : ℕ} (h : precisionCutoff M ≤ k) :
    (Nat.log 2 k+1)*M ≤ k/2 := by
  let q := Nat.log 2 k
  have hq : 4*(M+1) ≤ q := Nat.le_log_of_pow_le (by decide : 1<2) h
  have h4 : 4 ≤ q := by omega
  have hb : 2*((q+1)*M) ≤ q*q := by nlinarith [Nat.mul_le_mul_left q hq]
  have hk := (square_le_pow h4).trans (Nat.pow_log_le_self 2 (ne_of_gt ((precisionCutoff_pos M).trans_le h)))
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by dsimp only [q] at *; omega)

theorem depth_allowance_of_cutoff {C M k : ℕ} (hC : C ≤ M) (hk : precisionCutoff M ≤ k)
    (j : ℕ) (hj : 2^j ≤ k) : (C:ℝ)^(j+1) ≤ (2:ℝ)^k := by
  have hl := Nat.le_log_of_pow_le (by decide : 1<2) hj
  have hc : C ≤ 2^M := hC.trans (Nat.lt_two_pow_self (n:=M)).le
  have hExp : M*(j+1) ≤ k := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_right M (Nat.succ_le_succ hl)).trans
      ((half_budget_of_cutoff hk).trans (Nat.div_le_self k 2))
  exact_mod_cast (calc
    C^(j+1) ≤ (2^M)^(j+1) := Nat.pow_le_pow_left hc _
    _ ≤ 2^k := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) hExp)

theorem width_le_recursionFactor {a W : ℕ} (p : KernelPass.Plan (a+1) W W) :
    W ≤ recursionFactor p :=
  (Nat.le_add_right W 2).trans
    (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ (templateFactor p+1)))

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
