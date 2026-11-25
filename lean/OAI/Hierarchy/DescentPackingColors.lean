import OAI.Hierarchy.DescentWalshCorrelation
import Mathlib.Analysis.Real.Sqrt

namespace OAI
/-! # A single affine Walsh coloring for the older traffic in every colony -/

namespace Hierarchy.DescentPackingColors

open DescentWalshTables Finset
open scoped BigOperators

/-- The unnormalized Walsh spectrum satisfies Parseval with the actual binary address count. -/
theorem parseval {k : ℕ} (A : Bits k → ℝ) :
    ∑ a : Bits k, coefficient A a ^ 2 = (2:ℝ)^k * ∑ i, (A i)^2 := by
  have h := coefficient_twice (DescentRowScore.autocorrelation A) 0
  rw [coefficient] at h
  simp only [coefficient_correlation,character_row,binaryRow_apply,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,sign,ite_true,one_mul,DescentRowScore.autocorrelation,
    add_zero,pow_two] at h ⊢
  exact h

/-- Choose the same coloring functional for every colony. Rows with zero traffic and the
zero-dimensional binary address space are included. -/
theorem exists_coloring {k : ℕ} {C : Type*} [Fintype C] (A : C → Bits k → ℝ)
    (B : ℝ) (nonneg : ∀ c i, 0 ≤ A c i) (cap : ∀ c i, A c i ≤ B) :
    ∃ (a : Bits k) (b : ZMod 2),
      ∑ c, |∑ i : Bits k, sign (binaryRow a i+b) * A c i| ≤
        Real.sqrt (B * Fintype.card C * ∑ c, ∑ i, A c i) := by
  classical
  let X := ∑ c, ∑ i, A c i
  let E := fun (a : Bits k) => ∑ c, (coefficient (A c) a)^2
  have norm : ∑ a : Bits k, E a ≤ (2:ℝ)^k*(B*X) := by
    unfold E X
    rw [sum_comm]
    simp only [parseval,← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [Finset.mul_sum]
    apply sum_le_sum
    intro c _
    apply sum_le_sum
    intro i _
    simpa only [pow_two] using (mul_le_mul_of_nonneg_right (cap c i) (nonneg c i))
  have cardBits : (Fintype.card (Bits k) : ℝ) = 2^k := by simp [Bits,ZMod.card]
  have small : ∃ a : Bits k, E a ≤ B*X := by
    by_contra! h
    have hh : (∑ _a : Bits k, B*X) < ∑ a : Bits k, E a :=
      sum_lt_sum (fun a _ => (h a).le) ⟨0,mem_univ _,h 0⟩
    simp only [sum_const,card_univ,nsmul_eq_mul,cardBits] at hh
    linarith only [norm,hh]
  obtain ⟨a,ha⟩ := small
  refine ⟨a,0,?_⟩
  simp only [add_zero,← character_row]
  change ∑ c, |coefficient (A c) a| ≤ _
  apply Real.le_sqrt_of_sq_le
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ : C => (1:ℝ)) (fun c => |coefficient (A c) a|)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,sq_abs] at hcs
  exact hcs.trans ((mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)).trans_eq (by dsimp [X];ring))

end Hierarchy.DescentPackingColors

end OAI
