import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI
/-! # Converting the counted colony and indivisibility losses into a quarter of the wire mass -/

namespace Hierarchy.DescentCompiler

/-- The cardinality bound for the minimizing multiplier, together with the
group-root slack, pays the product of the occurrence cap and the actual
number of colonies. All amounts use the same bundle unit. -/
theorem colony_invoice {A B Q roots mass ε : ℝ} (hA : 0 < A) (hB : 0 < B)
    (count : Q ≤ roots + 240 * mass / (A * B))
    (slack : roots * (A * B) ≤ ε) :
    A * (B * Q) ≤ ε + 240 * mass := by
  have bound := mul_le_mul_of_nonneg_right count (mul_nonneg hA.le hB.le)
  rw [add_mul,div_mul_cancel₀ _ (mul_ne_zero hA.ne' hB.ne')] at bound
  linarith only [bound,slack]

/-- The actual matching estimate counts a pair on one side only. The rounded
dyadic packing cutoff can be chosen linearly in the number of permitted
destinations at one source. The core-independent loss is displayed explicitly. -/
theorem paid_quarter {A B Q X E ε β K mass I : ℝ}
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hX : 0 ≤ X) (hE : 0 ≤ E) (he : 0 ≤ ε)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (cutoff : 481*128*(K+1) ≤ A)
    (count : A*(B*Q) ≤ ε+240*mass) (full : mass ≤ 2*X+(β+1)*E+ε)
    (paired : X/2-Real.sqrt (B*Q*X)/2-2*B*K*Q ≤ I) :
    X/4-((β+1)*E+ε)/4 ≤ I := by
  let U := X+(β+1)*E+ε
  have cost : 0 ≤ (β+1)*E := mul_nonneg (by linarith) hE
  have total : 0 ≤ U := by dsimp [U]; linarith
  have larger : X ≤ U := by dsimp [U]; linarith
  have invoice : 128*(K+1)*(B*Q) ≤ U := by
    have small := mul_le_mul_of_nonneg_right cutoff (mul_nonneg hB hQ)
    dsimp [U]
    nlinarith only [small,count,full,cost,he,hX]
  have qnon := mul_nonneg hB hQ
  have kq := mul_nonneg hK qnon
  have qsmall : B*Q ≤ U/128 := by nlinarith only [invoice,kq]
  have waste : 2*B*K*Q ≤ U/64 := by nlinarith only [invoice,qnon]
  have radicand : B*Q*X ≤ (U/8)^2 := calc
    _ ≤ (U/128)*U := mul_le_mul qsmall larger hX (by positivity)
    _ ≤ _ := by nlinarith only [sq_nonneg U]
  have radical : Real.sqrt (B*Q*X) ≤ U/8 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,radicand⟩
  dsimp [U] at radical waste total
  linarith only [paired,radical,waste,total]

/-- A fixed degree determines a polynomial dyadic cap as soon as K ≤ 2^k.
The constant is independent of the network and its field. -/
theorem dyadic_cutoff {K k : ℕ} (hk : K ≤ 2^k) :
    (481*128*(K+1) : ℕ) ≤ 2^(17+k) := by
  rw [pow_add]
  have positive : 0 < 2^k := Nat.two_pow_pos _
  norm_num
  omega

end Hierarchy.DescentCompiler

end OAI
