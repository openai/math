import OAI.Computability.BorderVNP.DiagonalCommonAdvice
import OAI.Computability.BorderVNP.DiagonalAdvice
import OAI.Computability.BorderVNP.DiagonalSubstitution
import OAI.Computability.BorderVNP.ResidueAdviceBudget

/-! # The selected arithmetic data fit the signed diagonal at the paper's scales -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Branch MvPolynomial
open scoped Classical

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]

/-- At every sufficiently large length a small circuit yields an advised branch
whose entire chart and fixed scalar data fit in an arbitrarily small fixed
fraction of one batch. This choice precedes all pin and routing choices. -/
theorem eventually_advised_branches (q : ℕ) [CharP K q] (G : PaidIdentity K D m) (aux : ι → K)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) (factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k, k+1 = n → ∀ s ≤ stretch σ n,
      ∀ (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (F : Type u) [Field F] [CharP F q],
        BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
          ∃ (R : CommonField G aux q k s ord) (chart : AdvisedBranch R),
            factor * chartBitBudget (Fintype.card (G.Entry ⊕ ι)) (pairedTableParameters (k+1) s)
              (Nat.clog 2 (Nat.card chart.E)) (Nat.clog 2 R.p) < stretch ρ n := by
  obtain ⟨A,C,select⟩ := joint_advice_of_borderApprox.{u,v} q G aux
  filter_upwards [advice_polynomial_lt_batch hσ hσρ (factor*A*5^C) C] with n hbudget
  intro k hk s hs ord F _ _ hp
  obtain ⟨R,chart,hc⟩ := select k s ord F hp
  refine ⟨R,chart,?_⟩
  have hm : 2*(k+1)+s+2 ≤ 5*adviceScale σ ρ n := by
    unfold adviceScale
    omega
  calc
    _ ≤ factor*(A*(2*(k+1)+s+2)^C) := Nat.mul_le_mul_left factor hc
    _ ≤ factor*(A*(5*adviceScale σ ρ n)^C) := by gcongr
    _ = factor*A*5^C*adviceScale σ ρ n^C := by rw [mul_pow]; ring
    _ < _ := hbudget

/-- Every monomial from the chosen unary powers, including unrestricted choices,
fits this Section 11 degree bound. -/
def batchDegree (teams h r k : ℕ) : ℕ :=
  teams * h * (2 ^ Nat.clog 2 (r*(2*k+1)+1) - 1)

/-- This covers the full substituted row at every choice of external pins. -/
theorem processors_fit_degree (teams h r k : ℕ) (hh : 1 ≤ h) :
    Fintype.card (Fin teams × Fin r) * (2*k+1) ≤ batchDegree teams h r k := by
  have cap := Nat.le_pow_clog (by decide : 1 < 2) (r*(2*k+1)+1)
  have hbits : r*(2*k+1) ≤ 2^Nat.clog 2 (r*(2*k+1)+1)-1 := by omega
  simp only [Fintype.card_prod, Fintype.card_fin, batchDegree]
  rw [Nat.mul_assoc teams r]
  exact (Nat.mul_le_mul_left teams hbits).trans
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hh))

/-- Binary length of the full degree bound depends logarithmically on both
replication counts, the number of parameters, and the parse degree. -/
theorem batchDegree_bits (teams h r k : ℕ) :
    Nat.clog 2 (batchDegree teams h r k + 1) ≤
      Nat.clog 2 (teams+1) + Nat.clog 2 (h+1) + Nat.clog 2 (r+1) + Nat.clog 2 (2*k+2) := by
  let b := Nat.clog 2 (r*(2*k+1)+1)
  have z : r*(2*k+1)+1 ≤ (r+1)*(2*k+2) := by nlinarith
  have w : b ≤ Nat.clog 2 (r+1) + Nat.clog 2 (2*k+2) := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    exact z.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
  apply Nat.clog_le_of_le_pow
  rw [Nat.add_assoc (Nat.clog 2 (teams+1) + _) _ _, pow_add, pow_add]
  have hb : 1 ≤ 2^b := Nat.one_le_two_pow
  calc
    batchDegree teams h r k + 1 ≤ (teams+1)*(h+1)*2^b := by
      change teams*h*(2^b-1)+1 ≤ _
      have hl := Nat.sub_le (2^b) 1
      nlinarith only [Nat.mul_le_mul_left (teams*h) hl, hb, Nat.zero_le (teams*2^b), Nat.zero_le (h*2^b)]
    _ ≤ _ := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
      (Nat.pow_le_pow_right (by decide) w)

end Diagonal

end BorderVNP
end Computability
end OAI
