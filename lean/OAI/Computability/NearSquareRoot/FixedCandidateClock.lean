import OAI.Computability.NearSquareRoot.FixedCandidateInterface
import OAI.Computability.NearSquareRoot.PrecisionSqrtRescale
import OAI.Computability.NearSquareRoot.IntegerBudget

/-! # Conversion of the separated physical clocks to an input-length bound -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open Filter DigitPacking

/-- The pointwise/sqrt command has only logarithmic overhead in address width. -/
theorem productClock_asymptotic {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, (productClock n : ℝ) ≤ K*n*logScale n^γ := by
  let d := 1 + (Real.log 2)⁻¹
  have hd : 0 < d := by unfold d; positivity
  obtain ⟨K,hK,hB⟩ := eventually_integerBudget_le (C := 193*(d+1)) (P := 0)
    (by positivity) (by positivity) (ρ := 0) (by positivity) hγ 1 0
  refine ⟨K,hK,?_⟩
  filter_upwards [hB, eventually_ge_atTop (2:ℕ)] with n he hn
  apply le_trans _ he
  let k := addressBits n
  have hlog := clog_le_logScale (n := k+1) (by omega)
  have hcl : (Nat.clog 2 (k+1) : ℝ) ≤ d * logScale (k+1) := by
    exact (show ((Nat.clog 2 (k+1):ℕ):ℝ) ≤ (max 1 (Nat.clog 2 (k+1)) : ℕ) by exact_mod_cast le_max_right ..).trans hlog
  have hs : logScale (k+1) ≤ 1 + Real.log (2+(k:ℝ)) := by
    unfold logScale
    apply add_le_add_right
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have one : 1 ≤ 1 + Real.log (2+(k:ℝ)) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2+(k:ℝ) by exact_mod_cast (show 1 ≤ 2+k by omega))
    linarith
  have logBound : (Nat.clog 2 (k+1):ℝ)+1 ≤ (d+1)*(1+Real.log (2+(k:ℝ))) := by
    linarith [mul_le_mul_of_nonneg_left hs hd.le]
  have budget : (productClock n : ℝ) ≤ 193*(n:ℝ)*((Nat.clog 2 (k+1):ℝ)+1) := by
    exact_mod_cast FixedPoint.squareRootPass_clock hn
  have vol : (n:ℝ) ≤ (capacity n:ℝ)*k := by exact_mod_cast (packed_volume hn).1
  calc
    _ ≤ 193*((capacity n : ℝ)*k)*((d+1)*(1+Real.log (2+k))) := budget.trans (by gcongr)
    _ = _ := by simp [integerBudget,k]; ring

/-- Once the routing and transform clocks have the requested exponent, the
remaining multiplication commands preserve it. -/
theorem Clocks.eventually_total (c : Clocks) {γ : ℝ} (hγ : 0 < γ)
    (h : ∀ clock ∈ [c.route,c.forward,c.inverse], ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n in atTop, (clock n : ℝ) ≤ C*n*logScale n^γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (c.total n : ℝ) ≤ C*n*logScale n^γ := by
  obtain ⟨R,hR,hr⟩ := h c.route (by simp)
  obtain ⟨F,hF,hf⟩ := h c.forward (by simp)
  obtain ⟨J,hJ,hj⟩ := h c.inverse (by simp)
  obtain ⟨P,hP,hp⟩ := productClock_asymptotic hγ
  refine ⟨1+P+R+F+J,by positivity,?_⟩
  filter_upwards [hr,hf,hj,hp,eventually_ge_atTop (1:ℕ)] with n hr hf hj hp hn
  have hs : 1 ≤ logScale n := by
    unfold logScale
    linarith [Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)]
  have hh : (n:ℝ) ≤ (n:ℝ)*logScale n^γ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hs hγ.le)
  unfold total
  push_cast
  linarith

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
