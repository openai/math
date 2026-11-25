import OAI.Optimization.LinearProgramming.Compression.ProxyFuel
import OAI.Optimization.LinearProgramming.Compression.CommitQueryCost
import OAI.Optimization.LinearProgramming.Compression.RequestQueries
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests

/-! The manuscript cutoff dominates every adaptive sign query in both homogeneous rounding
calls and every bisection comparison. The estimates cover all generator lists at once. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators
open OAI.Optimization.LinearProgramming.Lattice

/-- The attainable query width in the commitment to the generator coordinates. -/
theorem manuscript_commit_fuel (N j : ℕ) (hj : j ≤ paperWidth N) :
    let M := (j+1)*fiberProjectionBudget j (paperWidth N) (epochHeightFor N j)+1
    paperRadius N+7+(j+1)+queryCoefficientWidth (j+1) M ≤ manuscriptProxyFuel N := by
  dsimp only
  apply manuscript_rounding_fuel
  · unfold paperWidth at hj; omega
  · exact manuscript_commit_inputWidth N j hj

/-- The attainable width when sign rounding is used on the generator list plus the request. -/
theorem manuscript_request_fuel (N j : ℕ) (hj : j ≤ paperWidth N) :
    let d := j+1
    let M := (d+2)*(requestCutoff d+3)
    paperRadius N+7+(d+1)+queryCoefficientWidth (d+1) M ≤ manuscriptProxyFuel N := by
  dsimp only
  apply manuscript_rounding_fuel
  · unfold paperWidth at hj; omega
  · exact manuscript_request_inputWidth N j hj

/-- For either rounding call, the global cutoff controls the full affine L1 norm,
including the separate constant term, on the actual history of the supplied selector. -/
theorem manuscript_rounding_query_l1 {N d M : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator (d+1) M ^ ((d+1)+1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * ((d+1 : ℕ) : ℚ) * M))
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm x a + c < 0)
    (row : Fin (d+1) → ℤ) (hr : row ∈
      SignQueries.history (affineCommitReply negative) (roundingProgramWith M select))
    (hfill : paperRadius N+7+(d+1)+queryCoefficientWidth (d+1) M ≤ manuscriptProxyFuel N) :
    (2 : ℤ)^(paperRadius N+7) * (|row (Fin.last d)| + ∑ i : Fin d, |row i.castSucc|) ≤
      2^manuscriptProxyFuel N := by
  obtain ⟨ha, hcap⟩ := computeCommitWith_query_l1 x hM select hsel negative ho row hr hfill
  exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans hcap

private theorem gridArgs_scaled_le_pow {d k fuel : ℕ} (w : Fin d → ℚ)
    (oracle : (Fin d → ℤ) → ℤ → Bool) (z : Fin d → ℤ) (last : Fin d)
    (hshort : ‖requestGraph w z‖ ≤ requestCutoff d) (mid : ℤ)
    (hmid : mid ∈ (requestGridRun oracle z last (2^k) (requestCutoff d)).2)
    (hfe : k+(k+4*d+12) ≤ fuel) :
    let args := requestGridArgs z last (2^k) mid
    (2 : ℤ)^k * (|args.2| + ∑ i, |args.1 i|) ≤ 2^fuel := by
  let args := requestGridArgs z last (2^k) mid
  have hnorm : (∑ i, |args.1 i|) + |args.2| ≤ 4 * ((2^k : ℕ) : ℤ) * (requestCutoff d : ℤ)^2 :=
    requestGridArgs_norm_le w oracle z last (2^k) (Nat.two_pow_pos _) hshort mid hmid
  have hheight : (4:ℤ) * ((2^k : ℕ) : ℤ) * (requestCutoff d : ℤ)^2 ≤ 2^(k+4*d+12) := by
    exact_mod_cast requestGridArgs_bit_cap d k
  have h := (mul_le_mul_of_nonneg_left (hnorm.trans hheight) (pow_nonneg (by norm_num : (0:ℤ) ≤ 2) k))
  change (2:ℤ)^k * (|args.2| + ∑ i, |args.1 i|) ≤ _
  rw [add_comm |args.2| (∑ i, |args.1 i|)]
  rw [← pow_add] at h
  exact h.trans (pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hfe)

/-- The same choice of fuel bounds every midpoint term actually used on a successful request,
including both signs of the selected relation's last coefficient. -/
theorem manuscript_grid_query_l1 (N j : ℕ) (hj : j ≤ paperWidth N) (w : Fin (j+1) → ℚ)
    (oracle : (Fin (j+1) → ℤ) → ℤ → Bool) (z : Fin (j+1) → ℤ) (last : Fin (j+1))
    (hshort : ‖requestGraph w z‖ ≤ requestCutoff (j+1)) (mid : ℤ)
    (hmid : mid ∈ (requestGridRun oracle z last (paperGrid N) (requestCutoff (j+1))).2) :
    let args := requestGridArgs z last (paperGrid N) mid
    (2 : ℤ)^(paperRadius N+7) * (|args.2| + ∑ i, |args.1 i|) ≤ 2^manuscriptProxyFuel N := by
  apply gridArgs_scaled_le_pow w oracle z last hshort mid hmid
  unfold manuscriptProxyFuel manuscriptProxyFuelFormula paperRadius
  dsimp only
  unfold paperWidth at hj
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
