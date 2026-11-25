import OAI.Optimization.LinearProgramming.Compression.RequestAlgorithm
import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer

/-! Encoding bounds and the dimension-dependent oracle query count for Section 3.2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- The exact number of bisection calls only grows linearly in the dimension and the
logarithm of the grid denominator. -/
theorem requestGridRun_dyadic_count {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool)
    (z : Fin d → ℤ) (last : Fin d) (p : ℕ) :
    (requestGridRun oracle z last (2^p) (requestCutoff d)).2.length ≤ 2*d + p + 7 := by
  have hlog (a k : ℕ) (ha : a ≠ 0) : (a * 2^k).log2 = a.log2 + k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Nat.mul_assoc, Nat.mul_comm (a * 2^k), Nat.log2_two_mul (by positivity), ih]
      omega
  have he : 2 * requestCutoff d * 2 ^ p = (d+3) * 2^(d+3+p) := by
    simp only [requestCutoff, pow_add, pow_succ]; ring
  rw [requestGridRun_queries, he, hlog _ _ (by omega)]
  have := Nat.log2_le_self (d+3)
  omega

/-- Reduced numerators and denominators of all returned slopes are bounded by the
basis cutoff itself. This is a bound on the delivered rationals as encoded. -/
theorem requestSlope_height {n : ℕ} {w : Fin (n+1) → ℚ} {z : Fin (n+1) → ℤ}
    (hn : z (Fin.last n) ≠ 0) (hs : ‖requestGraph w z‖ ≤ requestCutoff (n+1)) (i : Fin n) :
    (requestSlope z i).num.natAbs ≤ requestCutoff (n+1) ∧
      (requestSlope z i).den ≤ requestCutoff (n+1) := by
  have hc := (requestGraph_coords_le hs).1
  have hnat (j : Fin (n+1)) : (z j).natAbs ≤ requestCutoff (n+1) := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    exact_mod_cast hc j
  obtain ⟨hnum, hden⟩ := reduced_fraction_height (-z i.castSucc) (z (Fin.last n)) hn
  constructor
  · simpa [requestSlope] using hnum.trans (by simpa using hnat i.castSucc)
  · simpa [requestSlope] using hden.trans (hnat (Fin.last n))

/-- Reduced offset numerator and denominator lengths follow from the searched integer
and the explicit grid denominator. -/
theorem requestOffset_height {d : ℕ} (v : Fin d → ℝ)
    (oracle : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0)
    (z : Fin d → ℤ) (last : Fin d) (hn : z last ≠ 0) (q K : ℕ) (hq : 0 < q)
    (hr : |requestForm v z / (z last : ℝ)| ≤ K) :
    let e' : ℚ := ((requestGridRun oracle z last q K).1 : ℚ) / q
    e'.num.natAbs ≤ K*q ∧ e'.den ≤ q := by
  have hn' := requestGridRun_num_bound v oracle ho z last hn q K hr
  have hn'' : (requestGridRun oracle z last q K).1.natAbs ≤ K*q := by
    apply Int.ofNat_le.mp
    simpa only [Int.natCast_natAbs] using hn'
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨hc, hd⟩ := reduced_fraction_height (requestGridRun oracle z last q K).1 (q : ℤ) hq'
  constructor
  · simpa using hc.trans hn''
  · simpa using hd

/-- Coefficient height of the actual selected affine representation, independent of the
values of the unknown proxies. -/
theorem runMinorRequest_height {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (g : Fin (n+1) → Fin (n+1) → ℤ) (oracle : (Fin (n+1) → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0) (q : ℕ) (hq : 0 < q)
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    {f : (Fin n → ℚ) × ℚ} (h : runMinorRequest w g oracle q = some f) :
    (∀ i, (f.1 i).num.natAbs ≤ requestCutoff (n+1) ∧ (f.1 i).den ≤ requestCutoff (n+1)) ∧
      f.2.num.natAbs ≤ requestCutoff (n+1)*q ∧ f.2.den ≤ q := by
  unfold runMinorRequest at h
  cases hc : requestCandidate w g (Fin.last n) with
  | none => simp [hc] at h
  | some i =>
    obtain ⟨hn, hs⟩ := requestCandidate_some hc
    simp only [hc, Option.map_some, Option.some.injEq] at h
    subst f
    refine ⟨requestSlope_height hn hs, ?_⟩
    exact requestOffset_height v oracle ho _ _ hn q _ hq
      (request_residual_le v _ _ hn (abs_requestForm_le_of_basis v w _ hsign hs))

end Compression
end LinearProgramming
end Optimization
end OAI
