import OAI.Optimization.LinearProgramming.Compression.Request

/-! Binary search for the residual on an explicit rational grid, using one
integer affine sign query for each tested grid point (Section 3.2). -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Integer returned by a binary threshold search, together with the thresholds queried.
The lower bound is inclusive, and the upper bound is exclusive. -/
def requestGridSearch (below : ℤ → Bool) : ℕ → ℤ → ℤ × List ℤ
  | 0, lo => (lo, [])
  | k+1, lo =>
    let mid := lo + 2 ^ k
    let next := requestGridSearch below k (if below mid then lo else mid)
    (next.1, mid :: next.2)

theorem requestGridSearch_queries (below : ℤ → Bool) (depth : ℕ) (lo : ℤ) :
    (requestGridSearch below depth lo).2.length = depth := by
  induction depth generalizing lo with
  | zero => rfl
  | succ k ih => simp [requestGridSearch, ih]

theorem requestGridSearch_correct (below : ℤ → Bool) (t : ℝ)
    (ht : ∀ k : ℤ, below k = true ↔ t < k) (depth : ℕ) (lo : ℤ)
    (hlo : (lo : ℝ) ≤ t) (hhi : t < lo + (2 : ℝ)^depth) :
    ((requestGridSearch below depth lo).1 : ℝ) ≤ t ∧
      t < (requestGridSearch below depth lo).1 + 1 := by
  induction depth generalizing lo with
  | zero => simpa [requestGridSearch] using And.intro hlo hhi
  | succ k ih =>
    let mid := lo + (2 : ℤ) ^ k
    have hm : (mid : ℝ) = lo + (2 : ℝ)^k := by simp [mid]
    rw [pow_succ] at hhi
    by_cases ht' : below mid = true
    · have hm' := (ht mid).mp ht'
      rw [hm] at hm'
      dsimp [mid] at ht'
      simpa [requestGridSearch, ht'] using ih lo hlo hm'
    · have hm' := le_of_not_gt (fun h => ht' ((ht mid).mpr h))
      have hb : below mid = false := Bool.eq_false_iff.mpr ht'
      dsimp [mid] at hb
      simpa [requestGridSearch, hb, mid] using ih mid hm' (by rw [hm]; linarith)

theorem requestForm_int_mul {d : ℕ} (v : Fin d → ℝ) (z : Fin d → ℤ) (q : ℤ) :
    requestForm v (fun i => q * z i) = (q : ℝ) * requestForm v z := by
  simp only [requestForm, Int.cast_mul, Finset.mul_sum, mul_assoc]

/-- The oracle returns `true` for a strictly negative integer affine form. Clearing
the denominator, with its actual sign, gives a query for a scaled residual. -/
def requestGridBelow {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool) (z : Fin d → ℤ)
    (last : Fin d) (q : ℕ) (k : ℤ) : Bool :=
  if 0 < z last then oracle (fun i => (q : ℤ) * z i) (-k * z last)
  else oracle (fun i => -(q : ℤ) * z i) (k * z last)

theorem requestGridBelow_correct {d : ℕ} (v : Fin d → ℝ)
    (oracle : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0)
    (z : Fin d → ℤ) (last : Fin d) (hne : z last ≠ 0) (q : ℕ) (k : ℤ) :
    requestGridBelow oracle z last q k = true ↔
      (q : ℝ) * requestForm v z / (z last : ℝ) < k := by
  by_cases hz : 0 < z last
  · have hp : 0 < (z last : ℝ) := by exact_mod_cast hz
    simp only [requestGridBelow, hz, ↓reduceIte, ho, requestForm_int_mul, div_lt_iff₀ hp]
    push_cast
    constructor <;> intro h <;> linarith only [h]
  · have hn : (z last : ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hz) hne
    simp only [requestGridBelow, hz, ↓reduceIte, ho, requestForm_int_mul, div_lt_iff_of_neg hn]
    push_cast
    constructor <;> intro h <;> linarith only [h]

/-- Search data for the interval `[-K, K]` on a grid of spacing `1/q`. -/
def requestGridRun {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool) (z : Fin d → ℤ)
    (last : Fin d) (q K : ℕ) : ℤ × List ℤ :=
  requestGridSearch (requestGridBelow oracle z last q) ((2*K*q).log2 + 1) (-(K*q : ℕ))

theorem requestGridRun_queries {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool) (z : Fin d → ℤ)
    (last : Fin d) (q K : ℕ) : (requestGridRun oracle z last q K).2.length =
      (2*K*q).log2 + 1 := requestGridSearch_queries _ _ _

/-- The returned integer is the floor of the scaled residual. The endpoint cases
`e = ±K` are covered by the strict choice of the binary search width. -/
theorem requestGridRun_correct {d : ℕ} (v : Fin d → ℝ)
    (oracle : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0)
    (z : Fin d → ℤ) (last : Fin d) (hne : z last ≠ 0) (q K : ℕ)
    (hres : |requestForm v z / (z last : ℝ)| ≤ K) :
    (requestGridRun oracle z last q K).1 = ⌊(q : ℝ) * (requestForm v z / (z last : ℝ))⌋ := by
  let e := requestForm v z / (z last : ℝ)
  obtain ⟨hl, hu⟩ := abs_le.mp hres
  have hl' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) q)
  have hu' := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) q)
  have hpow : (2 : ℝ)*K*q < 2^((2*K*q).log2+1) := by
    exact_mod_cast (Nat.lt_log2_self (n := 2*K*q))
  have h := requestGridSearch_correct (requestGridBelow oracle z last q) ((q : ℝ)*e)
    (fun k => by simpa [e, mul_div_assoc] using requestGridBelow_correct v oracle ho z last hne q k)
    ((2*K*q).log2+1) (-(K*q : ℕ))
    (by dsimp [e]; push_cast; linarith only [hl'])
    (by dsimp [e]; push_cast; linarith only [hu', hpow])
  exact (Int.floor_eq_iff.mpr h).symm

/-- The accepted request obtains a rational affine approximation with error below
the grid spacing, without inspecting bits of the real proxies. -/
theorem request_grid_affine_approx {n : ℕ} (v : Fin (n+1) → ℝ)
    (oracle : (Fin (n+1) → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0)
    (z : Fin (n+1) → ℤ) (hne : z (Fin.last n) ≠ 0) (q K : ℕ) (hq : 0 < q)
    (hr : |requestForm v z / (z (Fin.last n) : ℝ)| ≤ K) :
    let e' : ℚ := ((requestGridRun oracle z (Fin.last n) q K).1 : ℚ) / q
    |v (Fin.last n) - (∑ i : Fin n, (requestSlope z i : ℝ) * v i.castSucc + e')| < (1 : ℝ) / q := by
  dsimp only
  rw [requestGridRun_correct v oracle ho z (Fin.last n) hne q K hr]
  let e := requestForm v z / (z (Fin.last n) : ℝ)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have heq := request_affine_identity v z hne
  change v (Fin.last n) = _ + e at heq
  rw [heq, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  change |(_ + e) - (_ + (⌊(q : ℝ)*e⌋ : ℝ) / q)| < (1 : ℝ) / q
  have hlo := Int.floor_le ((q : ℝ)*e)
  have hhi := Int.lt_floor_add_one ((q : ℝ)*e)
  rw [add_sub_add_left_eq_sub, abs_lt]
  constructor
  · rw [← neg_div, div_lt_iff₀ hq', sub_mul, div_mul_cancel₀ _ hq'.ne']
    nlinarith only [hlo]
  · rw [lt_div_iff₀ hq', sub_mul, div_mul_cancel₀ _ hq'.ne']
    nlinarith only [hhi]

/-- Numerator bound for the returned unreduced rational on the residual grid. -/
theorem requestGridRun_num_bound {d : ℕ} (v : Fin d → ℝ)
    (oracle : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0)
    (z : Fin d → ℤ) (last : Fin d) (hne : z last ≠ 0) (q K : ℕ)
    (hres : |requestForm v z / (z last : ℝ)| ≤ K) :
    |(requestGridRun oracle z last q K).1| ≤ (K*q : ℕ) := by
  rw [requestGridRun_correct v oracle ho z last hne q K hres, abs_le]
  obtain ⟨hl, hu⟩ := abs_le.mp hres
  have hlo := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) q)
  have hhi := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) q)
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith only [hlo]
  · have hf := Int.floor_le_floor hhi
    simpa only [← Nat.cast_mul, Int.floor_natCast, Nat.mul_comm q K] using hf

end Compression
end LinearProgramming
end Optimization
end OAI
