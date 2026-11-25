import OAI.Optimization.LinearProgramming.Compression.RequestSize

/-! Coefficient sizes of every affine sign oracle call of an accepted request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- All queried midpoints are inside the initial search interval. This is independent
of whether the oracle consistently answers a particular threshold. -/
theorem requestGridSearch_mem_bounds (below : ℤ → Bool) (depth : ℕ) (lo k : ℤ)
    (hk : k ∈ (requestGridSearch below depth lo).2) : lo ≤ k ∧ k ≤ lo + 2^depth := by
  induction depth generalizing lo with
  | zero => simp [requestGridSearch] at hk
  | succ p ih =>
    let mid := lo + 2^p
    change k ∈ mid :: (requestGridSearch below p (if below mid then lo else mid)).2 at hk
    rw [pow_succ]
    have hp : (0 : ℤ) ≤ 2^p := by positivity
    rcases List.mem_cons.mp hk with h | h
    · dsimp [mid] at h
      constructor <;> omega
    · by_cases hb : below mid = true
      · rw [ite_eq_left hb] at h
        obtain ⟨hl, hu⟩ := ih lo h
        constructor <;> omega
      · rw [ite_eq_right hb] at h
        obtain ⟨hl, hu⟩ := ih mid h
        dsimp [mid] at hl hu
        constructor <;> omega

theorem requestGridRun_threshold {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool)
    (z : Fin d → ℤ) (last : Fin d) (q K : ℕ) (hq : 0 < q) (hK : 0 < K)
    (k : ℤ) (hk : k ∈ (requestGridRun oracle z last q K).2) :
    |k| ≤ 3*(K : ℤ)*q := by
  have hp := Nat.log2_self_le (by positivity : 2*K*q ≠ 0)
  obtain ⟨hl, hu⟩ := requestGridSearch_mem_bounds (requestGridBelow oracle z last q)
    ((2*K*q).log2+1) (-(K*q : ℕ)) k hk
  push_cast at hl hu
  rw [pow_succ] at hu
  have hp' : (2 : ℤ) ^ (2*K*q).log2 ≤ 2*(K : ℤ)*q := by exact_mod_cast hp
  have hkq : (0 : ℤ) ≤ K*q := by positivity
  rw [abs_le]
  constructor <;> nlinarith only [hl, hu, hp', hkq]

/-- The signed integer vector and constant sent for a midpoint comparison. -/
def requestGridArgs {d : ℕ} (z : Fin d → ℤ) (last : Fin d) (q : ℕ) (k : ℤ) :
    (Fin d → ℤ) × ℤ :=
  if 0 < z last then (fun i => (q : ℤ) * z i, -k * z last)
  else (fun i => -(q : ℤ) * z i, k * z last)

theorem requestGridBelow_eq_args {d : ℕ} (oracle : (Fin d → ℤ) → ℤ → Bool)
    (z : Fin d → ℤ) (last : Fin d) (q : ℕ) (k : ℤ) :
    requestGridBelow oracle z last q k =
      oracle (requestGridArgs z last q k).1 (requestGridArgs z last q k).2 := by
  by_cases h : 0 < z last <;> simp [requestGridBelow, requestGridArgs, h]

/-- Complete coefficient one-norm, including the constant term, of each query in a
search trace generated from a short vector in the graph basis. -/
theorem requestGridArgs_norm_le {d : ℕ} (w : Fin d → ℚ) (oracle : (Fin d → ℤ) → ℤ → Bool)
    (z : Fin d → ℤ) (last : Fin d) (q : ℕ) (hq : 0 < q)
    (hshort : ‖requestGraph w z‖ ≤ requestCutoff d) (k : ℤ)
    (hk : k ∈ (requestGridRun oracle z last q (requestCutoff d)).2) :
    let args := requestGridArgs z last q k
    (∑ i, |args.1 i|) + |args.2| ≤ 4 * (q : ℤ) * (requestCutoff d : ℤ)^2 := by
  let K := requestCutoff d
  have hK : 0 < K := by dsimp [K, requestCutoff]; positivity
  have hd : d ≤ K := by
    have h := Nat.le_mul_of_pos_left (d+3) (show 0 < 2^(d+2) by positivity)
    dsimp [K, requestCutoff]
    omega
  have hk' := requestGridRun_threshold oracle z last q K hq hK k hk
  have hc (i : Fin d) : |z i| ≤ (K : ℤ) := by exact_mod_cast (requestGraph_coords_le hshort).1 i
  have hsum : (∑ i, |z i|) ≤ (d : ℤ) * K := by
    calc (∑ i, |z i|) ≤ ∑ _ : Fin d, (K : ℤ) := Finset.sum_le_sum (fun i _ => hc i)
         _ = _ := by simp
  have hsum' := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℤ) ≤ q)
  have hconst := mul_le_mul hk' (hc last) (abs_nonneg _) (by positivity)
  have hd' : (d : ℤ) ≤ K := by exact_mod_cast hd
  have hdim := mul_le_mul_of_nonneg_right hd' (show 0 ≤ (q : ℤ) * K by positivity)
  dsimp only
  by_cases hz : 0 < z last <;>
    simp only [requestGridArgs, hz, ↓reduceIte, abs_mul, abs_neg, Int.abs_natCast, ← Finset.mul_sum] <;>
    change _ ≤ 4 * (q : ℤ) * (K : ℤ)^2 <;>
    nlinarith only [hsum', hconst, hdim]

/-- For grid denominator `2^p` all these queries have one-norm at most this power of
two. Thus their bit lengths are polynomial even if the input logarithms are very large. -/
theorem requestGridArgs_bit_cap (d p : ℕ) :
    4 * 2^p * (requestCutoff d)^2 ≤ 2^(p+4*d+12) := by
  have hd : d+3 ≤ 2^(d+3) := by exact Nat.le_of_lt (Nat.lt_two_pow_self (n := d+3))
  have hk : requestCutoff d ≤ 2^(d+2) * 2^(d+3) := Nat.mul_le_mul_left _ hd
  rw [← pow_add] at hk
  calc
    4 * 2^p * (requestCutoff d)^2 ≤ 4 * 2^p * (2^(d+2+(d+3)))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 2)
    _ = 2^(p+4*d+12) := by
      rw [← pow_mul, show 4 = (2 : ℕ)^2 by decide, ← pow_add, ← pow_add]
      congr 1
      omega

end Compression
end LinearProgramming
end Optimization
end OAI
