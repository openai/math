import OAI.Computability.NearSquareRoot.InterchangeLogSlack
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Calls in one batched interchange

The stage count, rank fraction, label dimension, incidence bound and repair fraction
are kept separate. The scale `s` is `p²` in the label construction, the dimension
exponent `d` is `2p-1`, and `j` is `p`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter
open scoped Topology

/-- For all sufficiently large batch parameters `m`, the sum of the address changes
used by the stages and those used by spectral repair is at most `m^γ` per row.
All constants in the individual upper bounds may be enlarged to one common `K ≥ 1`.
The two hypotheses involving `q` express the choice of a power of two at scale
`m^(1/s)`. The rank and repair fractions are normalized by the number of labels
and the number of rows per label respectively. -/
theorem eventually_interchange_stage_calls (s d j : ℕ) (hs : 0 < s) (γ K : ℝ)
    (hK : 1 ≤ K) (hγ : 1 / 2 + ((d : ℝ) + j) / s < γ) :
    ∀ᶠ m : ℝ in atTop, ∀ (q : ℝ) (stages dim inc : ℕ) (rankFrac repairFrac : ℝ),
      1 ≤ q → m ≤ q ^ s → q ≤ 2 * m ^ (s : ℝ)⁻¹ →
      (stages : ℝ) ≤ K * Real.sqrt (m * (1 + Real.log m)) →
      (dim : ℝ) ≤ K * q ^ d →
      (inc : ℝ) ≤ K * q ^ j * (1 + Real.log q) ^ s →
      0 ≤ rankFrac → q ^ s * rankFrac ≤ K →
      0 ≤ repairFrac → 2 * m ^ 3 * repairFrac ≤ 1 →
      (stages : ℝ) * (K * dim * (1 + inc) * (1 + m * rankFrac)) +
          4 * m * repairFrac ≤ m ^ γ := by
  have hK0 : 0 ≤ K := by linarith
  let A := K ^ 3 * (1 + K) ^ 2 * (2 : ℝ) ^ (s + d + j)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_logSlack (A + 2) (by positivity) (s + 1) hγ] with m hm hslack
  intro q stages dim inc rankFrac repairFrac hq hms hqroot hst hD hinc hr hrank hrep hrepair
  have hm0 : 0 < m := by linarith
  have hq0 : 0 < q := by linarith
  let L := 1 + Real.log m
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hm]
  have hL0 : 0 ≤ L := by linarith
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog : 1 + Real.log q ≤ 2 * L := by
    have hroot : m ^ (s : ℝ)⁻¹ ≤ m := by
      convert Real.rpow_le_rpow_of_exponent_le hm (inv_le_one_of_one_le₀ hs') using 1
      rw [Real.rpow_one]
    have hq' : q ≤ 2 * m := hqroot.trans (by gcongr)
    have hb := Real.log_le_log hq0 hq'
    rw [Real.log_mul (by norm_num) hm0.ne'] at hb
    have h2 := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    dsimp [L]; linarith [Real.log_nonneg hm]
  have hst' : (stages : ℝ) ≤ K * m ^ (1 / 2 : ℝ) * L := by
    rw [Real.sqrt_mul hm0.le] at hst
    rw [← Real.sqrt_eq_rpow, mul_assoc]
    exact hst.trans (by gcongr; exact Real.sqrt_le_self_iff.mpr (Or.inr hL))
  have hproduct : 1 ≤ q ^ j * (2 * L) ^ s :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (one_le_pow₀ (by linarith))
  have hinc' : 1 + (inc : ℝ) ≤ (1 + K) * (q ^ j * (2 * L) ^ s) := by
    have hi' : (inc : ℝ) ≤ K * q ^ j * (2 * L) ^ s := hinc.trans (by
      gcongr; linarith [Real.log_nonneg hq])
    linarith
  have hr' : 1 + m * rankFrac ≤ 1 + K := by
    linarith [mul_le_mul_of_nonneg_right hms hr]
  have hrepair' : 4 * m * repairFrac ≤ 2 := by
    have hm' : m ≤ m ^ 3 := by nlinarith [sq_nonneg (m - 1), mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)]
    linarith [mul_le_mul_of_nonneg_right hm' hrep]
  let β := 1 / 2 + ((d : ℝ) + j) / s
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hqh : q ^ (d + j) ≤ (2 : ℝ) ^ (d + j) * m ^ (((d : ℝ) + j) / s) := by
    calc
      _ ≤ (2 * m ^ (s : ℝ)⁻¹) ^ (d + j) := by gcongr
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (m ^ (s : ℝ)⁻¹), ← Real.rpow_mul hm0.le]
        push_cast
        congr 2
        ring
  have hmain : (stages : ℝ) * (K * dim * (1 + inc) * (1 + m * rankFrac)) ≤
      A * L ^ (s+1) * m ^ β := by
    calc
      _ ≤ (K * m ^ (1 / 2 : ℝ) * L) *
          (K * (K * q ^ d) * ((1 + K) * (q ^ j * (2 * L) ^ s)) * (1 + K)) := by
            gcongr
      _ = K ^ 3 * (1 + K) ^ 2 * (2 : ℝ) ^ s * L ^ (s+1) *
          m ^ (1 / 2 : ℝ) * q ^ (d+j) := by rw [mul_pow, pow_succ, pow_add]; ring
      _ ≤ K ^ 3 * (1 + K) ^ 2 * (2 : ℝ) ^ s * L ^ (s+1) *
          m ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ (d+j) * m ^ (((d : ℝ) + j) / s)) := by gcongr
      _ = _ := by dsimp [A, β]; rw [Real.rpow_add hm0]; simp only [pow_add]; ring
  have habsorb : 1 ≤ L ^ (s+1) * m ^ β :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) (Real.one_le_rpow hm hβ)
  calc
    _ ≤ A * L ^ (s+1) * m ^ β + 2 := add_le_add hmain hrepair'
    _ ≤ (A + 2) * L ^ (s+1) * m ^ β := by linarith
    _ ≤ _ := hslack

/-- Choose the label radix for each sufficiently large natural `m`. The stage budget
counts calls on all streams: `R*N` is the batch size, `r` is the rank on the `N`
labels, and `defect` bounds the number of rows requiring spectral repair per label.
The final inequality is the stage count plus every repair call. -/
theorem eventually_interchange_batch_budget_with_power (p : ℕ) (hp : 0 < p) (γ K : ℝ)
    (hK : 1 ≤ K) (hγ : 1 / 2 + (3 * p - 1) / (p : ℝ) ^ 2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := (2 : ℝ) ^ k
      (m : ℝ) ≤ q ^ (p^2) ∧ q ≤ 2 * (m : ℝ) ^ ((p^2 : ℕ) : ℝ)⁻¹ ∧
      ∀ (stages dim inc r N defect R : ℕ), 0 < N → 0 < R →
        (stages : ℝ) ≤ K * Real.sqrt (m * (1 + Real.log m)) →
        (dim : ℝ) ≤ K * q ^ (2*p-1) →
        (inc : ℝ) ≤ K * q ^ p * (1 + Real.log q) ^ (p^2) →
        q ^ (p^2) * r ≤ K * N → 2 * m ^ 3 * defect ≤ R →
        (stages : ℝ) * (K * R * dim * (1 + inc) * (N + (m : ℝ) * r)) +
          4 * (m : ℝ) * defect * N ≤ (R : ℝ) * N * (m : ℝ) ^ γ := by
  have hs : 0 < p ^ 2 := pow_pos hp _
  have he : 1 / 2 + (((2*p-1 : ℕ) : ℝ) + p) / ((p^2 : ℕ) : ℝ) < γ := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*p), Nat.cast_pow]
    push_cast
    convert hγ using 1
    ring
  have hbudget := eventually_interchange_stage_calls (p^2) (2*p-1) p hs γ K hK he
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbudget,
    eventually_ge_atTop (1 : ℕ)] with m hb hm
  obtain ⟨k, _, hlow, hupp, _⟩ := exists_interchange_label_power (m : ℝ) (by exact_mod_cast hm)
    (p^2) hs
  refine ⟨k, hlow, hupp, ?_⟩
  intro stages dim inc r N defect R hN hR hst hd hi hr hrepair
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hr' : ((2 : ℝ) ^ k) ^ (p^2) * (r / (N : ℝ)) ≤ K := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hN').mpr hr
  have hdef : 2 * (m : ℝ)^3 * (defect / (R : ℝ)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_iff₀ hR', one_mul]
    exact_mod_cast hrepair
  have hb' := hb ((2 : ℝ)^k) stages dim inc (r / (N : ℝ)) (defect / (R : ℝ))
    (one_le_pow₀ (by norm_num)) hlow hupp hst hd hi (by positivity) hr' (by positivity) hdef
  calc
    _ = (R : ℝ) * N *
          ((stages : ℝ) * (K * dim * (1 + inc) * (1 + (m : ℝ) * (r / (N : ℝ)))) +
            4 * (m : ℝ) * (defect / (R : ℝ))) := by
              field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (by positivity)

/-- The full batch budget with the scale information omitted. -/
theorem eventually_interchange_batch_budget (p : ℕ) (hp : 0 < p) (γ K : ℝ)
    (hK : 1 ≤ K) (hγ : 1 / 2 + (3 * p - 1) / (p : ℝ) ^ 2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := (2 : ℝ) ^ k
      ∀ (stages dim inc r N defect R : ℕ), 0 < N → 0 < R →
        (stages : ℝ) ≤ K * Real.sqrt (m * (1 + Real.log m)) →
        (dim : ℝ) ≤ K * q ^ (2*p-1) →
        (inc : ℝ) ≤ K * q ^ p * (1 + Real.log q) ^ (p^2) →
        q ^ (p^2) * r ≤ K * N → 2 * m ^ 3 * defect ≤ R →
        (stages : ℝ) * (K * R * dim * (1 + inc) * (N + (m : ℝ) * r)) +
          4 * (m : ℝ) * defect * N ≤ (R : ℝ) * N * (m : ℝ) ^ γ := by
  filter_upwards [eventually_interchange_batch_budget_with_power p hp γ K hK hγ] with m hm
  obtain ⟨k, _, _, hb⟩ := hm
  exact ⟨k, hb⟩

end NearSquareRoot
end Computability
end OAI
