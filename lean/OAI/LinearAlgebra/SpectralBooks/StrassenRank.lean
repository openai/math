import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum
import OAI.LinearAlgebra.SpectralBooks.PowerThreshold
import OAI.LinearAlgebra.SpectralBooks.RankLimit

namespace OAI
/-!
# Strassen's spectral formula for tensor rank

The asymptotic rank of a tensor is the largest value of a normalized spectral
point. A strict upper bound for all spectral values of a power supplies a
comparison with a diagonal. Its fixed multiplicative constant disappears in
further powers, giving the required upper bound on asymptotic rank.
-/

noncomputable section

namespace LinearAlgebra.SpectralBooks.SiteTensor

open Set Filter
open scoped NNReal Topology Classical

universe v
section
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- Rank is the smallest size of a full diagonal admitting a local restriction
to the given tensor. -/
def rank (T : TensorClass.{v} I K) : ℕ := Nat.find (exists_le_natCast T)

theorem le_rank (T : TensorClass.{v} I K) : T ≤ (rank T : TensorClass I K) :=
  Nat.find_spec (exists_le_natCast T)

theorem rank_le_of_le {T : TensorClass.{v} I K} {n : ℕ} (h : T ≤ (n : TensorClass I K)) :
    rank T ≤ n := Nat.find_min' (exists_le_natCast T) h

@[simp] theorem rank_zero : rank (0 : TensorClass.{v} I K) = 0 :=
  Nat.eq_zero_of_le_zero (rank_le_of_le (by simp))

theorem rank_mul_le (T U : TensorClass.{v} I K) : rank (T * U) ≤ rank T * rank U :=
  rank_le_of_le (by simpa using mul_mono (le_rank T) (le_rank U))

/-- The infimum of tensor-power rank roots. -/
def asymptoticRank (T : TensorClass.{v} I K) : ℝ :=
  ⨅ n : ℕ, (rank (T ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

theorem asymptoticRank_nonneg (T : TensorClass.{v} I K) : 0 ≤ asymptoticRank T :=
  le_ciInf fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The roots of the positive tensor-power ranks converge to their infimum. -/
theorem tendsto_rank_root (T : TensorClass.{v} I K) :
    Tendsto (fun n : ℕ => (rank (T ^ n) : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 (asymptoticRank T)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, asymptoticRank] using
    tendsto_root_of_submultiplicative (fun n => rank (T ^ n))
      (fun m n => by simpa only [pow_add] using rank_mul_le (T ^ m) (T ^ n))

private theorem pow_asymptoticRank_le_rank (T : TensorClass.{v} I K) {k : ℕ} (hk : 0 < k) :
    (asymptoticRank T)^k ≤ rank (T ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have h := ciInf_le (f := fun n : ℕ =>
    (rank (T ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)) ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ m
  apply (pow_le_pow_left₀ (asymptoticRank_nonneg T) h _).trans_eq
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Nat.cast_succ,
    inv_mul_cancel₀ (by positivity : (m + 1 : ℝ) ≠ 0), Real.rpow_one]

/-- Every normalized point is bounded by asymptotic rank, by comparison of
each power with a diagonal. -/
theorem spectral_value_le_asymptoticRank
    (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (T : TensorClass.{v} I K) : (f.val T : ℝ) ≤ asymptoticRank T := by
  apply le_ciInf
  intro n
  let φ := normalizedSpectrum.toRingHom f
  have h : φ (T^(n+1)) ≤ φ (rank (T^(n+1)) : TensorClass I K) := f.property.2.2.2.2 _ _ (le_rank _)
  rw [map_pow, map_natCast] at h
  have hr : (φ T : ℝ) ^ (n+1) ≤ rank (T^(n+1)) := by exact_mod_cast h
  change (φ T : ℝ) ≤ _
  simpa only [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), Nat.cast_succ,
    mul_inv_cancel₀ (by positivity : (n+1:ℝ) ≠ 0), Real.rpow_one] using
    Real.rpow_le_rpow (pow_nonneg (NNReal.coe_nonneg _) _) hr (by positivity : (0:ℝ) ≤ (n+1:ℝ)⁻¹)

end

variable {I K : Type*} [Fintype I] [Field K]

/-- A point of the normalized spectrum attains the asymptotic rank for every
tensor over its ground field when there are at least two sites. -/
theorem exists_spectral_value_eq_asymptoticRank [Nontrivial I] (T : TensorClass.{v} I K) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop), (f.val T : ℝ) = asymptoticRank T := by
  obtain ⟨g, hg, hmax⟩ := isCompact_spectrum.exists_isMaxOn (spectrum_nonempty I K)
    (continuous_apply T).continuousOn
  let f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop) := ⟨g, hg⟩
  refine ⟨f, le_antisymm (spectral_value_le_asymptoticRank f T) ?_⟩
  by_cases hz : T = 0
  · subst T
    simpa only [pow_one, rank_zero, Nat.cast_zero, f.property.1, NNReal.coe_zero] using
      pow_asymptoticRank_le_rank (I := I) (K := K) 0 (k := 1) (by decide)
  by_contra! hgap
  have hone : (1:ℝ) ≤ (f.val T : ℝ) := by exact_mod_cast one_le_spectral_value f (one_le_of_ne_zero hz)
  obtain ⟨k, r, hk, hr, hsmall, hlarge⟩ := exists_nat_between_powers hone hgap
  let φ := normalizedSpectrum.toRingHom f
  have hdiag : (r : TensorClass.{v} I K) ≠ 0 := by
    intro heq
    have hφ := congrArg φ heq
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at hφ
    exact hr.ne' hφ
  have strict (e : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      e.val (T^k) < e.val r := by
    let q := normalizedSpectrum.toRingHom e
    change q (T^k) < q r
    rw [map_pow, map_natCast]
    have he : e.val T ≤ f.val T := hmax e.property
    exact (pow_le_pow_left' he k).trans_lt (by exact_mod_cast hsmall)
  obtain ⟨C, _, hc⟩ := strictSpectralComparison I K _ _ (pow_ne_zero k hz) hdiag strict
  have hp (n : ℕ) (hn : 0 < n) : ((asymptoticRank T)^k)^n ≤ (C : ℝ) * (r:ℝ)^n := by
    have hh : T^(k*n) ≤ ((C * r^n : ℕ) : TensorClass I K) := by
      simpa [pow_mul, nsmul_eq_mul] using hc n hn
    rw [← pow_mul]
    exact (pow_asymptoticRank_le_rank T (Nat.mul_pos hk hn)).trans (by exact_mod_cast rank_le_of_le hh)
  exact (not_lt_of_ge (le_of_pow_le_const_mul_pow (by exact_mod_cast hr) hp)) hlarge

end LinearAlgebra.SpectralBooks.SiteTensor

end
end OAI
