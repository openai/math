import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Selecting a summand by amplified strict comparison

In this file addition in `T` denotes tensor product of nonzero tensors, so a
logarithmic price is an additive homomorphism. Ordinary sums and restrictions
remain separate relations. We use the consequence of strict comparison obtained
by expanding a restriction of `K` direct copies of a tensor power and dropping
the zero images. The constant `K` may vary with the initial power `k`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

variable {T : Type*} [AddCommMonoid T]

/-- The expanded conclusion of strict spectral comparison for a finite direct sum.
Every nonzero summand in the target is the image of a word of length `n` in the
sources. Its price will be bounded using restriction monotonicity. -/
def ExpandedStrictComparison (spectrum : Set (T →+ ℝ))
    (restricts : T → T → Prop) (ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop) : Prop :=
  ∀ {J : ℕ} (X : T) (Y : Fin J → T), 0 < J →
    (∀ f ∈ spectrum, ∃ i, f X < f (Y i)) →
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∃ L : ℕ, 0 < L ∧ L ≤ K * J ^ n ∧ ∃ Z : Fin L → T,
        ordinarySum (n • X) L Z ∧
        ∀ l, ∃ w : Fin n → Fin J, restricts (Z l) (∑ t, Y (w t))

private theorem remove_constant {a b c : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ c + n * b) : a ≤ b := by
  by_contra! hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (sub_pos.mpr hab) c
  have hh := h (m + 1) (Nat.succ_pos _)
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hm hh
  linarith

/-- The finite alternative used in the proof of doubling. If each normalized
point prefers some `Y i` to `X`, a monotone price satisfying the ordinary-sum
estimate on all positive powers of `X` weakly prefers some `Y i` as well.
The two amplifications absorb first the constant number of direct copies and
then the cost of choosing one of the `J` sources. -/
theorem finite_comparison_of_ordinary_sum
    {spectrum : Set (T →+ ℝ)} {restricts : T → T → Prop}
    {ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop}
    (compare : ExpandedStrictComparison spectrum restricts ordinarySum)
    (h : T →+ ℝ) (mono : ∀ {x y}, restricts x y → h x ≤ h y)
    {C : ℝ} (hC : 0 ≤ C) {X : T}
    (stretch : ∀ (m L : ℕ) (Z : Fin L → T), 0 < m →
      ordinarySum (m • X) L Z → ∃ l, h (m • X) ≤ h (Z l) + C * Real.logb 2 L)
    {J : ℕ} (hJ : 0 < J) (Y : Fin J → T)
    (cover : ∀ f ∈ spectrum, ∃ i, f X < f (Y i)) : ∃ i, h X ≤ h (Y i) := by
  classical
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j => h (Y j)) Finset.univ_nonempty
  refine ⟨i, remove_constant (c := C * Real.logb 2 J) fun k hk => ?_⟩
  have hlarge (f : T →+ ℝ) (hf : f ∈ spectrum) : ∃ j, f (k • X) < f (k • Y j) := by
    obtain ⟨j, hj⟩ := cover f hf
    refine ⟨j, ?_⟩
    simpa only [map_nsmul, nsmul_eq_mul] using
      mul_lt_mul_of_pos_left hj (show (0 : ℝ) < k by exact_mod_cast hk)
  obtain ⟨K, hK, decompose⟩ := compare (k • X) (fun j => k • Y j) hJ hlarge
  apply remove_constant (c := C * Real.logb 2 K)
  intro n hn
  obtain ⟨L, hL, hcount, Z, hZ, hword⟩ := decompose n hn
  have hsum : ordinarySum ((n * k) • X) L Z := by rwa [Nat.mul_comm, mul_nsmul]
  obtain ⟨l, hprice⟩ := stretch (n * k) L Z (Nat.mul_pos hn hk) hsum
  obtain ⟨w, hw⟩ := hword l
  have hfactor : h (Z l) ≤ n * (k * h (Y i)) := calc
    h (Z l) ≤ h (∑ t, k • Y (w t)) := mono hw
    _ = ∑ t, k * h (Y (w t)) := by simp
    _ ≤ ∑ _t : Fin n, k * h (Y i) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hmax (w t) (Finset.mem_univ _)) (Nat.cast_nonneg _)
    _ = n * (k * h (Y i)) := by simp
  have hlog : Real.logb 2 L ≤ Real.logb 2 K + n * Real.logb 2 J := calc
    Real.logb 2 L ≤ Real.logb 2 ((K * J ^ n : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hL) (by exact_mod_cast hcount)
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  simp only [map_nsmul, nsmul_eq_mul, Nat.cast_mul] at hprice
  linarith only [hprice, hfactor, mul_le_mul_of_nonneg_left hlog hC]

end SpectralBooks
end LinearAlgebra
end OAI
