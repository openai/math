import OAI.Optimization.LinearProgramming.PriceGame.LearningPool

/-! # Number of mistaken representative changes across actual skeletons -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Reset

open Finset

/-- The integer widths begin below `2*R`; this estimate expresses the logarithmic
charge bound directly in the binary input length. -/
theorem log_range_le_bits {R : ℕ} (hR : 0 < R) :
    Real.log (2 * (R : ℝ)) ≤ 1 + (R.size : ℝ) := by
  have hpow : (R : ℝ) ≤ (2 : ℝ) ^ R.size := by exact_mod_cast (Nat.lt_size_self R).le
  have h₁ : 2 * (R : ℝ) ≤ (2 : ℝ) ^ (1 + R.size) := by
    simpa [pow_add] using (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
  have h₂ := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (R : ℝ)) h₁
  rw [Real.log_pow] at h₂
  have hlog : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ _ := h₂
    _ ≤ (((1 + R.size : ℕ) : ℝ)) * 1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ = _ := by simp

private theorem all_skeletons_le (N : ℕ) : Fintype.card (Skeleton N) ≤
    (Skeleton.enumerate N).length := by
  classical
  have h : (univ : Finset (Skeleton N)) ⊆ (Skeleton.enumerate N).toFinset :=
    fun s _ => List.mem_toFinset.mpr (Skeleton.mem_enumerate s)
  simpa only [card_univ] using (card_le_card h).trans (List.toFinset_card_le _)

/-- At each replacement, some genuinely issued probe compares the currently selected
representative differently from the bounded hidden integer assignment. Histories can be
adaptive and can jump over any number of successful trials between two replacements. -/
theorem number_of_changes {N : ℕ} (R T : ℕ) (hR : 0 < R) (P : Fin N → ℤ)
    (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ) + 1) (hist : ℕ → List (Probe N))
    (retain : ∀ t < T, hist t ⊆ hist (t + 1))
    (wrong : ∀ t < T, ∃ (s : Skeleton N) (q : Test N),
      q ∈ (hist (t + 1)).flatMap s.testsAt ∧
      compare (featureValue (Pool.selectedExpert R s (hist t) P).raw q.feature) q.threshold ≠
      compare (featureValue (fun i => (P i : ℚ)) q.feature) q.threshold) :
    T ≤ (Skeleton.enumerate N).length * 66 ^ 2 * (1 + 66 * (1 + R.size)) := by
  classical
  by_cases hT : T = 0
  · simp [hT]
  obtain ⟨s₀, q₀, _⟩ := wrong 0 (by omega)
  have hex (t : ℕ) : ∃ (s : Skeleton N) (q : Test N), t < T →
      q ∈ (hist (t + 1)).flatMap s.testsAt ∧
      compare (featureValue (Pool.selectedExpert R s (hist t) P).raw q.feature) q.threshold ≠
      compare (featureValue (fun i => (P i : ℚ)) q.feature) q.threshold := by
    by_cases ht : t < T
    · obtain ⟨s,q,h⟩ := wrong t ht
      exact ⟨s,q,fun _ => h⟩
    · exact ⟨s₀,q₀,by simp [ht]⟩
  choose ss qs hq using hex
  have hchanges := Selections.number_of_changes (fun s : Skeleton N => s.sources.card)
    R T hR (fun _ => 0) (fun s => Compact.pack s P)
    (fun s => Compact.pack_zero s P) (fun s => Compact.pack_int_box s R P hP)
    (fun s t => Compact.thresholds s (hist t))
    (fun s t ht => Compact.thresholds_mono s (retain t ht)) ss
    (fun t => Compact.endpoints (ss t) (qs t).feature) (fun t => (qs t).threshold)
    (fun t ht => Compact.threshold_mem _ _ _ (hq t ht).1) (by
      intro t ht
      have hm := (hq t ht).1
      have hw := (hq t ht).2
      change compare (featureValue (Compact.unpack (ss t) (Pool.selectedCompact R (ss t)
        (hist t) P)) (qs t).feature) _ ≠ _ at hw
      rw [Compact.featureValue_unpack (ss t) (hist (t+1)) (qs t) hm _
        (Pool.selectedCompact_zero R (ss t) (hist t) P),
        Compact.featureValue_pack (ss t) (hist (t+1)) (qs t) hm,
        ← Compact.pack_intCast] at hw
      exact hw)
  have hlog := log_range_le_bits hR
  have hlog₀ : 0 ≤ Real.log (2 * (R : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * R by omega))
  have htotal : (T : ℝ) ≤ (Fintype.card (Skeleton N) : ℝ) * 66^2 *
      (1 + 66 * (1 + (R.size : ℝ))) := by
    calc
      (T : ℝ) ≤ _ := hchanges
      _ ≤ ∑ _s : Skeleton N, (66 : ℝ)^2 * (1 + 66 * (1 + (R.size : ℝ))) := by
        apply sum_le_sum
        intro s _
        have hpN : s.sources.card + 1 ≤ 66 := Nat.succ_le_succ s.card_sources_le
        have hp : (s.sources.card : ℝ) + 1 ≤ 66 := by exact_mod_cast hpN
        simp only [Nat.cast_add, Nat.cast_one]
        apply mul_le_mul (pow_le_pow_left₀ (by positivity) hp 2)
        · exact add_le_add le_rfl (mul_le_mul hp hlog hlog₀ (by norm_num))
        · positivity
        · norm_num
      _ = _ := by simp; ring
  have hNat : T ≤ Fintype.card (Skeleton N) * 66^2 * (1 + 66 * (1 + R.size)) := by
    exact_mod_cast htotal
  exact hNat.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (all_skeletons_le N)))

/-- An explicit polynomial in the dimension and the binary length of the range. -/
theorem polynomial_bound {N : ℕ} (hN : 0 < N) (R : ℕ) :
    (Skeleton.enumerate N).length * 66^2 * (1 + 66 * (1 + R.size)) ≤
      ((N+1) * (2 * ((2*N^2)^64 * (1 + (N+1) * (2*N^2))))) *
        66^2 * (1 + 66 * (1 + R.size)) := by
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  apply (Skeleton.length_enumerate_le _ hN).trans
  have hD : States.Mass.depth N ≤ N + 1 := Nat.succ_le_succ (Nat.log2_le_self N)
  gcongr

end Reset
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
