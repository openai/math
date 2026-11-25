import OAI.LinearAlgebra.SpectralBooks.Tensor
import Mathlib.Analysis.Subadditive

/-! # The limit defining asymptotic tensor rank

Splitting Kronecker powers gives a submultiplicative sequence of natural
ranks. Applying Fekete's lemma to their logarithms identifies the manuscript's
limit with the infimum of the positive-index rank roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

/-- The positive-index root infimum is the limit for a natural-valued
submultiplicative sequence, including sequences with a zero term. -/
theorem tendsto_root_of_submultiplicative (r : ℕ → ℕ)
    (hmul : ∀ m n, r (m + n) ≤ r m * r n) :
    Tendsto (fun n : ℕ => (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)) atTop
      (𝓝 (⨅ n : ℕ, (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹))) := by
  let root (n : ℕ) := (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)
  change Tendsto root atTop (𝓝 (⨅ n, root n))
  have hnonneg n : 0 ≤ root n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbdd : BddBelow (Set.range root) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  by_cases hz : ∃ k, r k = 0
  · obtain ⟨k, hk⟩ := hz
    have heq (n : ℕ) (hn : k ≤ n) : root n = 0 := by
      have h := hmul k (n + 1 - k)
      rw [show k + (n + 1 - k) = n + 1 by omega, hk, zero_mul, Nat.le_zero] at h
      simp [root, h, Real.zero_rpow (by positivity : ((n + 1 : ℝ)⁻¹) ≠ 0)]
    have hinf : (⨅ n, root n) = 0 :=
      le_antisymm ((ciInf_le hbdd k).trans_eq (heq k le_rfl)) (le_ciInf hnonneg)
    rw [hinf]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨k, fun n hn => (heq n hn).symm⟩)
  · push Not at hz
    have hpos (n : ℕ) : (0 : ℝ) < r n := by exact_mod_cast Nat.pos_of_ne_zero (hz n)
    let u (n : ℕ) := Real.log (r n)
    have hsub : Subadditive u := by
      intro m n
      dsimp [u]
      rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
      apply Real.log_le_log (hpos _)
      exact_mod_cast hmul m n
    have hu : BddBelow (Set.range fun n : ℕ => u n / n) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero (hz n))) (Nat.cast_nonneg _)
    have hroot n : root n = Real.exp (u (n + 1) / (n + 1)) := by
      dsimp only [root]
      rw [Real.rpow_def_of_pos (hpos _)]
      rfl
    have hlim : Tendsto root atTop (𝓝 (Real.exp hsub.lim)) := by
      have h := (Real.continuous_exp.continuousAt.tendsto.comp
        ((hsub.tendsto_lim hu).comp (tendsto_add_atTop_nat 1)))
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ← hroot] using h
    have hinf : (⨅ n, root n) = Real.exp hsub.lim := by
      refine le_antisymm (ge_of_tendsto' hlim (ciInf_le hbdd)) (le_ciInf fun n => ?_)
      rw [hroot, Real.exp_le_exp]
      simpa only [Nat.cast_succ] using
        hsub.lim_le_div hu (Nat.succ_ne_zero n)
    rwa [hinf]

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

private def splitPowerWord {A : Type*} (m n : ℕ) (x : Fin (m + n) → A) :
    (Fin m → A) × (Fin n → A) :=
  (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)

/-- Splitting each site's words into a prefix and suffix shows that the
rank of Kronecker powers is submultiplicative. -/
theorem tensorRank_power_add_le (T : Tensor F X Y Z) (m n : ℕ) :
    tensorRank (Tensor.power T (m + n)) ≤
      tensorRank (Tensor.power T m) * tensorRank (Tensor.power T n) := by
  have h := ((rankAtMost_tensorRank (Tensor.power T m)).product
    (rankAtMost_tensorRank (Tensor.power T n))).pullback
    (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
  apply tensorRank_le_of_rankAtMost
  have heq : Tensor.power T (m + n) = Tensor.pullback
      (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
      (Tensor.product (Tensor.power T m) (Tensor.power T n)) := by
    funext x y z
    exact Fin.prod_univ_add (fun i => T (x i) (y i) (z i))
  rw [heq]
  exact h

/-- The tensor-power rank roots converge to asymptotic rank. -/
theorem tendsto_tensorRank_power_root (T : Tensor F X Y Z) :
    Tendsto (fun n : ℕ => (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 (asymptoticRank T)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, asymptoticRank] using
    tendsto_root_of_submultiplicative (fun n => tensorRank (Tensor.power T n))
      (tensorRank_power_add_le T)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
