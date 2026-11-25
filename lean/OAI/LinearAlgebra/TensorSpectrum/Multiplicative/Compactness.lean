import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective
import Mathlib.Tactic.Linarith

/-!
# Compactness for approximate projective eigenstates

An arbitrary product of real lines need not be sequentially compact. This file
therefore uses the finite-intersection property of the compact state set, rather
than selecting an unjustified convergent subsequence of approximate states.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

private theorem finite_positive_lower_bound (F : Finset {ε : ℝ // 0 < ε}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ F, δ ≤ ε.val := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert ε F _ ih =>
    obtain ⟨δ, hδ, hF⟩ := ih
    refine ⟨min ε.val δ, lt_min ε.property hδ, ?_⟩
    intro η hη
    rcases Finset.mem_insert.mp hη with rfl | hη
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hF η hη)

/-- Coordinatewise residual bounds with a common error parameter are enough to
obtain an exact eigenstate in an arbitrary compact subset of the product space. -/
theorem eigenstate_of_approximate (K : Set (S → ℝ)) (z : S) (r : ℝ)
    (B : S → ℝ) (hB : ∀ x, 0 ≤ B x) (hcompact : IsCompact K)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ f ∈ K, ∀ x, |f (z * x) - r * f x| ≤ ε * B x) :
    ∃ f ∈ K, f ∈ eigenSlice z r := by
  let A : {ε : ℝ // 0 < ε} → Set (S → ℝ) :=
    fun ε => {f | ∀ x, |f (z * x) - r * f x| ≤ ε.val * B x}
  have hclosed : ∀ ε, IsClosed (A ε) := by
    intro ε
    have heq : A ε = ⋂ x : S,
        {f : S → ℝ | |f (z * x) - r * f x| ≤ ε.val * B x} := by
      ext f
      simp only [A, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isClosed_iInter fun x => isClosed_le
      (((continuous_apply (z * x)).sub (continuous_const.mul (continuous_apply x))).abs)
      continuous_const
  have hfinite : ∀ F : Finset {ε : ℝ // 0 < ε},
      (K ∩ ⋂ ε ∈ F, A ε).Nonempty := by
    intro F
    obtain ⟨δ, hδ, hF⟩ := finite_positive_lower_bound F
    obtain ⟨f, hf, hres⟩ := happrox δ hδ
    refine ⟨f, hf, ?_⟩
    simp only [mem_iInter, A, mem_ofPred_eq]
    intro ε hε x
    exact (hres x).trans (mul_le_mul_of_nonneg_right (hF ε hε) (hB x))
  obtain ⟨f, hf, hall⟩ := hcompact.inter_iInter_nonempty A hclosed hfinite
  refine ⟨f, hf, ?_⟩
  intro x
  have hres : ∀ ε : ℝ, 0 < ε → |f (z * x) - r * f x| ≤ ε * B x := by
    intro ε hε
    exact (mem_iInter.mp hall ⟨ε, hε⟩) x
  have habs : |f (z * x) - r * f x| = 0 := by
    apply le_antisymm _ (abs_nonneg _)
    by_contra hnot
    have hp : 0 < |f (z * x) - r * f x| := lt_of_not_ge hnot
    have hden : 0 < B x + 1 := by linarith [hB x]
    let ε := |f (z * x) - r * f x| / (B x + 1)
    have hε : 0 < ε := div_pos hp hden
    have heq : ε * (B x + 1) = |f (z * x) - r * f x| :=
      div_mul_cancel₀ _ hden.ne'
    have hbound := hres ε hε
    nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

end OAI.LinearAlgebra.TensorSpectrum
