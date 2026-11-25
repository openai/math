import OAI.Hierarchy.CorrectionGap
import OAI.Hierarchy.CorrectionSize

namespace OAI
/-! # Physical sparse amplification with an arbitrary exact verifier -/

noncomputable section
namespace Hierarchy.Tagged

open ThreeFlat Routing Catalyst CorrectionFrame

def AmplificationBound (F : Type*) [Field F] (E K : ℕ) : Prop :=
    ∀ {k p s H : ℕ} (X : Approximation F k p)
      (f : (Fin p → Bool) → F) (N : BitNetwork F (Fintype.card (Fin p))) {D : ℝ},
      (∀ x, TypedWiring.value N x = f x) →
      N.cells+N.internal ≤ E*H*X.size → 0<s → 2≤H →
      (Nat.log 2 (s+1)+2)^3 ≤ X.size →
      4*(k:ℝ)*(Real.logb 2 H+3) ≤ D → X.Gap f D →
      ∃ Y : Approximation F k (s*p), Y.width = copiesWidth s X.width ∧
        Y.size ≤ K*s*X.size ∧ Y.Gap (dataProduct s f) ((s:ℝ)*D/(2*H))

/-- The spacing pays for the actual exact verifier. The same size constant
works in every characteristic and for every number of catalyst directions. -/
theorem amplify_exact_uniform (E : ℕ) :
    ∃ K : ℕ, ∀ (F : Type*) [Field F], AmplificationBound F E K := by
  obtain ⟨K,make⟩ := CorrectionSize.linear_batch_uniform E
  refine ⟨K,fun F _ {k p s H} X f N {D} eval cost hs hH logcost threshold gap => ?_⟩
  obtain ⟨A,size,rows⟩ := make F X N H hs hH logcost cost
  have fe := funext eval
  rw [fe] at rows
  have hHn : 0<H := by omega
  have hHr : 0<(H:ℝ) := by exact_mod_cast hHn
  have lt : s < (s/H+1)*H :=
    (Nat.div_lt_iff_lt_mul hHn).mp (Nat.lt_succ_self _)
  have copies : (s:ℝ)/H ≤ ((s/H:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hHr).mpr
    exact_mod_cast lt.le
  exact ⟨CorrectionBatch.package X.width A,rfl,size,CorrectionGap.amplified_all
    (by exact_mod_cast (show 1≤H by omega)) threshold (s/H) copies X f gap A rows⟩

theorem amplify_exact (F : Type*) [Field F] (E : ℕ) : ∃ K : ℕ, AmplificationBound F E K := by
  obtain ⟨K,universal⟩ := amplify_exact_uniform E
  exact ⟨K,universal F⟩

end Hierarchy.Tagged

end
end OAI
