import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.CorrectionFrame

namespace OAI
/-! # Physical layer distances and finite length codes on the core board -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe CorrectionFrame
open scoped Classical RealInnerProductSpace
noncomputable section

private theorem axis_dist {k : ℕ} (i j : Fin k) (diff : i≠j) (s t : Bool) :
    dist (point (some (i,s))) (point (some (j,t)))=Real.sqrt 2 := by
  have orth : Inner.inner ℝ (point (some (i,s))) (point (some (j,t))) = 0 := by
    cases s <;> cases t <;> simp [point,EuclideanSpace.inner_single_left,diff]
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [dist_eq_norm,norm_sub_sq_real,orth,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  cases s <;> cases t <;> norm_num [point]

/-- This distance uses the actual signed Euclidean coordinates used by the
tagged defect price. It applies to every boot/core link before any pruning. -/
theorem layer_distance {S : PurchaseSampler} {h d k : ℕ} (π : Equiv.Perm (Fin (2^h)))
    (M : ℕ) (e : Edges S h d k) : M*dist (point (ends π e).1.2) (point (ends π e).2.2) ≤
      coreLength (freeLength M) e := by
  rcases e with free|⟨⟨p,t⟩,l⟩
  · rcases free with ⟨c,j,s⟩|⟨c,a,s,u⟩|⟨f,l⟩|⟨f,l⟩
    · cases s <;> simp [ends,freeEnds,coreLength,freeLength,point]
    · change (M:ℝ)*dist (point (some (a.val.1,s))) (point (some (a.val.2,u))) ≤ (⌈Real.sqrt 2*(M:ℝ)⌉:ℤ)
      rw [axis_dist _ _ (ne_of_lt a.property) s u,mul_comm]
      exact Int.le_ceil _
    · simp [ends,freeEnds,coreLength,freeLength]
    · rcases f with ⟨t,g,⟨o,i⟩⟩
      simp [ends,freeEnds,coreLength,freeLength]
  · simp [ends,coreLength]

theorem cross_scale_zero {S : PurchaseSampler} {h d k : ℕ} (π : Equiv.Perm (Fin (2^h)))
    (t : ℝ) (e : Edges S h d k) (cross : (ends π e).1.2 ≠ (ends π e).2.2) :
    coreScale t e=0 := by
  rcases e with e|⟨⟨p,j⟩,l⟩
  · rfl
  · exact (cross rfl).elim

/-- All charges are integers from a four-element public menu. -/
theorem length_code {S : PurchaseSampler} {h d k : ℕ} (M : ℕ) (e : Edges S h d k) :
    ∃ z ∈ ({0,1,(M:ℤ),⌈Real.sqrt 2*(M:ℝ)⌉} : Finset ℤ),
      coreLength (freeLength M) e=z := by
  rcases e with e|e
  · rcases e with r|r|r
    · exact ⟨M, by simp, by simp [coreLength,freeLength]⟩
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨0, by simp, by simp [coreLength,freeLength]⟩
  · exact ⟨1, by simp, by simp [coreLength]⟩

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
