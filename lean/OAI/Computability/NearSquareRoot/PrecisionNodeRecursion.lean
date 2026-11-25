import OAI.Computability.NearSquareRoot.PrecisionNodePlanStep
import OAI.Computability.NearSquareRoot.PrecisionPlanBase
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeExact
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshLaneNorm

/-! # The actual recursive node is ready and computes the normalized Walsh map

Induction is on the exponent of the selected piece. The template works on
the actual rounded banks produced by its preceding instructions. Its children
are complete normalized transforms, so earlier perturbations enter their
error budgets with coefficient one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace PhysicalWalshNode

open IntegerMultiplication KernelPass PhysicalWalsh FlatWalshNode

def recursionFactor {a W : ℕ} (plan : Plan (a+1) W W) := (W+2)*(templateFactor plan+2)

theorem run_accurate {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (hp : Correct plan)
    (N frac : ℕ) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (fault : Real.sqrt (N:ℝ)*((2:ℝ)/2^frac) ≤ δ) (s : Shape)
    (hd : W^s.level ∣ s.pref) (hN : count (a+1) s ≤ N) (room : T*2^frac < 2^s.w)
    (small : (recursionFactor plan:ℝ)^(s.level+1)*δ ≤ 1) :
    NodeAccurate hW plan frac s ((recursionFactor plan:ℝ)^(s.level+1))
      T ((recursionFactor plan:ℝ)^(s.level+1)*δ) := by
  let C : ℝ := recursionFactor plan
  let F : ℝ := templateFactor plan
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hCF : F+1 ≤ C := by
    change (templateFactor plan:ℝ)+1 ≤ (recursionFactor plan:ℝ)
    exact_mod_cast (show templateFactor plan+1 ≤ recursionFactor plan by unfold recursionFactor; nlinarith)
  have hC : 1 ≤ C := by linarith
  have hCW : (W:ℝ)*F ≤ C := by
    change (W:ℝ)*(templateFactor plan:ℝ) ≤ (recursionFactor plan:ℝ)
    exact_mod_cast (show W*templateFactor plan ≤ recursionFactor plan by unfold recursionFactor; nlinarith)
  generalize heq : s.level = h at *
  induction h generalizing s with
  | zero =>
    intro x M hm bound
    have hM : 0 ≤ M := (norm_nonneg _).trans hm
    have hmt : M ≤ T := by
      change C^(0+1)*(M+1) ≤ T at bound
      rw [pow_one] at bound
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) hM]
    obtain ⟨good,err⟩ := run_base_ideal_error hW plan frac s heq x M hm
      ((mul_le_mul_of_nonneg_right hmt (by positivity)).trans_lt room)
    refine ⟨good,err.trans ?_⟩
    change Real.sqrt (count (a+1) s) * _ ≤ C ^ (0+1) * δ
    have hsize := Real.sqrt_le_sqrt (show (count (a+1) s:ℝ) ≤ N by exact_mod_cast hN)
    exact ((mul_le_mul_of_nonneg_right hsize (by positivity)).trans fault).trans
      (by rw [pow_one]; exact le_mul_of_one_le_left hδ hC)
  | succ h ih =>
    let R := C^(h+1)
    have hR : 1 ≤ R := one_le_pow₀ hC
    have pos : 0 < s.level := by omega
    have hscale : R*C = C^(h+1+1) := (pow_succ ..).symm
    have hRC : R ≤ R*C := le_mul_of_one_le_right (by linarith) hC
    have hdiv : W^s.level ∣ s.pref := by simpa [heq] using hd
    have subsmall : R*δ ≤ 1 := by
      apply (mul_le_mul_of_nonneg_right hRC hδ).trans
      simpa only [hscale] using small
    have hface := fun (axis : Fin (a+1)) => volume_split (W := W) s axis pos hdiv
    have hsub (axis : Fin (a+1)) : count (a+1) (descend (a+1) W axis s) ≤ count (a+1) s := by
      rw [← hface axis]
      exact Nat.le_mul_of_pos_left _ hW
    have hLane : laneCount a W s ≤ N := by
      let axis : Fin (a+1) := 0
      exact (child_count s axis pos ▸ hsub axis).trans hN
    have hflt : Real.sqrt (laneCount a W s)*((2:ℝ)/2^frac) ≤ R*δ := by
      apply (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (show (laneCount a W s:ℝ) ≤ (N:ℝ) by exact_mod_cast hLane)) (by positivity)).trans
      exact fault.trans (le_mul_of_one_le_left hδ hR)
    have children axis : NodeAccurate hW plan frac (descend (a+1) W axis s) R T (R*δ) := by
      have depth : (descend (a+1) W axis s).level = h := by simp [descend,heq]
      have hcd := child_divisible s axis pos hdiv
      rw [depth] at hcd
      exact ih _ ((hsub axis).trans hN) room depth hcd subsmall
    have P := nodePlan_numericalStep hW plan s pos frac hT hR (mul_nonneg (by linarith) hδ) room hflt children
    intro x M hm bound
    have bound' : R*C*(M+1) ≤ T := by simpa only [hscale] using bound
    have hM : 0 ≤ M := (norm_nonneg _).trans hm
    let xs := lane (a+1) W s x
    let y := meaningRow frac x
    let ys := idealLane (a+1) W s y
    have bank : BankBall (l := PhysicalWalshGrid.layout (coords a W) Shape.w) (v := idealLayout) s (laneSize a W s) (laneGap a W frac s) xs ys M 0 := by
      intro b
      exact ⟨(idealLane_norm_le a W s pos hdiv y b).trans hm, by simp [xs,ys,y,laneGap,
        atWidth,meaningRow,lane,idealLane]⟩
    obtain ⟨ready,compare⟩ := P xs ys M 0 hM le_rfl (by
      simpa using nextCap_plan (lt_of_lt_of_le zero_lt_one hR) hF hM subsmall hCF bound') bank
    refine ⟨good_of_step hW plan pos ready, ?_⟩
    let recorded := (nodeOps hW plan).applyPlan plan s xs
    let ideal := (idealOps a W (childIdeal a W)).applyPlan plan s ys
    have gap b : laneGap a W frac s (recorded b) (ideal b) ≤ F*(R*δ) := by
      simpa using (compare b).2
    have output := unlane_gap_le a W frac hW s pos hdiv recorded ideal (F*(R*δ)) gap
    have eq := completeIdeal hW plan hp s pos hdiv y
    change atWidth _ (idealUnlane _ _ s ideal) = atWidth _ (idealRow _ s y) at eq
    rw [eq] at output
    rw [run_step hW plan s pos]
    apply output.trans
    change (W:ℝ)*(F*(R*δ)) ≤ C^(h+1+1)*δ
    rw [← hscale]
    nlinarith only [mul_le_mul_of_nonneg_right hCW (mul_nonneg (by linarith : 0 ≤ R) hδ)]

end PhysicalWalshNode

end

end NearSquareRoot
end Computability
end OAI
