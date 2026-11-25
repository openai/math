import OAI.Computability.NearSquareRoot.PrecisionFlatWalshUnlane

/-! # Euclidean norms of the physical split and reassembled Walsh banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open PhysicalWalshNode

private def regroup {G B T U L : Type*} (e : L ≃ (G × T) × U) :
    ((G × B × T) × U) ≃ B × L where
  toFun x := (x.1.2.1, e.symm ((x.1.1,x.1.2.2),x.2))
  invFun x := (((e x.2).1.1,x.1,(e x.2).1.2), (e x.2).2)
  left_inv x := by simp only [Equiv.apply_symm_apply]
  right_inv x := by
    change (x.1,e.symm (e x.2)) = x
    rw [e.symm_apply_apply]

private theorem regroup_pos {G B T U L : Type*} (e : L ≃ (G × T) × U) (g : G) (b : B) (t : T) (u : U) :
    (regroup e).symm (b,e.symm ((g,t),u)) = ((g,b,t),u) := by
  change (((e (e.symm ((g,t),u))).1.1,b,(e (e.symm ((g,t),u))).1.2),(e (e.symm ((g,t),u))).2) = _
  rw [e.apply_symm_apply]

private def bankChart (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) :
    Fin (count (a+1) s) ≃ Fin W × Fin (laneCount a W s) :=
  (chart a W s hl hd).trans (regroup (laneChart a W s hl))

private theorem bankChart_pos (a W : ℕ) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    (bankChart a W s hl hd).symm (b,(laneChart a W s hl).symm ((g,t),u)) =
      (chart a W s hl hd).symm ((g,b,t),u) := by
  exact congrArg (chart a W s hl hd).symm (regroup_pos (laneChart a W s hl) g b t u)

private theorem squared_lanes (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (x : EuclideanSpace ℂ (Fin (count (a+1) s))) (y : Fin W → EuclideanSpace ℂ (Fin (laneCount a W s)))
    (eqn : ∀ b i, x ((bankChart a W s hl hd).symm (b,i)) = y b i) :
    ‖x‖^2 = ∑ b, ‖y b‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← (bankChart a W s hl hd).symm.sum_comp, Fintype.sum_prod_type]
  simp only [eqn]

/-- The Euclidean norm of any single physical lane is at most that of the
complete input row, for arbitrary complex values at the physical ordinals. -/
theorem idealLane_norm_le (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (x : IdealRow) (b : Fin W) :
    ‖atWidth (laneCount a W s) (idealLane (a+1) W s x b)‖ ≤ ‖atWidth (count (a+1) s) x‖ := by
  let y (l : Fin W) := atWidth (laneCount a W s) (idealLane (a+1) W s x l)
  have cut := squared_lanes a W s hl hd (atWidth (count (a+1) s) x) y (by
    intro l i
    obtain ⟨⟨⟨g,t⟩,u⟩,rfl⟩ := (laneChart a W s hl).symm.surjective i
    rw [bankChart_pos]
    change x ((chart a W s hl hd).symm ((g,l,t),u)) =
      idealLane (a+1) W s x l ((laneChart a W s hl).symm ((g,t),u))
    rw [chart_symm_val, laneChart_symm_val, idealLane_chart a W s hl])
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [cut]
  exact Finset.single_le_sum (fun l _ => sq_nonneg ‖y l‖) (Finset.mem_univ b)

/-- The squared error after reassembly is exactly the sum of the squared
lane errors in the signed-record and ideal layouts. -/
theorem unlane_gap_sq (a W p : ℕ) (hW : 0 < W) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (x : Fin W → Data s) (y : Fin W → IdealRow) :
    ‖atWidth (count (a+1) s) (meaningRow p (unlane (a+1) hW s x)) -
      atWidth (count (a+1) s) (idealUnlane (a+1) hW s y)‖^2 =
      ∑ b, (laneGap a W p s (x b) (y b))^2 := by
  apply squared_lanes a W s hl hd _ (fun b =>
    atWidth (laneCount a W s) (meaningRow p (x b)) - atWidth (laneCount a W s) (y b))
  intro b i
  obtain ⟨⟨⟨g,t⟩,u⟩,rfl⟩ := (laneChart a W s hl).symm.surjective i
  rw [bankChart_pos]
  let l := (laneChart a W s hl).symm ((g,t),u)
  let j := (chart a W s hl hd).symm ((g,b,t),u)
  change IntegerMultiplication.Grid.meaning p s.w (unlane (a+1) hW s x j) -
    idealUnlane (a+1) hW s y j = IntegerMultiplication.Grid.meaning p s.w (x b l) - y b l
  unfold j l
  rw [unlane_chart, idealUnlane_chart, laneChart_symm_val]

/-- A uniform error allowance for each physical lane transfers to the
reassembled row. -/
theorem unlane_gap_le (a W p : ℕ) (hW : 0 < W) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (x : Fin W → Data s) (y : Fin W → IdealRow)
    (e : ℝ) (hgap : ∀ b, laneGap a W p s (x b) (y b) ≤ e) :
    ‖atWidth (count (a+1) s) (meaningRow p (unlane (a+1) hW s x)) -
      atWidth (count (a+1) s) (idealUnlane (a+1) hW s y)‖ ≤ (W:ℝ)*e := by
  let f (b : Fin W) := laneGap a W p s (x b) (y b)
  have hf (b : Fin W) : 0 ≤ f b := norm_nonneg _
  calc
    _ ≤ ∑ b, f b := by
      apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun b _ => hf b)).mp
      rw [unlane_gap_sq a W p hW s hl hd]
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun b _ => hf b)
    _ ≤ ∑ _ : Fin W, e := Finset.sum_le_sum fun b _ => hgap b
    _ = _ := by simp

end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
