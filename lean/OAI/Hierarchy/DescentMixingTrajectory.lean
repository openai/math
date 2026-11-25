import OAI.Hierarchy.DescentConditionalRow
import OAI.Hierarchy.DescentMixingScores

namespace OAI
/-! # Computing the combined exceptional-base estimator from its collision weights -/

namespace Hierarchy.DescentBaseVariance

open DescentGL DescentLinearLayouts DescentRowScore
open scoped BigOperators Classical
noncomputable section

private abbrev DepthWeights (bits : ℕ) := Fin (bits+1) → Nonzero bits → ℝ

/-- A single load vector contributes its autocorrelation only at its own depth. -/
def depthCorrelation {bits : ℕ} (j : Fin (bits+1)) (x : Bits bits → ℝ) :
    Fin (bits+1) → Nonzero bits → ℝ :=
  fun l d => if l=j then autocorrelation x d.val else 0

private def collisionLinear {bits : ℕ} (L : Layout bits) : DepthWeights bits →ₗ[ℝ] ℝ where
  toFun w := allDepthCollisionCost w L
  map_add' f g := by simp only [allDepthCollisionCost,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' a f := by simp [allDepthCollisionCost,Finset.mul_sum]

private theorem at_depth {bits : ℕ} (L : Layout bits) (j : Fin (bits+1)) (x : Bits bits → ℝ) :
    collisionLinear L (depthCorrelation j x) = offDiagonal (Nat.le_of_lt_succ j.isLt) L x := by
  change (∑ l : Fin (bits+1), ∑ d : Nonzero bits, depthCorrelation j x l d *
    (if headRows (Nat.le_of_lt_succ l.isLt) (L d.val)=0 then 1 else 0)) = _
  rw [Finset.sum_eq_single j]
  · unfold offDiagonal
    rw [Finset.sum_subtype (p:=fun d : Bits bits => d≠0) (Finset.univ.erase 0) (fun _=>by simp)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hit : headRows (Nat.le_of_lt_succ j.isLt) (L d.val)=0 <;>
      simp [depthCorrelation,layout,hit]
  · intro l _ ne
    simp [depthCorrelation,ne]
  · simp

variable {A C : Type*} [Fintype A] [Fintype C] {bits : ℕ}
variable (levels : A → ℕ) (j : (a : A) → Fin (levels a) → ℕ) (hj : ∀ a s,j a s≤bits)
variable (cj : C → ℕ) (hcj : ∀ c,cj c≤bits)
variable (x : A → Bits bits → ℝ) (y : C → Bits bits → ℝ) (k : ℕ) (B K : ℝ)

/-- The weighted autocorrelation tables of all base levels and neighbor pairs,
including the common scale of the combined estimator. -/
def mixingCollisionWeights : Fin (bits+1) → Nonzero bits → ℝ :=
  ((2:ℝ)^k*B) • ((∑ a, ∑ s : Fin (levels a),
    (4*(2:ℝ)^((s.val+7)/8)) • depthCorrelation ⟨j a s,Nat.lt_succ_of_le (hj a s)⟩ (x a)) +
    ∑ c, K^2 • depthCorrelation ⟨cj c,Nat.lt_succ_of_le (hcj c)⟩ (y c))

/-- The coefficient read from the combined table at a particular depth and
nonzero difference. Both families use the same original bit addresses. -/
theorem mixingCollisionWeights_apply (l : Fin (bits+1)) (d : Nonzero bits) :
    mixingCollisionWeights levels j hj cj hcj x y k B K l d = ((2:ℝ)^k*B)*
      ((∑ a, ∑ s : Fin (levels a), (4*(2:ℝ)^((s.val+7)/8))*
        (if l.val=j a s then autocorrelation (x a) d.val else 0)) +
       ∑ c, K^2*(if l.val=cj c then autocorrelation (y c) d.val else 0)) := by
  simp [mixingCollisionWeights,depthCorrelation,Finset.sum_apply,Fin.ext_iff]

/-- The simultaneous level and capacity estimator evaluated on a single layout. -/
def mixingPotential (L : Layout bits) : ℝ :=
  ((2:ℝ)^k*B)*((∑ a,∑ s : Fin (levels a),4*(2:ℝ)^((s.val+7)/8)*
      levelCharge s.val (2^k) (layout (hj a s) L) (x a)) +
    ∑ c,K^2*variance (layout (hcj c) L) (y c))

/-- The layout-independent contribution left after removing the nonzero
vector differences from the combined estimator. -/
def mixingOffset : ℝ :=
  ((2:ℝ)^k*B)*((∑ a,∑ s : Fin (levels a),4*(2:ℝ)^((s.val+7)/8)*
    (if 1/(2:ℝ)^k≤1/(2:ℝ)^s.val then
      (∑ i,x a i^2) - (∑ i,x a i)^2/(2:ℝ)^(j a s) else 0)) +
    ∑ c,K^2*((∑ i,y c i^2) - (∑ i,y c i)^2/(2:ℝ)^(cj c)))

/-- The full estimator differs from the all-depth collision objective by the
explicit constant contributed by the squared masses and means. -/
theorem mixingPotential_eq (L : Layout bits) :
    mixingPotential levels j hj cj hcj x y k B K L = mixingOffset levels j cj x y k B K +
      allDepthCollisionCost (mixingCollisionWeights levels j hj cj hcj x y k B K) L := by
  change _ = _ + collisionLinear L _
  simp only [mixingPotential,mixingOffset,level_by_difference,variance_by_difference,
    mixingCollisionWeights,map_add,map_smul,map_sum,smul_eq_mul,at_depth,mul_add,Finset.sum_add_distrib]
  ring

/-- The tie-broken row controller simultaneously derandomizes all base levels
and capacity pairs in the original, scaled variance estimator. -/
theorem chosen_mixingTrajectory (initial : Layout bits) :
    let cost := mixingPotential levels j hj cj hcj x y k B K
    let weights := mixingCollisionWeights levels j hj cj hcj x y k B K
    ∃ run : ℕ → Layout bits, run 0=initial ∧
      (∀ i : Fin bits, (∀ l < i.val,layoutRow (run (i.val+1)) l=layoutRow (run i.val) l) ∧
        rowFunctional (run (i.val+1)) i = (rowIndex bits).symm (chosenIndex i.isLt (run i.val)
          (collisionRowData i weights (run i.val)).2) ∧
        prefixMean cost (run (i.val+1)) (i.val+1) ≤ prefixMean cost (run i.val) i.val) ∧
      cost (run bits) ≤ average cost := by
  let weights := mixingCollisionWeights levels j hj cj hcj x y k B K
  let cost := mixingPotential levels j hj cj hcj x y k B K
  let offset := mixingOffset levels j cj x y k B K
  have splitCost : cost = fun L => offset+allDepthCollisionCost weights L :=
    funext (mixingPotential_eq levels j hj cj hcj x y k B K)
  have mean (L : Layout bits) (m : ℕ) : prefixMean cost L m = offset+prefixMean (allDepthCollisionCost weights) L m :=
    by rw [splitCost, prefixMean_const_add]
  obtain ⟨run,start,steps,bound⟩ := chosenRow_collisionTrajectory initial weights
  refine ⟨run,start,fun i=>?_,?_⟩
  · obtain ⟨agree,index,decrease⟩ := steps i
    refine ⟨agree,index,?_⟩
    change prefixMean cost _ _ ≤ prefixMean cost _ _
    rw [mean,mean]
    exact add_le_add_right decrease offset
  · change cost (run bits) ≤ (∑L,cost L)/Fintype.card (Layout bits)
    rw [←prefixMean_zero cost initial,mean,congrFun splitCost (run bits),prefixMean_zero]
    exact add_le_add_right bound offset

end
end Hierarchy.DescentBaseVariance

end OAI
