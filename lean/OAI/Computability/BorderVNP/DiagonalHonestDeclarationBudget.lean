import OAI.Computability.BorderVNP.DiagonalSharedDeclarationCapacity
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBudget

/-! # Admission of the true cube declaration before its native execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical VPVNP VPVNP.MotifBase TeamScales Filter
open scoped BigOperators
open private range_sum from OAI.Computability.BorderVNP.CubeGroupWeightPhysicalSchedule

variable {l : Layout} {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
    {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
    {recv : A → Fin l.cells} {w : A → ℕ}

/-- The pure row declaration satisfies both integer guards as soon as the
total cost and each individual symbol obey the paper's balancing estimates. -/
theorem declarationCapacity_of_cost {X R : ℕ}
    (total : (∑ u, jointCost blocks b K h D label recv w u) ≤ ((X*(R+1) : ℕ) : ℚ)/1024)
    (maxGroup : ∀ u, jointCost blocks b K h D label recv w u ≤ (X : ℚ)/1024) :
    declarationCapacity R X blocks b K h D label recv w := by
  let weight := declarationWeight blocks b K h D label recv w
  let f := fun i => TeamNative.unscale (weight i)
  let budget : TeamBudget.Layout := ⟨R+1,X,0⟩
  have word (i : Fin l.groups) : f i.val = jointCost blocks b K h D label recv w i := by
    simp only [f,weight,declarationWeight,dite_eq_left i.isLt,TeamNative.unscale_scaledWeight,jointCost]
  have sum : (∑ i ∈ Finset.range l.groups, f i) = ∑ u, jointCost blocks b K h D label recv w u := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => word i)
  have mean : (∑ i ∈ Finset.range l.groups, f i)/((R : ℚ)+1) ≤ (X : ℚ)/1024 := by
    rw [sum]
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast at total
    linarith only [total]
  refine ⟨fun j => (budget.le_teamLimit _).mpr ?_,(budget.le_totalLimit _).mpr ?_⟩
  · have seen (v : ℚ) (hv : v ∈ (List.range l.groups).map f) : 0≤v ∧ v≤(X:ℚ)/1024 := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
      exact ⟨by dsimp only [f,TeamNative.unscale]; positivity, (word ⟨i,List.mem_range.mp hi⟩).trans_le (maxGroup _)⟩
    have load := assigned_weight_le _ ((X:ℚ)/1024) (by positivity) seen j
    rw [range_sum] at load
    change TeamNative.unscale (TeamNative.loads R weight l.groups j) ≤ (X : ℚ)/256
    rw [congrFun (TeamNative.loads_unscale R weight l.groups) j]
    change assignGroups ((List.range l.groups).map f) (fun _ => 0) j ≤ _
    linarith only [load,mean,show (0:ℚ)≤X by positivity]
  · have additive : TeamNative.unscale (∑ i ∈ Finset.range l.groups, weight i) = ∑ i ∈ Finset.range l.groups,f i := by
      simp only [f, TeamNative.unscale, Nat.cast_sum, Finset.sum_div]
    change TeamNative.unscale (∑ i ∈ Finset.range l.groups, weight i) ≤ (X:ℚ)*((R+1 : ℕ) : ℚ)/1024
    rw [additive,sum]
    exact_mod_cast total

end Cube.GroupWeights

namespace Diagonal.FixedCube

open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.GroupWeights VPVNP TeamScales Filter
open scoped BigOperators

/-- A single eventual range suffices for every selector of the fixed integer
family and every published network satisfying the group and delivery volume
estimates. Both integral capacity guards hold before a native run is chosen. -/
theorem eventually_declarationCapacity {F : Type*} [Field F] (cube : FixedCube F)
    {α ξ : ℝ} (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(cube.pred+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r R : ℕ) (l : Layout) (blocks : ℕ) (A : Type*) [Fintype A]
      (decl : LengthDeclaration cube.pred l.groups) (select : Packet cube.pred l.groups blocks → Selector cube.pred cube.copies cube.h)
      (label : Fin l.cells → Label (cube.pred+1) l.groups) (recv : A → Fin l.cells) (size : A → ℕ),
      1 ≤ r → (R+1 : ℝ) ≤ (k:ℝ)^(2*α) → l.groups=alphabet α k →
      blocks=blocksFor (exterior ξ r k*(R+1) : ℕ) (cube.h*cube.b) (l.groups^(cube.pred+1)) →
      passesLengths cube.b cube.width select decl →
      (∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits size => recv j.1) u) label ≤
        4*((exterior ξ r k*(R+1) : ℕ) : ℝ)/((l.groups^(cube.pred+1) : ℕ) : ℝ)) →
      (∑ j, size j) ≤ 3*(R+1)*r*literal α k →
      declarationCapacity R (exterior ξ r k) blocks cube.b cube.copies cube.h decl label recv size := by
  let M := cube.h*cube.width+MotifWidths.selectorBits cube.copies (Fintype.card (Edge (cube.pred+1))) cube.h+1
  have gap : 8*α*((cube.pred+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using hgap
  filter_upwards [eventually_group_charge_room hα hξ (cube.pred+1) (cube.h*cube.b) M cube.block_pos gap,
    eventually_ge_atTop 1] with k room hk
  intro r R l blocks A _ decl select label recv size hr hR groups count pass balanced data
  obtain ⟨small,localCap,pad,dataCap⟩ := room r (R+1) hr (by omega) (by exact_mod_cast hR)
  rw [←groups] at small localCap pad
  rw [←count] at pad
  have hd : 0 < l.groups := groups ▸ Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)
  have packet : M ≤ M*(2^cube.pred*(cube.h*cube.b)) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) cube.block_pos)
  apply declarationCapacity_of_cost (l := l)
  · exact sum_jointCost_le_cut (label := label) (recv := recv) cube.width select pass (exterior ξ r k*(R+1))
      cube.tolerance cube.scale_sqrt (cube.cost _ _ hd select) (by simpa only [Nat.cast_add,Nat.cast_one] using small)
      pad (dataCap _ data)
  · exact jointCost_le_symbol_budget cube.width select pass (exterior ξ r k) R M
      (Nat.succ_pos _) hd ((Nat.le_succ _).trans packet) balanced localCap pad

end Diagonal.FixedCube

end BorderVNP
end Computability
end OAI
