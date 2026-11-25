import OAI.Hierarchy.DescentMixingLayout
import OAI.Hierarchy.DescentMixingTrajectory

namespace OAI
/-! # The selected prefix rows achieve the geometric estimator bound -/

namespace Hierarchy.DescentBaseVariance
open DescentGL DescentLinearLayouts
open scoped BigOperators Classical
noncomputable section

/-- The least-index legal row at each step produces an invertible layout with
the simultaneous load and capacity bound on the original vectors. -/
theorem chosen_mixing_layout {A C : Type*} [Fintype A] [Fintype C]
    (bits k : ℕ) (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (hj : ∀ a s,j a s≤bits)
    (cj : C→ℕ) (hcj : ∀ c,cj c≤bits)
    (x : A→Bits bits→ℝ) (n : A→ℝ) (y : C→Bits bits→ℝ)
    (B K X : ℝ) (hB : 0<B) (count : ∀ a (s : Fin (levels a)),(2:ℝ)^(j a s)=n a*2^s.val)
    (hn : ∀ a,0<n a) (hx : ∀ a i,0≤x a i) (small : ∀ a i,x a i≤1/(2:ℝ)^k)
    (mass : ∀ a,∑ i,x a i≤n a) (hy : ∀ c i,0≤y c i) (thin : ∀ c i,y c i≤1/(2:ℝ)^k)
    (quota : (∑ c,∑ i,y c i)≤X/(2^k*B))
    (initial : Layout bits) :
    let r := (2:ℝ)^(1/8:ℝ)
    let cost := mixingPotential levels j hj cj hcj x y k B K
    let weights := mixingCollisionWeights levels j hj cj hcj x y k B K
    ∃ run : ℕ → Layout bits, run 0=initial ∧
      (∀ i : Fin bits, (∀ l < i.val,layoutRow (run (i.val+1)) l=layoutRow (run i.val) l) ∧
        rowFunctional (run (i.val+1)) i = (rowIndex bits).symm
          (chosenIndex i.isLt (run i.val) (collisionRowData i weights (run i.val)).2) ∧
        prefixMean cost (run (i.val+1)) (i.val+1) ≤ prefixMean cost (run i.val) i.val) ∧
      cost (run bits) ≤
        ((2:ℝ)^k*B)*(∑ a,n a)*(8*((2:ℝ)^k)^(-(7/8):ℝ)*(1/(r-1)+1/(1-r/2))) +
        K^2*X/2^k := by
  obtain ⟨run,start,steps,bound⟩ :=
    chosen_mixingTrajectory levels j hj cj hcj x y k B K initial
  exact ⟨run,start,steps,bound.trans
    (average_mixing_layout bits k levels j hj cj hcj x n y B K X hB count hn hx small mass hy thin quota)⟩

end
end Hierarchy.DescentBaseVariance

end OAI
