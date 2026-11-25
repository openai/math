import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentBaseOverload

namespace OAI
/-! # Identifying the same layout estimator on block words and binary vectors -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section
variable {k d : ℕ}

theorem address_load (hd : d≤k) (L : Layout k) (x : Block k → ℝ) (v : Bits d) :
    load (dyadicLayout hd L) x (address d v)=
      load (DescentLinearLayouts.layout hd L) (x ∘ address k) v := by
  unfold load
  rw [←(address k).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp [dyadicLayout,DescentLinearLayouts.layout];
    by_cases same : v = headRows hd (L i) <;> simp [same]

theorem address_mean (x : Block k → ℝ) :
    mean x (Block d)=mean (x ∘ address k) (Bits d) := by
  unfold mean
  rw [←(address k).sum_comp x]
  simp [Block]

theorem address_variance (hd : d≤k) (L : Layout k) (x : Block k → ℝ) :
    variance (dyadicLayout hd L) x=variance (DescentLinearLayouts.layout hd L) (x ∘ address k) := by
  unfold variance
  rw [←(address d).sum_comp]
  simp only [address_load,address_mean]

theorem address_surplus (hd : d≤k) (L : Layout k) (x : Block k → ℝ) :
    surplus (dyadicLayout hd L) x=surplus (DescentLinearLayouts.layout hd L) (x ∘ address k) := by
  unfold surplus
  rw [←(address d).sum_comp (fun j => (load (dyadicLayout hd L) x j)^2),
    ←(address k).sum_comp (fun i => x i^2)]
  simp only [address_load,Function.comp_apply]

theorem address_levelCharge (s : ℕ) (F : ℝ) (hd : d≤k) (L : Layout k) (x : Block k → ℝ) :
    levelCharge s F (dyadicLayout hd L) x=
      levelCharge s F (DescentLinearLayouts.layout hd L) (x ∘ address k) := by
  unfold levelCharge
  split <;> first | exact address_variance hd L x | exact address_surplus hd L x

end
end Hierarchy.DescentColonies

end OAI
