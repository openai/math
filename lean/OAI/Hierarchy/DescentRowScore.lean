import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

namespace OAI
/-! # Scoring and selecting the next binary row for an exceptional-base reset -/

namespace Hierarchy.DescentRowScore

open scoped BigOperators Classical

noncomputable section

/-- The least-index minimizing row implements the fixed tie break. -/
def nextRow {R : Type*} [LinearOrder R] (menu : Finset R) (available : menu.Nonempty)
    (score : R→ℝ) : R :=
  let minima := menu.filter fun r=>∀ v∈menu,score r≤score v
  minima.min' (by obtain ⟨r,hr,best⟩ := menu.exists_min_image score available
                  exact ⟨r,Finset.mem_filter.mpr ⟨hr,best⟩⟩)

theorem nextRow_spec {R : Type*} [LinearOrder R] (menu : Finset R)
    (available : menu.Nonempty) (score : R→ℝ) :
    let r := nextRow menu available score
    r∈menu ∧ (∀ v∈menu,score r≤score v) ∧
      ∀ v∈menu,score v=score r → r≤v := by
  classical
  let mins := menu.filter fun r=>∀ v∈menu,score r≤score v
  have nonempty : mins.Nonempty := by
    obtain ⟨r,hr,best⟩ := menu.exists_min_image score available
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,best⟩⟩
  have winner := Finset.mem_filter.mp (Finset.min'_mem mins nonempty)
  refine ⟨winner.1,winner.2,?_⟩
  intro v hv tie
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hv,fun z hz=>tie.le.trans (winner.2 z hz)⟩

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

/-- One coefficient of the Walsh transform at a binary row. -/
def walsh (row : V→ₗ[ZMod 2] ZMod 2) (w : V→ℝ) : ℝ :=
  ∑ d,(if row d=0 then 1 else -1)*w d

/-- All row scores are recovered as a half-sum of the common total weight
and the row's coefficient of the same Walsh transform. -/
theorem kernel_score (row : V→ₗ[ZMod 2] ZMod 2) (w : V→ℝ) :
    ∑ d ∈ Finset.univ.filter (fun d=>row d=0),w d = ((∑ d,w d) + walsh row w)/2 := by
  rw [Finset.sum_filter,walsh,←Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : row d=0 <;> simp [h]

/-- The off-diagonal coefficient for one specified additive difference. -/
def autocorrelation (x : V→ℝ) (d : V) : ℝ := ∑ i,x i*x (i+d)

omit [Module (ZMod 2) V] in
theorem regroup_collisions {Q : Type*} [AddCommGroup Q] (f : V→+Q) (x : V→ℝ) :
    (∑ i,∑ j,if f i=f j then x i*x j else 0) =
      ∑ d,if f d=0 then autocorrelation x d else 0 := by
  classical
  calc
    _ = ∑ i,∑ d,if f d=0 then x i*x (i+d) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Fintype.sum_equiv (Equiv.addLeft i)
      intro d
      change (if f d=0 then x i*x (i+d) else 0) =
        (if f i=f (i+d) then x i*x (i+d) else 0)
      rw [map_add]
      by_cases h : f d=0 <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : f d=0 <;> simp [h,autocorrelation]


end
end Hierarchy.DescentRowScore

end OAI
