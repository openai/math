import OAI.Hierarchy.DescentIntegerScale
import OAI.Hierarchy.DescentConditionalRow

namespace OAI
/-! # Integer comparisons of the actual conditional Walsh row scores -/

namespace Hierarchy.DescentIntegerScale

open DescentGL
open scoped BigOperators Classical
noncomputable section

variable {h r : ℕ}
local notation "k" => (h+1)+r

/-- Differences contributing to the score after appending a candidate row. -/
def surviving (base : Layout k) (row : Row k) : Finset (Bits k) :=
  Finset.univ.filter fun d => d ≠ 0 ∧ headRows (show h≤k by omega) (base d)=0 ∧ row d=0

theorem conditionalRowScore_eq_score (base : Layout k) (row : Row k) (q : ℕ)
    (W : Fin (r+1) → Bits k → ℕ) :
    conditionalRowScore base (fun j d => (W j d.val : ℝ)/(q:ℝ)^2) row =
      score q r W (surviving base row) := by
  rw [conditionalRowScore, ←DescentRowScore.kernel_score]
  simp only [score,surviving,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d=0
  · simp [hd,conditionalRowAggregate]
  · by_cases old : headRows (show h≤k by omega) (base d)=0
    · by_cases hits : row d=0 <;> simp [hd,old,hits,conditionalRowAggregate]
    · simp [hd,old,conditionalRowAggregate]

theorem conditionalRowScore_eq_integer (base : Layout k) (row : Row k) (q : ℕ)
    (W : Fin (r+1) → Bits k → ℕ) :
    conditionalRowScore base (fun j d => (W j d.val : ℝ)/(q:ℝ)^2) row =
      (rowNumerator r W (surviving base row) : ℝ) / (denominator q r : ℝ) :=
  (conditionalRowScore_eq_score base row q W).trans (score_eq_integer _ _ _ _)

theorem compare_conditionalRows (base : Layout k) (a b : Row k) {q : ℕ} (hq : 0<q)
    (hr : 0<r) (W : Fin (r+1) → Bits k → ℕ) :
    conditionalRowScore base (fun j d => (W j d.val : ℝ)/(q:ℝ)^2) a ≤
      conditionalRowScore base (fun j d => (W j d.val : ℝ)/(q:ℝ)^2) b ↔
    rowNumerator r W (surviving base a) ≤ rowNumerator r W (surviving base b) := by
  rw [conditionalRowScore_eq_score,conditionalRowScore_eq_score]
  exact compare_scores hq hr W _ _

/-- With no residual rows, the joint kernel of a feasible final extension is zero. -/
theorem surviving_last (base T : Layout (h+1))
    (agree : ∀ i : Fin h,rowFunctional T i.castSucc=rowFunctional base i.castSucc) :
    surviving (r:=0) base (rowFunctional T (Fin.last h))=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨ne,old,last⟩ := (Finset.mem_filter.mp hd).2
  apply ne
  apply T.injective
  rw [map_zero]
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simpa using last
  · have eqn := congrArg (fun f : Row (h+1) => f d) (agree l)
    exact (show T d l.castSucc=base d l.castSucc by simpa using eqn).trans (congrFun old l)

end
end Hierarchy.DescentIntegerScale

end OAI
