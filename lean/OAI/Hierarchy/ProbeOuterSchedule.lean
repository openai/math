import OAI.Hierarchy.ProbeStopping

namespace OAI
/-! # The finite outer repair loop with conservative completion -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- Once the signed account has saved the whole crude remaining cost, every
later mesh increment runs directly and fulfills the original scheduled demands. -/
def outerRun {X : Type*} (repairStep : ℕ → ℕ → X → X) (good : ℕ → X → Bool)
    (price : ℕ → X → ℝ) (floor : ℝ) (fuel : ℕ) (move : ℕ → X → X) (start : X) :
    ℕ → X × Bool
  | 0 => (start,false)
  | j+1 =>
    let prev := outerRun repairStep good price floor fuel move start j
    if prev.2 then (move j prev.1,true)
    else
      let y := repair (repairStep j) (good j) (price j) floor prev.1 fuel
      (move j y, decide (price j y≤floor))

/-- One uniform finite repair fuel suffices for every admissible history.
The fallback pays using the previously saved signed balance, even if that
balance is arbitrarily negative. -/
theorem outer_run_paid {X : Type*} (repairStep : ℕ → ℕ → X → X)
    (good : ℕ → X → Bool) (price : ℕ → X → ℝ) (move : ℕ → X → X) (start : X)
    (total fuel : ℕ) (allow crude : ℕ → ℝ) {upper fallback goodCost crudeCost gain : ℝ}
    (hg : 0<gain) (nonnegA : ∀ j<total,0≤allow j) (nonnegC : ∀ j<total,0≤crude j)
    (regularBudget : (∑ j ∈ Finset.range total,allow j) ≤ goodCost)
    (crudeBudget : (∑ j ∈ Finset.range total,crude j) ≤ crudeCost)
    (enough : price 0 start+goodCost≤upper) (floor : fallback+crudeCost≤upper)
    (fuelBound : upper-(fuel:ℝ)*gain≤fallback)
    (save : ∀ j<total, ∀ h<fuel, ∀ x, good j x=false → fallback<price j x →
      price j (repairStep j h x)+gain≤price j x)
    (regular : ∀ j<total, ∀ x, good j x=true → price (j+1) (move j x)≤price j x+allow j)
    (general : ∀ j<total, ∀ x, price (j+1) (move j x)≤price j x+crude j) :
    price total (outerRun repairStep good price fallback fuel move start total).1≤upper := by
  let run := outerRun repairStep good price fallback fuel move start
  let sum (a : ℕ → ℝ) (m : ℕ) := ∑ j ∈ Finset.range m, a j
  have mono (a : ℕ→ℝ) (nn : ∀ j<total,0≤a j) (m : ℕ) (hm : m≤total) :
      sum a m≤sum a total := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      (fun j h _=>nn j (Finset.mem_range.mp h))
  have inv (m : ℕ) (hm : m≤total) :
      price m (run m).1 ≤ if (run m).2 then fallback+sum crude m else price 0 start+sum allow m := by
    induction m with
    | zero => simp [run,outerRun,sum]
    | succ m ih =>
      have lt : m<total := by omega
      have old := ih (by omega)
      let x := (run m).1
      have aBound := (mono allow nonnegA m lt.le).trans regularBudget
      have cNon : 0≤sum crude m :=
        Finset.sum_nonneg (fun j h=>nonnegC j ((Finset.mem_range.mp h).trans lt))
      have aNext : sum allow (m+1)=sum allow m+allow m := Finset.sum_range_succ ..
      have cNext : sum crude (m+1)=sum crude m+crude m := Finset.sum_range_succ ..
      by_cases done : (run m).2=true
      · have prev : price m x≤fallback+sum crude m := by simpa [x,done] using old
        have next : run (m+1)=(move m x,true) := by simp [run,outerRun,x] at done ⊢; simp_all
        rw [next]; simp only [ite_true,cNext]
        linarith [general m lt x]
      · have prev : price m x≤price 0 start+sum allow m := by simpa [x,done] using old
        let y := repair (repairStep m) (good m) (price m) fallback x fuel
        have yExists := repair_receipt (repairStep m) (good m) (price m) fallback gain hg x fuel
          (by linarith) (save m lt)
        change price m y≤price m x ∧ (good m y=true ∨ price m y≤fallback) at yExists
        have next : run (m+1)=(move m y,decide (price m y≤fallback)) := by
          simp only [run,outerRun,done,Bool.false_eq_true,ite_false,x,y]
        rw [next]
        by_cases saved : price m y≤fallback
        · simp only [saved,decide_true,ite_true,cNext]
          linarith [general m lt y]
        · have ok := yExists.2.resolve_right saved
          simp only [saved,decide_false,Bool.false_eq_true,ite_false,aNext]
          linarith [regular m lt y ok,yExists.1]
  have final := inv total le_rfl
  by_cases done : (run total).2=true <;> simp [done] at final <;>
    linarith [show sum crude total≤crudeCost from crudeBudget,
      show sum allow total≤goodCost from regularBudget]

end
end Hierarchy.AdaptiveProbe

end OAI
