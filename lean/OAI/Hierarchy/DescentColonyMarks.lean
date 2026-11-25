import OAI.Hierarchy.DescentBaseOverload

namespace OAI
/-! # Bounding initial colony marks by off-diagonal mass -/

namespace Hierarchy.DescentColonies
open DescentBaseVariance
open scoped BigOperators Classical
noncomputable section

variable {I Q P : Type*} [Fintype I] [Fintype Q] [Fintype P] [Nonempty Q] [Nonempty P]

def markedBins (f : I → Q) (x : I → ℝ) := Finset.univ.filter fun j => 1 < load f x j

omit [Nonempty Q] in
/-- With individual mass at most one half, an overloaded interval has at
least one half of a unit of colliding ordered cross-products. -/
theorem initial_marks (f : I → Q) (x : I → ℝ) (nonneg : ∀i,0≤x i) (small : ∀i,x i≤1/2) :
    ((markedBins f x).card : ℝ) ≤ 2*surplus f x := by
  have smallSquares (j : Q) : load f (fun i => x i^2) j ≤ (1/2)*load f x j := by
    simp only [load,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hit : j=f i
    · simp only [ite_eq_left hit]
      nlinarith [mul_nonneg (nonneg i) (sub_nonneg.mpr (small i))]
    · simp [hit]
  have localBound (j : Q) : (if 1<load f x j then (1:ℝ) else 0)≤2*localSurplus f x j := by
    split <;> rename_i test
    · unfold localSurplus
      nlinarith [smallSquares j,mul_nonneg (sub_nonneg.mpr test.le) (show 0 ≤ load f x j + 1/2 by linarith)]
    · linarith [localSurplus_nonneg f x nonneg j]
  rw [←sum_localSurplus,Finset.mul_sum]
  convert Finset.sum_le_sum (s:=Finset.univ) (fun j _ => localBound j) using 1
  simp [markedBins]

private theorem mean_le {f g : P → ℝ} (h : ∀a,f a≤g a) : average f≤average g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

theorem expected_initial_marks (layouts : P → I → Q) (pairs : PairBound layouts)
    (x : I → ℝ) (nonneg : ∀i,0≤x i) (small : ∀i,x i≤1/2) :
    average (fun p => ((markedBins (layouts p) x).card:ℝ)) ≤ 2*(∑i,x i)^2/Fintype.card Q := by
  have expected := (average_deviations layouts pairs x nonneg).2
  calc
    _ ≤ average (fun p => 2*surplus (layouts p) x) := mean_le fun p => initial_marks (layouts p) x nonneg small
    _ = 2*average (fun p => surplus (layouts p) x) := by
      unfold average
      rw [←Finset.mul_sum]
      ring
    _ ≤ _ := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left expected (by norm_num : (0:ℝ)≤2)

/-- Either the absolute count of target prefixes or the weighted source
collision estimate can cap the same term. Selecting the smaller bound uses
only layout-independent expected values. -/
theorem ancestor_expectation (K : ℝ) (layouts : P → I → Q) (pairs : PairBound layouts)
    (x : I → ℝ) (nonneg : ∀i,0≤x i) (small : ∀i,x i≤1/2) :
    average (fun p => min K ((markedBins (layouts p) x).card:ℝ)) ≤
      min K (2*(∑i,x i)^2/Fintype.card Q) := by
  exact le_min ((mean_le (fun _ => min_le_left _ _)).trans_eq (average_const K))
    ((mean_le (fun _ => min_le_right _ _)).trans (expected_initial_marks layouts pairs x nonneg small))

end
end Hierarchy.DescentColonies

end OAI
