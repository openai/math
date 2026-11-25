import OAI.Hierarchy.DescentBaseVariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI
/-! # The exceptional-base estimators for a single position and level -/

namespace Hierarchy.DescentBaseVariance

open scoped Classical BigOperators

noncomputable section
variable {I P Q : Type*} [Fintype I] [Fintype P] [Fintype Q]
variable [Nonempty P] [Nonempty Q]

/-- Off-diagonal contribution from one bin, before summing over bins. -/
def localSurplus (f : I → Q) (x : I → ℝ) (j : Q) : ℝ :=
  (load f x j)^2 - load f (fun i=>x i^2) j

omit [Nonempty Q] in
theorem sum_localSurplus (f : I → Q) (x : I → ℝ) :
    ∑ j,localSurplus f x j = surplus f x := by
  simp only [localSurplus,surplus,Finset.sum_sub_distrib,sum_load]

omit [Fintype Q] [Nonempty Q] in
theorem localSurplus_nonneg (f : I → Q) (x : I → ℝ) (pos : ∀ i,0≤x i) (j : Q) :
    0 ≤ localSurplus f x j := by
  apply sub_nonneg.mpr
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
    (f:=fun i=>if j=f i then x i else 0) (fun i _=>by split <;> simp [pos])
  simpa [load,ite_pow] using h

omit [Nonempty Q] in
/-- A bin of normalized load greater than two costs at least half its load in
either estimator. Thus the same bound also covers one mark on the bin. -/
theorem overload_cost (f : I → Q) (x : I → ℝ) (j : Q) (pos : ∀ i,0≤x i)
    (small : ∀ i,x i≤1) (avg : mean x Q≤1) (overload : 2<load f x j) :
    load f x j/2 ≤ (load f x j - mean x Q)^2 ∧
    load f x j/2 ≤ localSurplus f x j := by
  have diag : load f (fun i=>x i^2) j ≤ load f x j := by
    apply Finset.sum_le_sum
    intro i _
    split <;> simp_all only [le_refl]
    nlinarith [mul_nonneg (pos i) (sub_nonneg.mpr (small i))]
  have spread : 1≤load f x j - mean x Q := by linarith
  constructor
  · nlinarith [sq_nonneg (load f x j - mean x Q - 1),
      mul_nonneg (sub_nonneg.mpr spread) (sub_nonneg.mpr spread)]
  · unfold localSurplus
    nlinarith [sq_nonneg (load f x j-2)]

/-- The estimator selected in the reset depends on the level but uses the
same candidate layout as every other level. -/
def levelCharge (s : ℕ) (F : ℝ) (f : I → Q) (x : I → ℝ) : ℝ :=
  if 1/F ≤ 1/(2:ℝ)^s then variance f x else surplus f x

omit [Nonempty Q] in
/-- The two charges control all marked bins and their summed mass, including
the level-zero load of bases that already overflow the splitting threshold. -/
theorem marked_bins (s : ℕ) (F : ℝ) (f : I→Q) (x : I→ℝ) (pos : ∀ i,0≤x i)
    (small : ∀ i,x i≤1) (avg : mean x Q≤1) :
    let marked := Finset.univ.filter (fun j=>2<load f x j)
    (marked.card : ℝ) ≤ levelCharge s F f x ∧
      (∑ j ∈ marked,load f x j) ≤ 2*levelCharge s F f x := by
  classical
  let cost (j : Q) := if 1/F≤1/(2:ℝ)^s then (load f x j-mean x Q)^2 else localSurplus f x j
  have nonnegative (j : Q) : 0≤cost j := by
    dsimp [cost]
    split
    · exact sq_nonneg _
    · exact localSurplus_nonneg f x pos j
  have estimate (j : Q) (h : 2<load f x j) : load f x j/2≤cost j := by
    obtain ⟨v,u⟩ := overload_cost f x j pos small avg h
    dsimp [cost]
    split <;> assumption
  have all : (∑ j,cost j)=levelCharge s F f x := by
    by_cases coarse : 1/F≤1/(2:ℝ)^s
    · simp only [cost,levelCharge,ite_eq_left coarse,variance]
    · simp only [cost,levelCharge,ite_eq_right coarse,sum_localSurplus]
  let marked := Finset.univ.filter (fun j=>2<load f x j)
  have sub : (∑ j ∈ marked,cost j) ≤ levelCharge s F f x := by
    rw [←all]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _=>nonnegative j)
  have isMarked {j : Q} (hj : j∈marked) : 2<load f x j :=
    (Finset.mem_filter.mp (show j∈Finset.univ.filter (fun u : Q=>2<load f x u) from hj)).2
  have one (j : Q) (hj : j∈marked) : (1:ℝ)≤cost j := by
    have h := isMarked hj
    linarith [estimate j h]
  have mass (j : Q) (hj : j∈marked) : load f x j≤2*cost j := by
    linarith [estimate j (isMarked hj)]
  constructor
  · refine le_trans ?_ sub
    simpa using Finset.sum_le_sum one
  · have total := Finset.sum_le_sum mass
    rw [←Finset.mul_sum] at total
    exact total.trans (mul_le_mul_of_nonneg_left sub (by norm_num))

theorem level_average (s : ℕ) (layout : P → I → Q) (pairs : PairBound layout)
    (x : I → ℝ) {n F : ℝ} (hn : 0<n) (hF : 0<F)
    (bins : (Fintype.card Q:ℝ)=n*2^s)
    (pos : ∀ i,0≤x i) (small : ∀ i,x i≤1/F) (mass : ∑ i,x i≤n) :
    average (fun p=>levelCharge s F (layout p) x) ≤ n * min (1/F) (1/(2:ℝ)^s) := by
  have total : 0≤∑ i,x i := Finset.sum_nonneg fun i _ => pos i
  have positive : 0<(2:ℝ)^s := by positivity
  obtain ⟨boundedV,boundedU⟩ := average_deviations layout pairs x pos
  by_cases coarse : 1/F≤1/(2:ℝ)^s
  · simp only [levelCharge,ite_eq_left coarse,min_eq_left coarse]
    calc
      _ ≤ _ := boundedV
      _ ≤ _ := sum_squares_le x pos small
      _ ≤ (1/F)*n := mul_le_mul_of_nonneg_left mass (by positivity)
      _ = _ := mul_comm _ _
  · simp only [levelCharge,ite_eq_right coarse,min_eq_right (le_of_not_ge coarse)]
    apply boundedU.trans
    rw [bins]
    apply (div_le_iff₀ (mul_pos hn positive)).mpr
    have squares : (∑ i,x i)^2 ≤ n^2 := by gcongr
    calc
      _ ≤ _ := squares
      _ = _ := by field_simp

omit [Nonempty Q] in
/-- All capacity overflows on a neighbor pair are charged against its actual
normalized core-load vector. -/
theorem capacity_marks (f : I→Q) (x : I→ℝ) (K : ℝ) (hK : 0<K) :
    (((Finset.univ.filter (fun j=>mean x Q + 1/K < load f x j)).card):ℝ) ≤
      K^2*variance f x := by
  let marked := Finset.univ.filter (fun j=>mean x Q + 1/K < load f x j)
  calc
    (marked.card:ℝ) = ∑ j ∈ marked,(1:ℝ) := by simp
    _ ≤ ∑ j ∈ marked,K^2*(load f x j-mean x Q)^2 := Finset.sum_le_sum
      fun j hj=>overflow_charge hK (Finset.mem_filter.mp hj).2
    _ ≤ ∑ j,K^2*(load f x j-mean x Q)^2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _=>mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by simp [variance,Finset.mul_sum]

end
end Hierarchy.DescentBaseVariance

end OAI
