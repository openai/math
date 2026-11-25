import OAI.Hierarchy.DescentBaseOverload
import OAI.Hierarchy.DescentDyadicMixing

namespace OAI
/-! # The simultaneous exceptional-base budget over positions -/

namespace Hierarchy.DescentBaseVariance

open scoped BigOperators Classical

noncomputable section
variable {I P A : Type*} [Fintype I] [Fintype P] [Nonempty P] [Fintype A]

theorem total_level_budget (levels : A→ℕ) (bins : (a:A)→Fin (levels a)→Type*)
    [∀ a s,Fintype (bins a s)] [∀ a s,Nonempty (bins a s)]
    (layout : ∀ a s,P→I→bins a s) (pairs : ∀ a s,PairBound (layout a s))
    (x : A→I→ℝ) (n : A→ℝ) (k : ℕ) (r : ℝ) (hr : 1<r) (hlt : r<2) (h8 : r^8=2)
    (hn : ∀ a,0<n a) (count : ∀ a (s:Fin (levels a)),(Fintype.card (bins a s):ℝ)=n a*2^s.val)
    (pos : ∀ a i,0≤x a i) (small : ∀ a i,x a i≤1/(2:ℝ)^k)
    (mass : ∀ a,∑ i,x a i≤n a) :
    average (fun p=>∑ a,∑ s : Fin (levels a),
      4*(2:ℝ)^((s.val+7)/8)*levelCharge s.val (2^k) (layout a s p) (x a)) ≤
      (∑ a,n a) * (8*(r/2)^k*(1/(r-1) + 1/(1-r/2))) := by
  simp_rw [average_sum,average_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  let part (s : ℕ) := min (1/(2:ℝ)^k) (1/(2:ℝ)^s)
  have step (s : Fin (levels a)) :
      4*(2:ℝ)^((s.val+7)/8)*average (fun p=>levelCharge s.val (2^k) (layout a s p) (x a)) ≤
        (8*n a)*(r^s.val*part s.val) := by
    have ev := level_average (F:=(2:ℝ)^k) s.val (layout a s) (pairs a s) (x a) (hn a) (by positivity)
      (count a s) (pos a) (small a) (mass a)
    have nr : 0≤n a*part s.val := mul_nonneg (hn a).le (le_min (by positivity) (by positivity))
    calc
      _ ≤ 4*(2:ℝ)^((s.val+7)/8)*(n a*part s.val) :=
        mul_le_mul_of_nonneg_left ev (by positivity)
      _ ≤ (4*(2*r^s.val))*(n a*part s.val) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ceil_weight r hr.le h8 s.val) (by norm_num)) nr
      _ = _ := by ring
  calc
    _ ≤ ∑ s : Fin (levels a),(8*n a)*(r^s.val*part s.val) := Finset.sum_le_sum fun s _=>step s
    _ = (8*n a)*(∑ s ∈ Finset.range (levels a),r^s*part s) := by
      rw [←Finset.mul_sum,Fin.sum_univ_eq_sum_range (fun s : ℕ => r^s * part s) (levels a)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_level_sum r hr hlt k (levels a)) (mul_nonneg (by norm_num : (0:ℝ)≤8) (hn a).le)
    _ = _ := by ring

theorem choose_combined_layout (base capacity : P→ℝ) {L U : ℝ} (hL : average base≤L)
    (hU : average capacity≤U) : ∃ p,base p + capacity p ≤ L+U := by
  obtain ⟨p,hp⟩ := exists_layout_le_average (fun p=>base p + capacity p)
  refine ⟨p,hp.trans ?_⟩
  unfold average at *
  rw [Finset.sum_add_distrib,add_div]
  exact add_le_add hL hU

end
end Hierarchy.DescentBaseVariance

end OAI
