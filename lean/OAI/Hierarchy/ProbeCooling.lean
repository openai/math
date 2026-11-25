import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI
/-! # Uniform cooling allowance on arbitrary finite rational time meshes -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

private def primitive (r t : ℝ) := Real.log (max r t/r)+min t r/r

private theorem step_log {s t : ℝ} (ht : 0<t) (hs : 0 < s) :
    (s-t)/s ≤ Real.log s-Real.log t := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
  rw [Real.log_div ht.ne' hs.ne'] at h
  rw [sub_div,div_self hs.ne']
  linarith

/-- On one downward time step, the right-endpoint charge is at most the decrease
of a scalar antiderivative. This also covers steps crossing the truncation time r. -/
private theorem band {r s t : ℝ} (hr : 0<r) (ht : 0<t) (dec : t≤s) :
    (s-t)*min (1/s) (1/r)≤primitive r s-primitive r t := by
  have hs := ht.trans_le dec
  rcases le_total s r with low|high
  · have low' := dec.trans low
    have rate := one_div_le_one_div_of_le hs low
    simp only [min_eq_right rate,primitive,max_eq_left low,max_eq_left low',min_eq_left low,
      min_eq_left low',div_self hr.ne',Real.log_one,zero_add]
    ring_nf
    exact le_rfl
  · have rate := one_div_le_one_div_of_le hr high
    rw [min_eq_left rate]
    rcases le_total r t with high'|low'
    · rw [primitive,primitive,max_eq_right high,max_eq_right high',min_eq_right high,min_eq_right high',
        div_self hr.ne',Real.log_div hs.ne' hr.ne',Real.log_div ht.ne' hr.ne']
      linarith [step_log ht hs,show (s-t)*(1/s)=(s-t)/s by ring]
    · rw [primitive,primitive,max_eq_right high,max_eq_left low',min_eq_right high,min_eq_left low',
        div_self hr.ne',Real.log_one,zero_add,Real.log_div hs.ne' hr.ne']
      have first := step_log hr hs
      have next := mul_le_mul_of_nonneg_left rate (sub_nonneg.mpr low')
      have split : (s-t)*(1/s)=(s-r)/s+(r-t)*(1/s) := by ring
      have last : (r-t)*(1/r)=1-t/r := by rw [mul_one_div,sub_div,div_self hr.ne']
      linarith

/-- No limiting mesh is required for the time charge. The same estimate holds
when local repairs or probe feedback are executed between any consecutive steps. -/
theorem cooling_allowance {r : ℝ} (hr : 0<r) (bounded : r≤1)
    (s : ℕ → ℝ) (m : ℕ) (start : s 0=1) (pos : ∀ j ≤ m,0 < s j)
    (dec : ∀ j < m,s (j+1)≤s j) :
    ∑ j ∈ Finset.range m, (s j-s (j+1))*min (1/s j) (1/r) ≤ 1-Real.log r := by
  have use (i : ℕ) (hi : i ≤ m) :
      (∑ j ∈ Finset.range i, (s j-s (j+1))*min (1/s j) (1/r))+primitive r (s i)≤primitive r (s 0) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.sum_range_succ]
      linarith [ih (by omega),band hr (pos (i+1) hi) (dec i (by omega))]
  have first : primitive r (s 0)=1-Real.log r := by
    simp [primitive,start,max_eq_right bounded,min_eq_right bounded,hr.ne']
    ring
  have lower : 0≤primitive r (s m) := by
    apply add_nonneg
    · exact Real.log_nonneg ((le_div_iff₀ hr).mpr (by simp))
    · exact div_nonneg (le_min (pos m le_rfl).le hr.le) hr.le
  linarith [use m le_rfl]

end
end Hierarchy.AdaptiveProbe

end OAI
