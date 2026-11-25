import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace OAI
/-! # Counting marked tiles from the normalized squared signed readings -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

private theorem signed_sq (x : ℝ) : (max x 0)^2+(max (-x) 0)^2=x^2 := by
  rcases le_total 0 x with h|h
  · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
  · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]

def signedVector {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k × Bool) :=
  WithLp.toLp 2 fun js => max (if js.2 then x js.1 else -(x js.1)) 0

theorem norm_signedVector {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    ‖signedVector x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simpa [signedVector,Fintype.sum_bool,Real.norm_eq_abs,sq_abs,add_comm] using signed_sq (x j)

/-- A tile whose signed readings have coordinatewise error η has displacement at most
the Euclidean norm of those readings plus sqrt(2k) η. -/
theorem tile_displacement {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin k × Bool))
    {η : ℝ} (hη : 0≤η) (close : ∀ j, |signedVector u j-v j|≤η) :
    ‖u‖ ≤ ‖v‖+Real.sqrt (2*k)*η := by
  have diff : ‖signedVector u-v‖≤Real.sqrt (2*k)*η := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hη)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt (by positivity)]
    have rows (j : Fin k × Bool) : ‖(signedVector u-v) j‖^2≤η^2 := by
      exact (sq_le_sq₀ (abs_nonneg _) hη).2 (close j)
    have sum := Finset.sum_le_sum (s:=Finset.univ) fun j _ => rows j
    simpa [mul_comm,mul_assoc,mul_left_comm] using sum
  rw [←norm_signedVector u]
  have triangle := norm_add_le (signedVector u-v) v
  rw [sub_add_cancel] at triangle
  linarith

/-- The number of tiles exceeding the threshold in at least one signed coordinate.
Here n is the number of tiles, d the number of signed directions and B the cap on one
coordinate's contribution. -/
theorem mark_density {T J : Type*} [Fintype T] [Fintype J] [Nonempty J]
    (charge : T → J → ℝ) {B : ℝ} (cap : ∀ t j, charge t j ≤ B)
    (large : (Fintype.card T:ℝ)≤∑ t, ∑ j, charge t j) :
    let d : ℝ := Fintype.card J
    let mark := Finset.univ.filter fun t => ∃ j, 1/(2*d) ≤ charge t j
    (Fintype.card T:ℝ)/2 ≤ mark.card*(d*B) := by
  classical
  let d : ℝ := Fintype.card J
  let mark := Finset.univ.filter fun t => ∃ j, 1/(2*d) ≤ charge t j
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos (α:=J)
  have row (t : T) : ∑ j, charge t j ≤ 1/2+(if t∈mark then d*B else 0) := by
    by_cases ht : t∈mark
    · rw [ite_eq_left ht]
      have bound := Finset.sum_le_sum (s:=Finset.univ) fun j _ => cap t j
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at bound
      change _ ≤ d*B at bound
      linarith
    · rw [ite_eq_right ht,add_zero]
      have small (j : J) : charge t j < 1/(2*d) := by
        apply lt_of_not_ge
        intro hj
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj⟩)
      have bound := Finset.sum_le_sum (s:=Finset.univ) fun j _ => (small j).le
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at bound
      change _ ≤ d*(1/(2*d)) at bound
      have id : d*(1/(2*d))=1/2 := by field_simp [hd.ne']
      simpa only [id] using bound
  have total := large.trans (Finset.sum_le_sum (s:=Finset.univ) fun t _ => row t)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_mem,
    Finset.univ_inter] at total
  change _ ≤ (mark.card:ℝ)*(d*B)
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
