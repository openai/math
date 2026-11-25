import OAI.LinearAlgebra.SpectralBooks.Dimension
import OAI.ThreeFlat.ProfileTail
import OAI.ThreeFlat.StudentTail

namespace OAI
/-! # The dimension-three Student test in load coordinates -/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks

/-- With three degrees of freedom, the Student tail at the threshold for a
positive load is exactly the trigonometric profile of the load ratio. -/
theorem studentTail_three_load {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    studentTail 3 (Real.sqrt (3 * (L / m - 1))) = profile (m / L) := by
  have hL : 0 < L := hm.trans_le hmL
  have hr := profile_eq_atan_tail (div_pos hm hL) ((div_le_one hL).mpr hmL)
  rw [show 1 / (m / L) = L / m by field_simp] at hr
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), studentTail_three_scaled, hr]

/-- Finite rectangular Student tests in dimension three, expressed directly in
the paper's trigonometric profile. A vanishing load contributes zero. -/
theorem studentBound_three_iff {m : Fin 3 → ℝ} {L : ℝ} (hm : ∀ i, 0 ≤ m i)
    (hmL : ∀ i, m i ≤ L) :
    StudentBound 3 m L ↔ ∑ i, profile (m i / L) ≤ 1 := by
  classical
  have hterm (i : Fin 3) :
      (if 0 < m i then studentTail 3 (Real.sqrt (3 * (L / m i - 1))) else 0) =
        profile (m i / L) := by
    by_cases hi : 0 < m i
    · simpa only [hi, ite_true] using studentTail_three_load hi (hmL i)
    · have hzero : m i = 0 := (not_lt.mp hi).antisymm (hm i)
      simp [hzero, profile_zero]
  simp only [StudentBound, Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num,
    div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, Finset.sum_filter, hterm]

/-- Three equal positive loads each consume at most one third of the unit
allowance for the dimension-three Student test. -/
theorem profile_le_oneThird_of_studentBound {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    (h : StudentBound 3 (fun _ => m) L) : profile (m / L) ≤ 1 / 3 := by
  have hp := (studentBound_three_iff (fun _ ↦ hm.le) (fun _ ↦ hmL)).mp h
  simp only [Fin.sum_univ_three] at hp
  linarith

end ThreeFlat

end OAI
