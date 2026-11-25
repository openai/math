import OAI.Computability.IntegerMultiplication.Fourier.Index
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Sum

/-!
# A window with finite Fourier expansion
-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open scoped BigOperators Real
open Finset Complex

noncomputable def rad (D : ℕ) : Finset ℤ :=
  Icc (-(D:ℤ)) D

@[simp]
theorem mem_rad {i : ℤ} {D : ℕ} : i ∈ rad D ↔ -(D : ℤ) ≤ i ∧ i ≤ (D : ℤ) := mem_Icc

def offset (D r : ℕ) : ℤ := (r : ℤ)-D
def unoff (D : ℕ) (r : ℤ) : ℕ := (r+(D:ℤ)).toNat

theorem unoff_offset (D r : ℕ) : unoff D (offset D r)=r := by simp [offset,unoff]

theorem sum_offset {X : Type*} [AddCommMonoid X] (f : ℤ → X) (D : ℕ) :
    (∑ i ∈ range (2*D+1), f (offset D i)) = ∑ i ∈ rad D, f i :=
  Finset.sum_bij' (fun i _ => offset D i) (fun i _ => unoff D i)
    (by simp [offset]; omega)
    (by simp [unoff]; omega)
    (fun i _ => unoff_offset D i)
    (by simp [offset,unoff]; omega)
    (by simp)

noncomputable def coef (D : ℕ) (r : ℤ) : ℝ :=
  if r∈rad D then
    ((Nat.choose (2*D) (unoff D r) : ℕ) : ℝ)/4^D
  else 0

noncomputable def window (D n : ℕ) (i : ℤ) : ℝ :=
  (Real.cos (π*((i:ℝ)/n)))^(2*D)

theorem pow_two_D (D : ℕ) : (2 : ℂ)^(2*D)=(4:ℂ)^D := by rw [pow_mul]; norm_num

private theorem twoD_sub (r D : ℕ) (h : r∈range (2*D+1)) :
    ((2*D-r:ℕ):ℝ) = 2*(D:ℝ)-r := by rw [Nat.cast_sub (by simp at h; omega)]; push_cast; rfl

theorem window_phase (D n : ℕ) (i : ℤ) :
    (window D n i : ℂ) = ∑ r ∈ rad D, (coef D r : ℂ) * phase n (r*i) := by
  unfold window
  push_cast
  -- target Complex.cos rather than coerced?
  have he := cos_cis ((i:ℝ)/n)
  push_cast at he
  rw [he,div_pow,add_pow,← sum_offset (fun r => (coef D r : ℂ)*phase n (r*i))]
  simp only [pow_two_D,div_eq_mul_inv, sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hm : offset D r ∈ rad D := by simp [offset]; simp at hr; omega
  rw [mul_assoc (cis _ ^ r)] -- actually regroup want mul then cis
  rw [cis_pow,cis_pow, coef,ite_eq_left hm,unoff_offset]
  push_cast
  rw [← mul_assoc, ← cis_add]
  have ha : phase n (offset D r * i) =
    cis ((r:ℝ)*((i:ℝ)/(n:ℝ)/2)+ ((2*D-r:ℕ):ℝ)*(-((i:ℝ)/n)/2)) := by
    unfold phase
    congr 1
    rw [twoD_sub _ _ hr]
    simp only [Int.cast_mul, offset, Int.cast_sub, Int.cast_natCast]
    ring
  rw [ha]
  ring_nf

theorem window_abs_le (D n : ℕ) (i : ℤ) :
    |window D n i| ≤ 1 := by
  rw [window, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

end Fourier

end IntegerMultiplication
end Computability
end OAI
