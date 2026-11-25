import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open scoped BigOperators Real
open Complex

/-- Angles measured in whole turns (positive sign). -/
noncomputable def cis (r : ℝ) : ℂ :=
  Complex.exp (↑(r*(2*π)) * I)

/-- Cyclic characters of integer order n. -/
noncomputable def phase (n : ℕ) (i : ℤ) : ℂ :=
  cis ((i : ℝ)/n)

theorem cis_add (a b : ℝ) : cis (a+b)=cis a*cis b := by
  rw [cis,add_mul, ofReal_add,add_mul,exp_add]
  rfl

@[simp] theorem cis_int (a : ℤ) : cis (a : ℝ)=1 := by
  unfold cis
  push_cast
  rw [mul_assoc]
  exact exp_int_mul_two_pi_mul_I a

@[simp] theorem cis_zero : cis 0=1 := by simp [cis]
@[simp] theorem cis_one : cis 1=1 := by simpa using cis_int 1

theorem cis_neg (a : ℝ) : cis (-a)=(cis a)⁻¹ := by simp [cis, exp_neg]

theorem cis_sub (a b : ℝ) : cis (a-b)=cis a/cis b := by rw [sub_eq_add_neg,cis_add,cis_neg,div_eq_mul_inv]

@[simp] theorem cis_norm (a : ℝ) : ‖cis a‖=1 := by
  simp [cis, norm_exp]

theorem cos_cis (a : ℝ) :
    ((Real.cos (π*a) : ℝ) : ℂ) = (cis (a/2)+cis (-a/2))/2 := by
  unfold cis
  have h : a/2*(2*π) = π*a := by ring
  have g : -a/2*(2*π) = -(π*a) := by ring
  rw [h,g,ofReal_neg,exp_mul_I,exp_mul_I,cos_neg,sin_neg, ofReal_cos]
  ring

theorem cis_pow (a : ℝ) (i : ℕ) : (cis a)^i = cis (i*a) := by
  induction i with
  | zero => simp
  | succ i hi => rw [pow_succ,Nat.cast_add_one,add_mul,cis_add,one_mul,hi]

theorem phase_add (n) (i j : ℤ) :
    phase n (i+j)=phase n i*phase n j := by rw [phase, Int.cast_add, add_div,cis_add]; rfl

theorem phase_sub (n) (i j : ℤ) :
    phase n (i-j)=phase n i/phase n j := by rw [phase, Int.cast_sub,sub_div,cis_sub]; rfl

theorem phase_neg (n) (i : ℤ) : phase n (-i)=(phase n i)⁻¹ := by rw [phase, Int.cast_neg,neg_div,cis_neg]; rfl

@[simp] theorem phase_norm (n) (i : ℤ) : ‖phase n i‖=1 := cis_norm _

@[simp] theorem phase_divides (n : ℕ) [NeZero n] (k : ℤ) : phase n (k*n)=1 := by
  have h : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [phase,h]

theorem phase_eq_one (n : ℕ) [NeZero n] (i : ℤ) :
    phase n i=1 ↔ (n:ℤ)∣i := by
  have h : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  constructor
  · intro e
    obtain ⟨k,hk⟩ := exp_eq_one_iff.mp e
    use k
    unfold phase cis at * -- hk doesn't mention phase? e
    push_cast at hk
    rw [mul_assoc, mul_left_inj' two_pi_I_ne_zero] at hk
    field_simp at hk
    exact_mod_cast hk
  · intro hh
    obtain ⟨x,rfl'⟩ := hh
    rw [rfl', mul_comm]
    exact phase_divides n x

theorem phase_inj (n : ℕ) [NeZero n] (i j : ℤ) :
    phase n i=phase n j ↔ (n:ℤ)∣(i-j) := by
  rw [← phase_eq_one, phase_sub]
  refine (div_eq_one_iff_eq ?_).symm
  exact exp_ne_zero _

theorem phase_pow (n : ℕ) (i : ℤ) (j : ℕ) :
    phase n i ^ j = phase n (i*j) := by
  rw [phase,cis_pow,phase,Int.cast_mul,Int.cast_natCast]
  congr 1
  ring

/-- Character cancellation, with integer condition. -/
theorem sum_phase (n : ℕ) [NeZero n] (i : ℤ) :
    ∑ k : Fin n, phase n (i*(k.val : ℕ)) = if (n:ℤ)∣i then ↑n else 0 := by
  split
  · next h =>
    obtain ⟨x,h⟩ := h
    have e (k : Fin n) : phase n (i*(k.val : ℕ))=1 := by
      rw [phase_eq_one, h, mul_assoc]
      exact dvd_mul_right _ _
    simp [e]
  · next h =>
    simp_rw [← phase_pow, Fin.sum_univ_eq_sum_range (fun k => phase n i ^ k)]
    refine (mul_right_injective₀ (show phase n i-1≠0 from sub_ne_zero.mpr (by simpa [phase_eq_one] using h))) ?_
    beta_reduce
    rw [mul_comm (phase n i - 1), geom_sum_mul, phase_pow, phase_divides, mul_zero, sub_self]

end Fourier

end IntegerMultiplication
end Computability
end OAI
