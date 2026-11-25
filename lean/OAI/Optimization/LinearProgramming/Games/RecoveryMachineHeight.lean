import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.Games.Recovery
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace RecoveryMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Size used while the machine walks down and back up a continued fraction. -/
def height (q : ℚ) : ℕ := max q.num.natAbs q.den

def width (q : ℚ) : ℕ := (height q).size

theorem int_length (z : ℤ) : (intCode z).length = z.natAbs.size + 3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

theorem rat_length (q : ℚ) : (ratCode q).length = 2*q.num.natAbs.size + q.den.size + 7 := by
  simp only [ratCode, prodCode, pairBits_length, int_length, ← Nat.size_eq_bits_len]
  omega

theorem width_le_length (q : ℚ) : width q ≤ (ratCode q).length := by
  rw [rat_length]
  rcases le_total q.num.natAbs q.den with h | h <;> simp only [width,height,max_eq_right h,max_eq_left h] <;> omega

theorem length_le_width (q : ℚ) : (ratCode q).length ≤ 3*width q + 7 := by
  rw [rat_length]
  have hn := Nat.size_le_size (le_max_left q.num.natAbs q.den)
  have hd := Nat.size_le_size (le_max_right q.num.natAbs q.den)
  unfold width height
  omega

theorem height_inv (q : ℚ) : height q⁻¹ = height q := by
  by_cases h : q.num = 0
  · rw [Rat.zero_of_num_zero h,inv_zero]
  · simp [height,Rat.den_inv,h,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero h,max_comm]

/-- The fractional tail never grows in height, even on a negative or integral argument. -/
theorem tail_height (q : ℚ) : height (Int.fract q)⁻¹ ≤ height q := by
  rw [height_inv]
  apply (show height (Int.fract q) ≤ q.den from ?_).trans (le_max_right _ _)
  rw [height, Rat.den_intFract]
  apply max_le _ le_rfl
  let f := Int.fract q
  have hf : 0 ≤ f := Int.fract_nonneg q
  have hn : 0 ≤ f.num := Rat.num_nonneg.mpr hf
  have ha : (f.num.natAbs : ℤ) = f.num := (Int.eq_natAbs_of_nonneg hn).symm
  have hden : f.den = q.den := Rat.den_intFract q
  have hfrac : (f.num.natAbs : ℚ)/q.den = f := by
    rw [← hden, ← Int.cast_natCast,ha,Rat.num_div_den]
  have hh := Int.fract_lt_one q
  have h : f.num.natAbs < q.den := by
    have h' : (f.num.natAbs:ℚ)/q.den < 1 := hfrac.trans_lt hh
    exact_mod_cast (div_lt_one (by exact_mod_cast q.den_pos)).mp h'
  exact h.le

theorem floor_size (q : ℚ) : (⌊q⌋ : ℤ).natAbs.size ≤ width q := by
  apply Nat.size_le_size
  rw [Rat.floor_def']
  exact (Int.natAbs_ediv_le_natAbs _ _).trans (le_max_left _ _)

/-- A continued-fraction digit increases the binary width by at most its own binary size.
This bound holds for arbitrary signed digits and arbitrary accumulators. -/
theorem cons_width (a : ℤ) (q : ℚ) : width ((a : ℚ) + q⁻¹) ≤ a.natAbs.size + width q := by
  have hmax (y : ℚ) : height ((a:ℚ)+y) ≤ (a.natAbs+1)*height y := by
    have hden : y.den ≤ height y := le_max_right _ _
    have hnum : y.num.natAbs ≤ height y := le_max_left _ _
    apply max_le
    · rw [Rat.num_add]
      apply (Int.natAbs_ediv_le_natAbs _ _).trans
      apply (Int.natAbs_add_le _ _).trans
      simp only [Rat.num_intCast,Rat.den_intCast,Int.natAbs_mul,Int.natAbs_natCast,mul_one]
      nlinarith [Nat.mul_le_mul_left a.natAbs hden]
    · rw [Rat.intCast_add_den]
      exact hden.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (height y) (show 1 ≤ a.natAbs+1 by omega))
  apply Nat.size_le.mpr
  refine (hmax q⁻¹).trans_lt ?_
  rw [height_inv,pow_add]
  apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Nat.lt_size_self a.natAbs)))
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self (height q)) (by positivity)

theorem fold_width (xs : List ℤ) (q : ℚ) :
    width (xs.foldl (fun (acc : ℚ) (a : ℤ) => (a : ℚ)+acc⁻¹) q) ≤ width q + (listCode intCode xs).length := by
  induction xs generalizing q with
  | nil => simp [listCode]
  | cons a xs ih =>
    simp only [List.foldl_cons,listCode_length_cons,int_length]
    have h := ih ((a:ℚ)+q⁻¹)
    have h' := cons_width a q
    omega

end RecoveryMachine
end Games
end LinearProgramming
end Optimization
end OAI
