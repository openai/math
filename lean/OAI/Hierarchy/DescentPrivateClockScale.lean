import OAI.Hierarchy.DescentCompilerSlack
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Word exponents for the actual logarithmic epoch choice -/

namespace Hierarchy.DescentCompiler
noncomputable section

/-- A quadratic polynomial in the epoch age fits inside the input bit height when
the age is the integer half-logarithmic one used for the ROM. -/
theorem private_age_square (h B : ℕ) (hh : 0<h) (hB : 0<B) :
    let J:=Nat.log 2 h/(2*B)
    (J+1)^2≤h := by
  let J:=Nat.log 2 h/(2*B)
  have len : J*(2*B)≤Nat.log 2 h := Nat.div_mul_le_self _ _
  have twice : J*2≤J*(2*B) := Nat.mul_le_mul_left _ (by omega)
  calc
    _ ≤ (2^J)^2 := Nat.pow_le_pow_left Nat.lt_two_pow_self 2
    _ = 2^(J*2) := (pow_mul ..).symm
    _ ≤ _ := (Nat.le_log_iff_pow_le (by decide) hh.ne').mp (twice.trans len)

def privateGroupRate (t c e f : ℕ) := (1+(c+e)*(t+1)+8+f)*(t+1)

/-- The actual copies occupy only a linear number of address bits at the common
input scale, although their public radix itself increases with the age. -/
theorem private_copy_bits (t J c e f tail h : ℕ) (hh : 0<h) (age : (J+1)^2≤h) :
    tail+groupBits t J c e f*((t+1)*J+1)≤(tail+privateGroupRate t c e f)*h := by
  let K:=1+(c+e)*(t+1)+8+f
  have k : groupBits t J c e f≤K*(J+1) := groupBits_linear ..
  have l : (t+1)*J+1≤(t+1)*(J+1) := by rw [Nat.mul_succ];omega
  have scaled : groupBits t J c e f*((t+1)*J+1)≤(K*(t+1))*h := calc
    _ ≤ (K*(J+1))*((t+1)*(J+1)) := Nat.mul_le_mul k l
    _ = (K*(t+1))*(J+1)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ age
  rw [Nat.add_mul tail (privateGroupRate t c e f) h]
  exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hh) scaled

/-- The public counter fits an explicit sum of bit lengths. The exponent is valid
even for a zero population or a zero rate. -/
theorem private_volume_fits (volume rate : ℕ) :
    rate*volume^3<2^((Nat.log 2 rate+1)+3*(Nat.log 2 volume+1)) := by
  have r := Nat.lt_pow_succ_log_self (by decide : 1<2) rate
  have v := Nat.lt_pow_succ_log_self (by decide : 1<2) volume
  rw [pow_add,Nat.mul_comm 3, pow_mul]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left v.le 3)).trans_lt (Nat.mul_lt_mul_of_pos_right r (by positivity))

end
end Hierarchy.DescentCompiler

end OAI
