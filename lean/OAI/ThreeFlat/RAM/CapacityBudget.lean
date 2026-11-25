import OAI.ThreeFlat.RAM.ProgramBits

namespace OAI
/-! # Uniform text capacity at the diagonal trace scale -/

namespace ThreeFlat.RAM.CapacityPadding

/-- The exponential word alphabet holds every operand of the common
u-instruction, u-register, u-public-word interpreter. -/
theorem textFits_scale {u : ℕ} (hu : 128 ≤ u) : TextFits (16*u^10) u u u := by
  have h₁ := Nat.le_self_pow (by decide : 10 ≠ 0) u
  have h₂ : 16*u^10 < 2^(16*u^10) := Nat.lt_two_pow_self
  exact ⟨by omega,by omega,by omega⟩

/-- The padded program and all additional exponentially many advice bits
fit the same diagonal input length as an individually sized program. -/
theorem text_add_advice_fit {u : ℕ} (hu : 128 ≤ u) :
    (1+6*u+u)*(16*u^10)+2^(u^2) ≤ 2^(u^3) := by
  have hu2 : u ≤ 2^u := Nat.lt_two_pow_self.le
  have hc : 16*(1+6*u+u) ≤ u^2 := by
    have h : 128*u ≤ u*u := Nat.mul_le_mul_right u hu
    rw [pow_two]
    omega
  have h12 : 12*u ≤ u^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right u (by omega)
  have bits : (1+6*u+u)*(16*u^10) ≤ 2^(u^2) := calc
    _ = (16*(1+6*u+u))*u^10 := by ac_rfl
    _ ≤ u^2*u^10 := Nat.mul_le_mul_right _ hc
    _ = u^12 := (Nat.pow_add u 2 10).symm
    _ ≤ (2^u)^12 := Nat.pow_le_pow_left hu2 _
    _ = 2^(12*u) := by rw [← Nat.pow_mul,Nat.mul_comm u 12]
    _ ≤ 2^(u^2) := Nat.pow_le_pow_right (by decide) h12
  have h23 : u^2+1 ≤ u^3 := calc
    _ ≤ u^2*2 := by have := Nat.le_self_pow (by decide : 2 ≠ 0) u; omega
    _ ≤ u^2*u := Nat.mul_le_mul_left _ (by omega)
    _ = _ := (pow_succ ..).symm
  calc
    _ ≤ 2^(u^2)+2^(u^2) := Nat.add_le_add_right bits _
    _ = 2^(u^2+1) := by rw [pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) h23

end ThreeFlat.RAM.CapacityPadding

end OAI
