import OAI.ThreeFlat.Diagonal.TraceVolumeArithmetic

namespace OAI
/-! # Address space and running time of preparation inside the diagonal volume -/

namespace ThreeFlat.Diagonal.TraceVolume

variable {t p b c h q u binds : ℕ}

theorem preparation_cost (t p b c h q w binds : ℕ) :
    (11*(c+q)*(5*w+6)+6 + (4+11*(t*c)*(2*binds+4)))+
      (9+17*(2+(p+(b+t*h)))+26*((t*c)*3)) ≤ work t p b h c q w binds := by
  unfold work linkingTime graphVolume
  omega

/-- The metadata tape may follow an input of up to squared trace volume. Consecutive segments hold metadata
bits, the emitted physical rows, and the packed directory that the link arrays reuse. -/
theorem preparation_space_after_input (hu : 1 ≤ u) (ht : 1 ≤ t) {src : ℕ} (hsrc : src ≤ 2^(2*u^10))
    (hw : work t p b h c q (16*u^10) binds ≤ 2^(u^10)) :
    let w := 16*u^10
    let n := 11*(c+q)
    let raw := src+w*n
    let packed := raw+11*(t*c)
    raw < 2^w ∧ packed+n < 2^w ∧ raw ≤ 2^(3*u^10) ∧ t*c ≤ 2^(3*u^10) ∧
      2+(p+(b+t*h)) ≤ 2^(3*u^10) ∧ 2+q+h < 2^w ∧ c < 2^w := by
  let V := 2^(u^10)
  have hpow : 1 ≤ u^10 := Nat.one_le_pow _ _ hu
  have pos : 0<V := Nat.two_pow_pos _
  have large : V ≤ 2^(2*u^10) := Nat.pow_le_pow_right (by decide) (by omega)
  have wide : 2*2^(2*u^10) ≤ 2^(3*u^10) := by
    change 2^1*2^(2*u^10) ≤ 2^(3*u^10)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have huge : 32*2^(2*u^10) ≤ 2^(16*u^10) := by
    rw [show (32:ℕ)=2^5 from rfl,← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have emit : 11*(t*c) ≤ work t p b h c q (16*u^10) binds :=
    (Nat.le_mul_of_pos_right _ (by omega : 0<2*binds+4)).trans (by unfold work; omega)
  have budget : 11*(c+q)*(5*(16*u^10)+6) ≤ work t p b h c q (16*u^10) binds := by unfold work; omega
  have metadata : 16*u^10*(11*(c+q)) ≤ V := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega : 16*u^10 ≤ 5*(16*u^10)+6)).trans (budget.trans hw)
  have packed : 11*(c+q) ≤ V :=
    (Nat.le_mul_of_pos_right _ (by omega : 0<5*(16*u^10)+6)).trans (budget.trans hw)
  have hidden : h ≤ t*h := Nat.le_mul_of_pos_left _ (by omega)
  have graph : 10*(t*c+(b+t*h)+p+1) ≤ V := by
    apply le_trans _ hw
    unfold work graphVolume
    omega
  have cells : 11*(t*c) ≤ V := emit.trans hw
  dsimp only
  omega

theorem preparation_space (hu : 1 ≤ u) (ht : 1 ≤ t) {src : ℕ} (hsrc : src ≤ 2^(u^10))
    (hw : work t p b h c q (16*u^10) binds ≤ 2^(u^10)) :
    let w := 16*u^10
    let n := 11*(c+q)
    let raw := src+w*n
    let packed := raw+11*(t*c)
    raw < 2^w ∧ packed+n < 2^w ∧ raw ≤ 2^(3*u^10) ∧ t*c ≤ 2^(3*u^10) ∧
      2+(p+(b+t*h)) ≤ 2^(3*u^10) ∧ 2+q+h < 2^w ∧ c < 2^w :=
  preparation_space_after_input hu ht (hsrc.trans (Nat.pow_le_pow_right (by decide) (by omega))) hw

end ThreeFlat.Diagonal.TraceVolume

end OAI
