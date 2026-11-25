import OAI.ThreeFlat.Diagonal.TraceVolumeArithmetic

namespace OAI
/-! # The four replaceable strings and advice fit the diagonal tick input -/

namespace ThreeFlat.Diagonal.TraceVolume

theorem pins_at_scale {u e params : ℕ} (hu : cm ≤ u) (he : e ≤ u) (hparams : params ≤ u^e) :
    let S := 4*2^(u^10-u^4)+2^(u^3)+params
    S ≤ 2^(depth u) ∧ S ≤ 2^(u^10-2*u) := by
  intro S
  have u0 : 0 < u := by dsimp [cm] at hu; omega
  have u4 : 4 ≤ u := by dsimp [cm] at hu; omega
  have pow23 := Nat.pow_le_pow_right u0 (by decide : 2 ≤ 3)
  have pow34 := Nat.pow_le_pow_right u0 (by decide : 3 ≤ 4)
  have pow510 := Nat.pow_le_pow_right u0 (by decide : 5 ≤ 10)
  have grow (n : ℕ) : 4*u^n ≤ u^(n+1) := by
    rw [pow_succ,Nat.mul_comm (u^n)]
    exact Nat.mul_le_mul_right _ u4
  have p1 := Nat.le_self_pow (by decide : 2 ≠ 0) u
  have g2 := grow 2
  have g4 := grow 4
  change 4*u^2 ≤ u^3 at g2
  change 4*u^4 ≤ u^5 at g4
  let a := 2^(u^10-u^4)
  have ha (j : ℕ) (hj : j ≤ u^3) : 2^j ≤ a :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have pin : S ≤ 6*a := by
    have hq := ha (u^3) le_rfl
    have hx := hparams.trans ((width_pow_le_two_pow_sq he).trans (ha (u^2) pow23))
    dsimp only [S]
    omega
  have cancel : a*2^(u^4) = 2^(u^10) := by
    rw [show a = 2^(u^10-u^4) from rfl,← Nat.pow_add]
    congr 1
    omega
  have spare : 16*u^cm ≤ 2^(u^4) := calc
    _ ≤ 2^4*2^(u^2) := Nat.mul_le_mul_left _ (width_pow_le_two_pow_sq hu)
    _ = 2^(4+u^2) := (Nat.pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : 2*S ≤ cap u := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos u0)).mpr
    calc
      _ ≤ (2*(6*a))*u^cm := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ pin)
      _ ≤ a*(16*u^cm) := by ring_nf; omega
      _ ≤ a*2^(u^4) := Nat.mul_le_mul_left _ spare
      _ = _ := cancel
  have hl := (sites_cap hu).2
  refine ⟨by omega, pin.trans ?_⟩
  calc
    6*a ≤ 2^3*a := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(3+(u^10-u^4)) := (Nat.pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- Word-address bounds and the two-track grid with one full row of
time for each input slot. -/
theorem tick_grid {u e params : ℕ} (hu : cm ≤ u) (he : e ≤ u) (hparams : params ≤ u^e) :
    let S := (4*2^(u^10-u^4)+params)+2^(u^3)
    let f := 2^(depth u)
    S ≤ 2^(16*u^10) ∧ f ≤ 2^(16*u^10+1) ∧ S+f ≤ 2^(1+depth u) := by
  intro S f
  have hs : S ≤ f := by simpa only [S,f,Nat.add_right_comm] using (pins_at_scale hu he hparams).1
  have dw : depth u ≤ 16*u^10 := by have := depth_le u; omega
  exact ⟨hs.trans (Nat.pow_le_pow_right (by decide) dw),Nat.pow_le_pow_right (by decide) (by omega),
    by change S+2^(depth u) ≤ _; rw [pow_add,pow_one]; omega⟩

end ThreeFlat.Diagonal.TraceVolume

end OAI
