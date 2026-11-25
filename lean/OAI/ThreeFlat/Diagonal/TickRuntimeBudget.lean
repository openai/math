import OAI.ThreeFlat.Diagonal.DefectBudget
import Mathlib.Tactic

namespace OAI
/-! # Age-uniform cost of shared reconstruction and the weighted tick -/

namespace ThreeFlat.Diagonal.TickRuntimeBudget

/-- A polynomial multiple of a full chunk fits in a quarter of the team's
time, including any fixed field-dependent multiplicative constant. -/
theorem chunk_quarter {u e cm C : ℕ} (coef : 4*C ≤ u) (expo : e+1+cm ≤ u) (hu : 1 ≤ u) :
    let a := 2^(u^10-u^4)
    let m := 2^(u^10)/u^cm
    C*u^e*a ≤ m/4 := by
  intro a m
  have d : 0 < u^cm := Nat.pow_pos hu
  have a₁ := width_pow_le_two_pow_sq expo
  have e₂ := Nat.pow_le_pow_right hu (by decide : 2 ≤ 4)
  have e₄ := Nat.pow_le_pow_right hu (by decide : 4 ≤ 10)
  have h : (4*C)*(u^e*u^cm) ≤ 2^(u^4) := by
    calc
      (4*C)*(u^e*u^cm) ≤ u*(u^e*u^cm) := Nat.mul_le_mul_right _ coef
      _ = u^(e+1+cm) := by rw [pow_add,pow_succ]; ring
      _ ≤ 2^(u^2) := a₁
      _ ≤ 2^(u^4) := Nat.pow_le_pow_right (by decide) e₂
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  change _ ≤ 2^(u^10)/u^cm
  apply (Nat.le_div_iff_mul_le d).mpr
  calc
    C*u^e*a*4*u^cm = ((4*C)*(u^e*u^cm))*a := by ring
    _ ≤ 2^(u^4)*a := Nat.mul_le_mul_right _ h
    _ = 2^(u^10) := by
      change 2^(u^4)*2^(u^10-u^4) = _
      rw [← pow_add, Nat.add_sub_of_le e₄]

/-- The ceiling of the paper's seven-tenths exponent lies below the exponent
of a single physical chunk. -/
theorem replay_le_chunk {u : ℕ} (hu : 8 ≤ u) :
    2^((7*u^10+9)/10) ≤ 2^(u^10-u^4) := by
  have up : 0 < u := by omega
  have step : 8*u^4 ≤ u^5 := by
    rw [pow_succ u 4,Nat.mul_comm 8 (u^4)]
    exact Nat.mul_le_mul_left (u^4) hu
  have room := step.trans (Nat.pow_le_pow_right up (by decide : 5 ≤ 10))
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Fixed per-slot padding can reserve one hidden-bit pinning row per actual
unused hidden bit. All slots have the same contraction program text. -/
theorem padded_interpreter_quarter {m : ℕ} (large : 392 ≤ m) :
    let h := m/40000
    49+5*h+550*(2*h) ≤ m/4 := by
  intro h
  have cap : h*40000 ≤ m := Nat.div_mul_le_self _ _
  omega

/-- Building the variable padding records from the true selected sizes,
materializing the fixed lookup tables, clearing the evaluator registers and
running the padded weighted network all share the terminal quarter. -/
theorem padded_terminal_quarter {m lookup n : ℕ} (large : 8*(64+lookup) ≤ m)
    (suffix : n ≤ 4*(2*(m/40000))) :
    (5+62*n)+(53+lookup+5*(m/40000)+550*(2*(m/40000))) ≤ m/4 := by
  have h := Nat.div_mul_le_self m 40000
  omega

/-- Shift the fixed field/motif-dependent ROM overhead into the eventual age
threshold; the padding and evaluator retain the same absolute time exponent. -/
theorem fixed_ROM_quarter {m entries field : ℕ}
    (large : 8*(64+4+8*entries*(6*(8*entries)+10)+(field*field)*(6*(field*field)+10)) ≤ m)
    {n : ℕ} (suffix : n ≤ 4*(2*(m/40000))) :
    (4+8*entries*(6*(8*entries)+10))+(5+62*n)+
      (53+(field*field)*(6*(field*field)+10)+5*(m/40000)+550*(2*(m/40000))) ≤ m/4 := by
  let l := 4+8*entries*(6*(8*entries)+10)
  let f := (field*field)*(6*(field*field)+10)
  have h : 8*(64+(l+f)) ≤ m := by dsimp [l,f]; omega
  have b := padded_terminal_quarter h suffix
  dsimp [l,f] at b
  omega

theorem total {m admin cursor weights : ℕ} (a : admin ≤ m/4) (b : cursor ≤ m/4)
    (c : weights ≤ m/4) : admin+cursor+weights ≤ m := by omega

end ThreeFlat.Diagonal.TickRuntimeBudget

end OAI
