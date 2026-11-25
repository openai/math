import Lean.Elab.Tactic.Omega

namespace OAI
/-! # Work capacity in the grouped diagonal schedule

The integer slot count and the integer tick allowance both round down. The
slack from the exponent choice absorbs both losses and the unused tail of
each slot in the greedy contiguous schedule.
-/

namespace ThreeFlat.Diagonal

private theorem le_twice_div_mul {n d : Nat} (hd : 0 < d) (hn : d ≤ n) :
    n ≤ (2 * (n / d)) * d := by
  have h₁ : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by simpa using hn)
  have h₂ : n / d + 1 ≤ 2 * (n / d) := by omega
  calc
    n ≤ d * (n / d + 1) := Nat.le_of_lt (Nat.lt_mul_div_succ n hd)
    _ ≤ d * (2 * (n / d)) := Nat.mul_le_mul_left _ h₂
    _ = _ := Nat.mul_comm ..

/-- A polynomial gain of at least one power of `w` leaves a factor of 256 in
the total work budget. The bound holds with floor division in both budgets. -/
theorem schedule_work_budget {w cm s V K : Nat} (hw : 512 ≤ w) (hs : cm + 1 ≤ s)
    (hV : w ^ cm ≤ V) :
    256 * (K * V / w ^ s) ≤ (V / w ^ cm) * K := by
  have hwpos : 0 < w := by omega
  have hd := Nat.pow_pos (n := cm) hwpos
  have hfactor : 512 * w ^ cm ≤ w ^ s := by
    calc
      512 * w ^ cm ≤ w * w ^ cm := Nat.mul_le_mul_right _ hw
      _ = w ^ (cm + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right hwpos hs
  let W := K * V / w ^ s
  let m := V / w ^ cm
  have hscaled : (2 * (256 * W)) * w ^ cm ≤ (2 * (m * K)) * w ^ cm := by
    calc
      (2 * (256 * W)) * w ^ cm = W * ((2 * 256) * w ^ cm) := by ac_rfl
      _ ≤ W * (w ^ s) := Nat.mul_le_mul_left _ hfactor
      _ ≤ K * V := Nat.div_mul_le_self _ _
      _ ≤ K * ((2 * m) * w ^ cm) := Nat.mul_le_mul_left K (le_twice_div_mul hd hV)
      _ = (2 * (m * K)) * w ^ cm := by ac_rfl
  have h := Nat.le_of_mul_le_mul_right hscaled hd
  change 256 * W ≤ m * K
  omega

/-- Specialize to the paper's volume, teams and transitions. -/
theorem diagonal_work_budget {w cm s : Nat} (hw : 512 ≤ w) (hc : cm ≤ w)
    (hs : cm + 1 ≤ s) :
    let V := 2 ^ (w ^ 10)
    let q := 2 ^ (w ^ 3)
    let T := 2 ^ (w ^ 6)
    256 * (q * T * V / w ^ s) ≤ (V / w ^ cm) * (q * T) := by
  dsimp only
  apply schedule_work_budget hw hs
  have hwpos : 0 < w := by omega
  calc
    w ^ cm ≤ (2 ^ w) ^ cm := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
    _ = 2 ^ (w * cm) := (Nat.pow_mul ..).symm
    _ ≤ 2 ^ (w ^ 10) := Nat.pow_le_pow_right (by decide) (by
      calc
        w * cm ≤ w * w := Nat.mul_le_mul_left w hc
        _ = w ^ 2 := by simp [Nat.pow_succ]
        _ ≤ w ^ 10 := Nat.pow_le_pow_right hwpos (by decide))

/-- A group of total work at most `4 W / J` fits in its actual number of
slots. Every slot has `m / 4` ticks and may leave `maxCell` ticks unused. -/
theorem group_slot_budget {W m K J group maxCell : Nat} (hJ : 0 < J) (hcount : 4 * J ≤ K)
    (hm : 16 ≤ m) (hcell : 16 * maxCell ≤ m) (hgroup : J * group ≤ 4 * W)
    (hwork : 256 * W ≤ m * K) :
    group ≤ (K / (4 * J)) * (m / 4 - maxCell) := by
  let slots := K / (4 * J)
  let available := m / 4 - maxCell
  have hc : K ≤ (2 * slots) * (4 * J) :=
    le_twice_div_mul (Nat.mul_pos (by decide) hJ) hcount
  have ha : m ≤ 8 * available := by dsimp only [available]; omega
  have h64 : 64 * (J * group) ≤ 256 * W := by omega
  apply Nat.le_of_mul_le_mul_left (c := 64 * J) _ (Nat.mul_pos (by decide) hJ)
  calc
    (64 * J) * group = 64 * (J * group) := Nat.mul_assoc ..
    _ ≤ 256 * W := h64
    _ ≤ m * K := hwork
    _ ≤ (8 * available) * ((2 * slots) * (4 * J)) := Nat.mul_le_mul ha hc
    _ = ((8 * 2 * 4) * J) * (slots * available) := by ac_rfl

end ThreeFlat.Diagonal

end OAI
