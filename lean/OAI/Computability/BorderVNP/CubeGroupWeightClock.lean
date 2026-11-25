import OAI.Computability.BorderVNP.CubeGroupWeightCheckedSchedule
import OAI.Computability.BorderVNP.CubeMeanClock

/-! # The sparse public clock for the actual group scheduler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Filter

/-- Tick allowance of the histogram, first-minimum assignment and capacity check. -/
def checkedTicks (l : Layout) (teams : TeamNative.Layout) :=
  ticks l + TeamNative.assignmentTicks teams +
    (TeamBudget.setup.slots+(teams.r+1)*(TeamBudget.row.slots+1)+1)

/-- Exact native instruction accounting for the three consecutive stages. -/
theorem checkedTicks_eq (l : Layout) (teams : TeamNative.Layout) (hg : teams.groups = l.groups) :
    checkedTicks l teams = 124+13*l.groups+21*(l.groups*l.groups)+13*l.cells+
      13*(teams.r+1)+12*(l.groups*(teams.r+1)) := by
  change 66+(l.groups*4+2+(l.groups*l.groups*21+2+(l.cells*13+2)))+
    (22+(4*(teams.r+1)+2+(teams.groups*(12*(teams.r+1)+9)+2)))+
    (25+(teams.r+1)*9+1) = _
  rw [hg]
  ring

/-- The native group scheduler fits the public descriptor envelope from Section 8.1. -/
theorem checkedTicks_le_envelope (l : Layout) (teams : TeamNative.Layout) (Z : ℕ)
    (hg : teams.groups = l.groups) (hr : teams.r+1 ≤ l.groups) (hd : l.groups ≤ Z) :
    checkedTicks l teams ≤ MeanChoice.scanEnvelope 256 l.cells 0 Z := by
  let A := (l.cells+1)*(Z+1)^6
  have pos : 0 < (Z+1)^6 := pow_pos (Nat.zero_lt_succ _) _
  have one : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) pos.ne')
  have cells : l.cells ≤ A := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ pos)
  have power : (Z+1)^2 ≤ (Z+1)^6 := Nat.pow_le_pow_right (Nat.zero_lt_succ _) (by decide)
  have room : (Z+1)^2 ≤ A := power.trans (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _))
  rw [pow_two] at room
  have dz : l.groups*l.groups ≤ A := (Nat.mul_self_le_mul_self (hd.trans (Nat.le_succ _))).trans room
  have dr : l.groups*(teams.r+1) ≤ A := (Nat.mul_le_mul_left _ hr).trans dz
  have gd : l.groups ≤ A := (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ teams.r)).trans dr
  have rd : teams.r+1 ≤ A := hr.trans gd
  rw [checkedTicks_eq _ _ hg,MeanChoice.scanEnvelope]
  change _ ≤ 256*(l.cells+1)*(0+1)*(Z+1)^6
  rw [Nat.mul_one,Nat.mul_assoc]
  change _ ≤ 256*A
  omega

/-- The threshold is chosen before team size, cell count and the actual RAM layout.
Together with the grouping-room bounds this puts the full checked schedule
strictly below the public term `r n^0.95` of (8.3). -/
theorem eventually_checkedTicks {α : ℝ} (hα : 0 < α) (a B : ℕ) (small : α*a < 1/10^6) :
    ∀ᶠ n : ℕ in atTop, ∀ (r : ℕ) (l : Layout) (teams : TeamNative.Layout),
      1 ≤ r → teams.groups = l.groups → teams.r+1 ≤ l.groups → l.groups ≤ labelCount α a n →
      (l.cells : ℝ) ≤ B*r*(n : ℝ)^(9/10 : ℝ) → (checkedTicks l teams : ℝ) < r*(n : ℝ)^(95/100 : ℝ) := by
  filter_upwards [MeanChoice.eventually_scanEnvelope hα a small 256 B] with n hn
  intro r l teams hr hg hR hd hc
  have bound := checkedTicks_le_envelope l teams (labelCount α a n) hg hR hd
  exact (Nat.cast_le (α := ℝ).2 bound).trans_lt (hn r l.cells 0 hr hc (by
    simpa using Real.rpow_nonneg (Nat.cast_nonneg n) (1/100 : ℝ)))

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
