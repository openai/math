import OAI.Computability.VPVNP.PairSimulationRouteSchedule
import OAI.Computability.VPVNP.PairSimulationRouteClock

/-!
# Exact tick counts for the native routing checker

The geometry and field-mode branches depend on the cursor position and
current system. Each field visits its full width. Adding the fixed loop
instructions therefore yields a trace length determined by the position
and dimensions, independently of the resident bits and scratch registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM CursorRouting CursorNetwork RAMLayout

variable {D : ℕ}

/-- The complete routing clock, including initialization, width switch and dispatch. -/
def clock (D H w : ℕ) : ℕ :=
  (13 * (8 * w) + 37) * D + 2 + (((13 * blockBits H w + 37) * D + 5) * D + 2) + 4

theorem clock_le {n e w : ℕ} (budget : ProcessorBudget n D e w) (hn : 2048 ≤ n) :
    clock D (2 ^ e) w ≤ n ^ 5 := RouteClock.scheduler_le budget hn

/-- A host at least as wide as the fitted processor holds its dimension and
both native loop bounds. The processor's address envelope bounds the sorting block. -/
theorem hostFits {n e w W : ℕ} (budget : ProcessorBudget n D e w) (hle : w ≤ W) :
    D < W ∧ 8*w < 2 ^ W ∧ blockBits (2^e) w < 2 ^ W := by
  have hH : 0 < 2 ^ e := Nat.two_pow_pos _
  have cap : 2 ^ D < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ hH).trans_lt budget.capFits
  have hd : D < w := by
    by_contra! h
    exact (not_le_of_gt cap) (Nat.pow_le_pow_right (by decide) h)
  let a := 2 ^ (2 + e + D) + w + 32
  have he : 2 ^ e ≤ a := calc
    _ ≤ 2 ^ (2 + e + D) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ a := by dsimp [a]; omega
  have hw : w ≤ a := (Nat.le_add_left w _).trans (Nat.le_add_right _ 32)
  have ha : 0 < a := by dsimp [a]; omega
  have wide : 2 ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hle
  have block : blockBits (2^e) w < 2 ^ W := calc
    _ = 20 * (2^e * w) := by unfold blockBits; ring
    _ ≤ 20 * (a * a) := Nat.mul_le_mul_left _ (Nat.mul_le_mul he hw)
    _ = 20 * a ^ 2 := by rw [pow_two]
    _ ≤ 64 * a ^ 4 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right ha (by decide))
    _ < 2 ^ w := budget.addresses
    _ ≤ 2 ^ W := wide
  have small : 8*w ≤ blockBits (2^e) w := Nat.mul_le_mul_right w (by omega)
  exact ⟨hd.trans_le hle, small.trans_lt block, block⟩

variable [NeZero D]

/-- Successor calls, offset additions and counted-loop control. -/
def succTicks (W : ℕ) (v : Position D) (H w : ℕ) : ℕ :=
  2 + ∑ i : Fin D, (RouteCall.ticks W v (.inl i) (ramFieldBits H w (.inl i)) + 3)

/-- The step scan in one sorting phase, including its offset additions. -/
def rowTicks (W : ℕ) (v : Position D) (H w : ℕ) (i : Fin D) : ℕ :=
  2 + ∑ j : Fin (i.val + 1), (RouteCall.ticks W v (.inr (layer i j)) (blockBits H w) + 3)

/-- Sorting phases, with the instruction computing each step bound and the outer control. -/
def phaseTicks (W : ℕ) (v : Position D) (H w : ℕ) : ℕ :=
  2 + ∑ i : Fin D, (rowTicks W v H w i + 3)

/-- Exact tick count at the site, from the initial mask clear to the final branch. -/
def routeTicks (W : ℕ) (v : Position D) (H w : ℕ) : ℕ :=
  2 + succTicks W v H w + 1 + phaseTicks W v H w + 1

private theorem sum_le (n bound : ℕ) (f : Fin n → ℕ) (h : ∀ i, f i ≤ bound) :
    ∑ i, f i ≤ bound * n := calc
  _ ≤ ∑ _ : Fin n, bound := Finset.sum_le_sum (fun i _ ↦ h i)
  _ = _ := by simp [Nat.mul_comm]

theorem succTicks_le (W : ℕ) (v : Position D) (H w : ℕ) :
    succTicks W v H w ≤ (13 * (8*w) + 37)*D + 2 := by
  unfold succTicks
  rw [Nat.add_comm 2]
  apply Nat.add_le_add_right
  apply sum_le
  intro i
  have := RouteCall.ticks_le W v (.inl i) (8*w)
  change RouteCall.ticks W v (.inl i) (8*w) + 3 ≤ _
  omega

theorem rowTicks_le (W : ℕ) (v : Position D) (H w : ℕ) (i : Fin D) :
    rowTicks W v H w i ≤ (13 * blockBits H w + 37) * (i.val + 1) + 2 := by
  unfold rowTicks
  rw [Nat.add_comm 2]
  apply Nat.add_le_add_right
  apply sum_le
  intro j
  have := RouteCall.ticks_le W v (.inr (layer i j)) (blockBits H w)
  omega

theorem phaseTicks_le (W : ℕ) (v : Position D) (H w : ℕ) :
    phaseTicks W v H w ≤ ((13 * blockBits H w + 37)*D+5)*D+2 := by
  unfold phaseTicks
  rw [Nat.add_comm 2]
  apply Nat.add_le_add_right
  apply sum_le
  intro i
  have := rowTicks_le W v H w i
  have := Nat.mul_le_mul_left (13*blockBits H w+37) (show i.val + 1 ≤ D from i.isLt)
  omega

theorem routeTicks_le (W : ℕ) (v : Position D) (H w : ℕ) :
    routeTicks W v H w ≤ clock D H w := by
  have := succTicks_le W v H w
  have := phaseTicks_le W v H w
  unfold routeTicks clock
  omega

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
