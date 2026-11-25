import OAI.Hierarchy.DescentCompilerIteration
import Mathlib.Data.Fintype.Card

namespace OAI
/-! # One group size pays the root and atom slack at every compiler stage -/

namespace Hierarchy.DescentCompiler
open scoped BigOperators

/-- At age i the host has expanded i times and the number of live blocks
has shrunk i times. The next step joins a full group of r blocks. -/
def groups (R r l i : ℕ) := R*r^(l-(i+1))
def blocks (R r l i : ℕ) := R*r^(l-i)

/-- Using only the one-step position reservation, the count of jointly
reserved host positions and surviving blocks grows by one factor per step. -/
theorem positions_at (H : ℕ→ℕ) (m c r : ℕ) (initial : H 0≤m)
    (growth : ∀i,H (i+1)≤H i*(c*r)) (i : ℕ) : H i≤m*(c*r)^i := by
  induction i with
  | zero => simpa using initial
  | succ i ih => exact (growth i).trans (by simpa [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_right (c*r) ih)

theorem all_positions (H : ℕ→ℕ) (m c r R : ℕ) (initial : H 0≤m)
    (growth : ∀i,H (i+1)≤H i*(c*r)) {l i : ℕ} (hi : i≤l) :
    H i*blocks R r l i ≤ m*(R*r^l)*c^i := by
  apply (Nat.mul_le_mul_right _ (positions_at H m c r initial growth i)).trans_eq
  change m*(c*r)^i*(R*r^(l-i)) = _
  have power : r^i*r^(l-i)=r^l := by rw [←pow_add]; congr 1; omega
  rw [mul_pow]
  calc
    _ = m*(R*(r^i*r^(l-i)))*c^i := by ring
    _ = _ := by rw [power]

theorem groups_step {r R l i : ℕ} (hi : i<l) : groups R r l i*r=blocks R r l i := by
  unfold groups blocks
  rw [Nat.mul_assoc,←pow_succ]
  congr 2
  omega

/-- The group exponent depends only on fixed host growth, hub growth,
per-step packing cutoffs, and the number of rounds. A single r works for
every branch in every round, both for subround and reset root reservations. -/
def groupBits (t J hostGain hubGain cut : ℕ) :=
  J+(hostGain+hubGain)*((t+1)*J)+8+cut

theorem groupBits_linear (t J c g f : ℕ) :
    groupBits t J c g f≤(1+(c+g)*(t+1)+8+f)*(J+1) := by
  unfold groupBits
  nlinarith only [Nat.zero_le (c+g),Nat.zero_le ((c+g)*t),Nat.zero_le (J*f)]

theorem root_slack (t J c g f R m : ℕ) (H : ℕ→ℕ) (initial : H 0≤m)
    (growth : ∀i,H (i+1)≤H i*(2^c*2^groupBits t J c g f))
    {i a B : ℕ} (age : i<(t+1)*J) (cut : a≤f) (cap : B≤2^(8+g*i)) :
    let l := (t+1)*J
    let r := 2^groupBits t J c g f
    (H i*groups R r l i)*(2^a*B)*2^J≤m*(R*r^l) := by
  let l := (t+1)*J
  let r := 2^groupBits t J c g f
  let all := m*(R*r^l)
  have hcount := all_positions H m (2^c) r R initial growth age.le
  have groups : H i*groups R r l i*r≤all*(2^c)^i := by
    rw [Nat.mul_assoc,groups_step age]
    exact hcount
  have power : (2^c)^i*(2^a*B)*2^J ≤ r := by
    apply (Nat.mul_le_mul_right (2^J) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cap))).trans
    change (2^c)^i*(2^a*2^(8+g*i))*2^J≤2^groupBits t J c g f
    rw [←pow_mul,←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have cs := Nat.mul_le_mul_left c age.le
    have gs := Nat.mul_le_mul_left g age.le
    dsimp [groupBits]
    rw [Nat.add_mul]
    omega
  have both := (Nat.mul_le_mul_right ((2^a*B)*2^J) groups).trans
    (show (all*(2^c)^i)*((2^a*B)*2^J) ≤ all*r by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by simpa [Nat.mul_assoc] using power))
  have rpos : 0<r := Nat.two_pow_pos _
  change (H i*DescentCompiler.groups R r l i)*(2^a*B)*2^J≤all
  apply Nat.le_of_mul_le_mul_right ?_ rpos
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using both

/-- Convert the integer allocation directly to the real allowance of a chosen
physical placement. -/
theorem charged_roots {pos A B T total : ℕ} (ht : 0<T) (slack : pos*(A*B)*T≤total) :
    (pos:ℝ)*(A*B) ≤ (total:ℝ)/T := by
  apply (le_div_iff₀ (by exact_mod_cast ht : (0:ℝ)<T)).mpr
  exact_mod_cast slack

end Hierarchy.DescentCompiler

end OAI
