import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.LinearAlgebra.SpectralBooks.Fermion.Fermion
import Mathlib.Tactic

/-! # Finite fermionic energy states and their partition function

Modes have energies `i + 1/2` and may each be occupied at most once. Expanding the
product over modes gives the sum of Boltzmann weights over finite states.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset Real

noncomputable section

/-- Energy of a state with occupied modes `s`. -/
def fermionEnergy (s : Finset ℕ) : ℝ := ∑ i ∈ s, ((i : ℝ) + 1 / 2)

theorem fermionEnergy_nonneg (s : Finset ℕ) : 0 ≤ fermionEnergy s :=
  Finset.sum_nonneg (fun i _ ↦ by positivity)

theorem Fermion.weight_eq_twice_energy (s : State) : (weight s : ℝ) = 2 * fermionEnergy s := by
  simp only [weight, fermionEnergy, Nat.cast_sum, Finset.mul_sum, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- All the states of energy at most the real threshold `H`. -/
def fermionStates (H : ℝ) : Finset (Finset ℕ) := Fermion.states ⌊2 * H⌋

@[simp] theorem mem_fermionStates {s : Finset ℕ} {H : ℝ} :
    s ∈ fermionStates H ↔ fermionEnergy s ≤ H := by
  rw [fermionStates, Fermion.mem_states, Int.le_floor, Int.cast_natCast,
    Fermion.weight_eq_twice_energy]
  constructor <;> intro h <;> linarith

theorem Fermion.states_eq_fermionStates (B : ℤ) : states B = fermionStates ((B : ℝ) / 2) := by
  rw [fermionStates, show 2 * ((B : ℝ) / 2) = B by ring, Int.floor_intCast]

/-- The cumulative state count `D(H)` of the crossing construction. -/
def fermionCount (H : ℝ) : ℕ := (fermionStates H).card

theorem fermionCount_pos {H : ℝ} (hH : 0 ≤ H) : 0 < fermionCount H :=
  Finset.card_pos.mpr ⟨∅, mem_fermionStates.mpr (by simpa [fermionEnergy] using hH)⟩

/-- Logarithm of the partition function written as a sum over modes. -/
def fermionLogPartition (a : ℝ) : ℝ :=
  ∑' i : ℕ, Real.log (1 + Real.exp (-a * ((i : ℝ) + 1 / 2)))

private theorem summable_modeWeight {a : ℝ} (ha : 0 < a) :
    Summable (fun i : ℕ ↦ Real.exp (-a * ((i : ℝ) + 1 / 2))) :=
  Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha) (fun _ ↦ by linarith)

/-- The Boltzmann weights of the states are summable at positive inverse temperature. -/
theorem summable_fermionWeight {a : ℝ} (ha : 0 < a) :
    Summable (fun s : Finset ℕ ↦ Real.exp (-a * fermionEnergy s)) := by
  simpa only [fermionEnergy, Finset.mul_sum, Real.exp_sum] using
    summable_finsetProd_of_summable_nonneg (fun i ↦ Real.exp_nonneg _) (summable_modeWeight ha)

/-- The sum over all states is the exponential of the sum of the mode logarithms. -/
theorem tsum_fermionWeight {a : ℝ} (ha : 0 < a) :
    ∑' s : Finset ℕ, Real.exp (-a * fermionEnergy s) = Real.exp (fermionLogPartition a) := by
  rw [fermionLogPartition, Real.rexp_tsum_eq_tprod (fun _ ↦ by positivity)
    (Real.summable_log_one_add_of_summable (summable_modeWeight ha)),
    tprod_one_add (summable_finsetProd_of_summable_nonneg (fun _ ↦ Real.exp_nonneg _)
      (summable_modeWeight ha))]
  simp only [fermionEnergy, Finset.mul_sum, Real.exp_sum]

/-- Exponential partition bound for the cumulative count, valid also for negative thresholds. -/
theorem fermionCount_le_exp {a : ℝ} (ha : 0 < a) (H : ℝ) :
    (fermionCount H : ℝ) ≤ Real.exp (a * H + fermionLogPartition a) := by
  have hsum := (summable_fermionWeight ha).sum_le_tsum (fermionStates H)
    (fun s _ ↦ (Real.exp_pos _).le)
  rw [tsum_fermionWeight ha] at hsum
  have hmin : ∑ s ∈ fermionStates H, Real.exp (-a * H) ≤
      ∑ s ∈ fermionStates H, Real.exp (-a * fermionEnergy s) :=
    Finset.sum_le_sum fun s hs ↦ Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (mem_fermionStates.mp hs) (by linarith))
  have h := hmin.trans hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  rw [Real.exp_add]
  simpa [fermionCount, ← Real.exp_add, mul_assoc, mul_comm (Real.exp (a * H))] using
    mul_le_mul_of_nonneg_right h (Real.exp_pos (a * H)).le

end

end SpectralBooks
end LinearAlgebra
end OAI
