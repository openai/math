import OAI.LinearAlgebra.SpectralBooks.EnergyStates

/-! # The fermionic partition function in an energy interval

Tilting the temperature in each direction bounds the two tails. Inside the
interval every state has weight at most the exponential of its lower energy
cutoff, and the number of states is bounded by the upper cumulative count.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real

theorem fermionPartition_le_window {a w b : ℝ} (ha : 0 < a) (haw : a < w) (hwb : w < b)
    (L H : ℝ) : exp (fermionLogPartition w) ≤
    exp ((b - w) * L + fermionLogPartition b) + fermionCount H * exp (-w * L) +
      exp ((a - w) * H + fermionLogPartition a) := by
  classical
  let mid (s : Finset ℕ) := if s ∈ fermionStates H then exp (-w * L) else 0
  have hm : HasSum mid ((fermionCount H : ℝ) * exp (-w * L)) := by
    have h := hasSum_sum_of_ne_finset_zero (L := .unconditional _) (s := fermionStates H) (f := mid)
      (fun s hs ↦ by simp only [mid, hs, ↓reduceIte])
    have hh : ∑ s ∈ fermionStates H, mid s = (fermionCount H : ℝ) * exp (-w * L) := calc
      _ = ∑ _s ∈ fermionStates H, exp (-w * L) :=
        Finset.sum_congr rfl (fun s hs ↦ by simp only [mid, hs, ↓reduceIte])
      _ = _ := by simp [fermionCount]
    exact hh ▸ h
  have hw (c : ℝ) (hc : 0 < c) : HasSum (fun s : Finset ℕ ↦ exp (-c * fermionEnergy s))
      (exp (fermionLogPartition c)) := tsum_fermionWeight hc ▸ (summable_fermionWeight hc).hasSum
  have hb := ((hw b (ha.trans (haw.trans hwb))).mul_left (exp ((b - w) * L)))
  have hr := ((hw a ha).mul_left (exp ((a - w) * H)))
  rw [exp_add, exp_add]
  apply hasSum_le _ (hw w (ha.trans haw)) ((hb.add hm).add hr)
  intro s
  have hmid : 0 ≤ mid s := by simp only [mid]; split <;> positivity
  have hlow : 0 ≤ exp ((b - w) * L) * exp (-b * fermionEnergy s) := by positivity
  have hhigh : 0 ≤ exp ((a - w) * H) * exp (-a * fermionEnergy s) := by positivity
  rcases le_total (fermionEnergy s) L with h | h
  · have he : -w * fermionEnergy s ≤ (b - w) * L + -b * fermionEnergy s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hwb.le) (sub_nonneg.mpr h)]
    have hh := Real.exp_le_exp.mpr he
    rw [exp_add] at hh
    linarith
  by_cases hs : fermionEnergy s ≤ H
  · have hle : exp (-w * fermionEnergy s) ≤ mid s := by
      simp only [mid, mem_fermionStates.mpr hs, ↓reduceIte]
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (by linarith))
    linarith
  · have he : -w * fermionEnergy s ≤ (a - w) * H + -a * fermionEnergy s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr haw.le) (sub_nonneg.mpr (le_of_not_ge hs))]
    have hh := Real.exp_le_exp.mpr he
    rw [exp_add] at hh
    linarith

end SpectralBooks
end LinearAlgebra
end OAI
