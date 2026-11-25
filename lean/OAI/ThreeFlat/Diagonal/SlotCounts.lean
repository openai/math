import OAI.ThreeFlat.Diagonal.SlotEnergy
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Capacities of the four surviving supply types

Either layout retains edges with the same four masses, in the order
BC, BN, CN, DM or AC, AM, CM, DN. -/

namespace ThreeFlat.Diagonal.SlotEnergy

noncomputable def retainedMass : Fin 4 → ℝ := ![8/31,4/31,40/93,16/31]

@[simp] theorem total_retainedMass : ∑ e, retainedMass e = 4/3 := by
  norm_num [retainedMass, Fin.sum_univ_succ]

theorem min_retainedMass (e : Fin 4) : (4/31 : ℝ) ≤ retainedMass e := by
  fin_cases e <;> norm_num [retainedMass]

/-- Number of new slots from one occurrence of a surviving supply edge.
`scale` is the ratio of new arc mass to old arc mass. -/
noncomputable def slotCount (scale : ℝ) (e : Fin 4) : ℕ := ⌊retainedMass e / scale⌋₊

/-- Output degree at least `1024*K*d` makes every parallel count positive
and loses at most one part in 128 of each supply mass. -/
theorem slotCount_mass {scale : ℝ} (hs : 0 < scale) (hsmall : scale ≤ 1/1024)
    (e : Fin 4) : 0 < slotCount scale e ∧
      (1-1/128)*retainedMass e ≤ slotCount scale e * scale ∧ slotCount scale e * scale ≤ retainedMass e := by
  have he := min_retainedMass e
  apply floor_mass hs (by linarith : 0 < retainedMass e) (by norm_num : (1/128 : ℝ) < 1)
  linarith

/-- After summing over all roles at a base vertex, the four types occupy a
common number of incoming and outgoing slots bounded by the output degree. -/
theorem slotCount_capacity {K d d' Q : ℕ} (hK : 0 < K) (hd : 0 < d) (hd' : 0 < d')
    (hQ : 4*Q = 3*K) :
    let scale : ℝ := (K*d : ℕ)/d'
    d*Q*(∑ e, slotCount scale e) ≤ d' := by
  intro scale
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hf (e : Fin 4) : (slotCount scale e : ℝ)*scale ≤ retainedMass e := by
    apply (le_div_iff₀ hs).mp
    apply Nat.floor_le
    exact div_nonneg (by linarith [min_retainedMass e]) hs.le
  have htot : (∑ e, (slotCount scale e : ℝ))*scale ≤ 4/3 := by
    rw [Finset.sum_mul, ← total_retainedMass]
    exact Finset.sum_le_sum fun e _ => hf e
  have hp : (0 : ℝ) < d' := by exact_mod_cast hd'
  have hav : (∑ e, (slotCount scale e : ℝ))*((K : ℝ)*d) ≤ (4/3 : ℝ)*d' := by
    apply (div_le_iff₀ hp).mp
    simpa only [scale, Nat.cast_mul, ← mul_div_assoc] using htot
  have hh : 4*(Q : ℝ) = 3*K := by exact_mod_cast hQ
  have ans : (d : ℝ)*Q*(∑ e, (slotCount scale e : ℝ)) ≤ d' := by
    nlinarith [congrArg (fun x : ℝ => x * d * (∑ e, (slotCount scale e : ℝ))) hh]
  exact_mod_cast ans

end ThreeFlat.Diagonal.SlotEnergy

end OAI
