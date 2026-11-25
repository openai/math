import OAI.Optimization.LinearProgramming.PriceGame.Market
import OAI.Optimization.LinearProgramming.PriceGame.MarketOptimum

/-! Residual potentials certify maximum-weight integral transshipments. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace OptimumDual

open scoped BigOperators

variable {E G : Type*} [Fintype E] [Fintype G]

/-- The total potential drop depends only on supplies. The dummy's contribution vanishes
after subtracting its potential, and all real goods cancel by conservation. -/
theorem total_drop {pos : E → Bool} {qty : E → ℕ} {accepts : E → G → Prop}
    {g : E → Option G → ℕ} (hg : Optimum.Feasible pos qty accepts g)
    (p : E → ℚ) (π : Option G → ℚ) :
    ∑ e, ∑ o, side pos e * (p e - π o) * (g e o : ℚ) =
      ∑ e, side pos e * (p e - π none) * (qty e : ℚ) := by
  have cancel : ∑ e, ∑ o, (side pos e * (g e o : ℚ)) * (π o - π none) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro o _
    cases o with
    | none => simp
    | some i =>
      rw [← Finset.sum_mul]
      have hi : ∑ e, side pos e * (g e (some i) : ℚ) = 0 := hg.good i
      rw [hi, zero_mul]
  calc
    _ = ∑ e, ∑ o, (side pos e * (p e - π none) * (g e o : ℚ) -
        (side pos e * (g e o : ℚ)) * (π o - π none)) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro o _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, cancel, sub_zero]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.mul_sum, ← Nat.cast_sum, hg.row]

/-- A feasible integral flow with residual potentials is a maximum-weight flow. -/
theorem optimal_of_residual {pos : E → Bool} {qty : E → ℕ} {accepts : E → G → Prop}
    {c : E → G → ℚ} {f : E → Option G → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    (hf : Optimum.Feasible pos qty accepts f) (hp : ResidualPotentials pos accepts c f p π)
    (g : E → Option G → ℕ) (hg : Optimum.Feasible pos qty accepts g) :
    Optimum.value c g ≤ Optimum.value c f := by
  calc
    _ ≤ ∑ e, ∑ o, side pos e * (p e - π o) * (g e o : ℚ) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro o _
      by_cases hz : g e o = 0
      · simp [hz]
      · have ha : eligible accepts e o := by
          cases o with
          | none => exact True.intro
          | some i => exact Classical.byContradiction fun h => hz (hg.unavailable e i h)
        exact mul_le_mul_of_nonneg_right (hp.forward e o ha) (Nat.cast_nonneg _)
    _ = ∑ e, ∑ o, side pos e * (p e - π o) * (f e o : ℚ) :=
      (total_drop hg p π).trans (total_drop hf p π).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro o _
      by_cases hz : f e o = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (hp.backward e o (Nat.pos_of_ne_zero hz))
          (Nat.cast_nonneg _)

/-- Initial feasible flow at zero supplies. -/
theorem zero_feasible (pos : E → Bool) (accepts : E → G → Prop) :
    Optimum.Feasible pos (fun _ => 0) accepts (fun _ _ => 0) := by
  exact ⟨fun _ => by simp, fun _ _ _ => rfl, fun _ => by simp⟩

/-- The largest absolute cost of an arc, including the zero-cost dummy arcs. -/
def costBound (c : E → G → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image (fun ei : E × G => |c ei.1 ei.2|))).max' (by simp)

theorem costBound_nonneg (c : E → G → ℚ) : 0 ≤ costBound c :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem abs_le_costBound (c : E → G → ℚ) (e : E) (i : G) : |c e i| ≤ costBound c := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(e, i), Finset.mem_univ _, rfl⟩)

/-- Zero-flow potentials can be computed without finding any paths. -/
theorem zero_residual (pos : E → Bool) (accepts : E → G → Prop) (c : E → G → ℚ) :
    ResidualPotentials pos accepts c (fun _ _ => 0) (fun e => side pos e * costBound c)
      (fun _ => 0) := by
  refine ⟨?_, fun _ _ h => (Nat.not_lt_zero _ h).elim⟩
  intro e o _
  have hsign : side pos e * (side pos e * costBound c - 0) = costBound c := by
    cases he : pos e <;> simp [side, he]
  rw [hsign]
  cases o with
  | none => exact costBound_nonneg c
  | some i => exact (le_abs_self (c e i)).trans (abs_le_costBound c e i)

/-- Doubling every flow implements the doubling of the supplies. -/
theorem double_feasible {pos : E → Bool} {qty : E → ℕ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} (hf : Optimum.Feasible pos qty accepts f) :
    Optimum.Feasible pos (fun e => 2 * qty e) accepts (fun e o => 2 * f e o) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rw [← Finset.mul_sum, hf.row]
  · intro e i hi
    rw [hf.unavailable e i hi, mul_zero]
  · intro i
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ = (2 : ℚ) * ∑ e, Optimum.sign pos e * (f e (some i) : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = 0 := by rw [hf.good i, mul_zero]

omit [Fintype E] [Fintype G] in
/-- Doubling preserves residual edges and their potential inequalities. -/
theorem double_residual {pos : E → Bool} {accepts : E → G → Prop} {c : E → G → ℚ}
    {f : E → Option G → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    (hp : ResidualPotentials pos accepts c f p π) :
    ResidualPotentials pos accepts c (fun e o => 2 * f e o) p π := by
  refine ⟨hp.forward, ?_⟩
  intro e o h
  apply hp.backward
  omega

end OptimumDual
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
