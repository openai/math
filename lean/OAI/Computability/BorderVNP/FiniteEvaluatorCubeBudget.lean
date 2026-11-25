import OAI.Computability.BorderVNP.CubeGroupNativeEventually
import OAI.Computability.BorderVNP.DiagonalFixedCube

/-! # The finite evaluator's capacity guard for its selected cube

The cube used by the field evaluator supplies the physical cut inequality for
every passing selector assignment. That inequality controls the actual team
weights written by its own verified grouping schedule.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.FixedCube

open Cube Cube.Physical Cube.GroupWeights VPVNP TeamScales Filter
open scoped BigOperators

universe u v

variable {F : Type u} [Field F] (cube : FixedCube F)

/-- The dimension encoded as a power of two has exactly the scale used by the
physical minimum-cut and group-weight estimates. -/
theorem scale_sqrt : 100*(2/Real.sqrt (cube.pred+1)+cube.tolerance) < 1/10^6 := by
  have dim : (cube.pred : ℝ)+1=(2 : ℝ)^cube.power := by exact_mod_cast cube.dimension
  rw [dim,Real.sqrt_eq_rpow,div_eq_mul_inv,← Real.rpow_neg (by positivity),
    show -(1/(2:ℝ)) = -1/2 by ring]
  exact cube.scale

/-- At every sufficiently large length the actual native capacity guard passes
on the physical schedule of this same fixed cube and its true declaration. -/
theorem eventually_budget_passes {α ξ : ℝ} (hα : 0 < α) (hξ : ξ < α/3)
    (hgap : 8*α*(cube.pred+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r : ℕ) (l : Layout) (teams : TeamNative.Layout) (blocks : ℕ)
      (orig mem : ℕ → ℕ) (A : Type v) [Fintype A] (D : LengthDeclaration cube.pred l.groups)
      (select : Packet cube.pred l.groups blocks → Selector cube.pred cube.copies cube.h)
      (label : Fin l.cells → Label (cube.pred+1) l.groups) (recv : A → Fin l.cells) (w : A → ℕ),
      1 ≤ r → (teams.r+1 : ℝ) ≤ (k : ℝ)^(2*α) → l.groups = alphabet α k →
      blocks = blocksFor (exterior ξ r k*(teams.r+1) : ℕ) (cube.h*cube.b) (l.groups^(cube.pred+1)) →
      ScheduleResult l teams orig mem → PhysicalImage l orig blocks cube.b cube.copies cube.h D label recv w →
      passesLengths cube.b cube.width select D →
      (∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
        4*((exterior ξ r k*(teams.r+1) : ℕ) : ℝ)/((l.groups^(cube.pred+1) : ℕ) : ℝ)) →
      (∑ a, w a) ≤ 3*(teams.r+1)*r*literal α k →
      (⟨teams.r+1,exterior ξ r k,teams.totals⟩ : TeamBudget.Layout).Passes mem := by
  let M := cube.h*cube.width+MotifWidths.selectorBits cube.copies (Fintype.card (Edge (cube.pred+1))) cube.h+1
  have gap : 8*α*((cube.pred+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using hgap
  filter_upwards [eventually_group_charge_room hα hξ (cube.pred+1) (cube.h*cube.b) M cube.block_pos gap,
    eventually_ge_atTop 1] with k room hk
  intro r l teams blocks orig mem A _ D select label recv w hr hR groups blockCount result image pass balanced data
  obtain ⟨small,localCap,pad,dataCap⟩ := room r (teams.r+1) hr (by omega) (by exact_mod_cast hR)
  rw [← groups] at small localCap pad
  rw [← blockCount] at pad
  have hd : 0 < l.groups := groups ▸ Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)
  have mult : M ≤ M*(2^cube.pred*(cube.h*cube.b)) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) cube.block_pos)
  exact result.passes_of_physical image _ (result.team_le_exterior_of_cut image cube.width select pass
    (exterior ξ r k) M (Nat.succ_pos _) hd cube.tolerance cube.scale_sqrt
    ((Nat.le_succ _).trans mult) (cube.cost _ _ hd select) balanced
    (by simpa only [Nat.cast_add,Nat.cast_one] using small) localCap pad (dataCap _ data))

end Diagonal.FixedCube

end BorderVNP
end Computability
end OAI
