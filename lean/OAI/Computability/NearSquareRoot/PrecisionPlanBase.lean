import OAI.Computability.NearSquareRoot.PrecisionPlanNode
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIdeal
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeBaseNorm

/-! # Exact flat Walsh target of a terminal node

The two-bit ordinal kernel has the standard normalized Walsh entries in its
little-endian digit order. Every spectator coordinate is preserved. Thus
the unitary used in the terminal roundoff proof is precisely the ideal row
operation used throughout the recursion.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open Matrix KernelPass FlatWalshNode PhysicalWalshBase PhysicalWalsh.ChildLanes
noncomputable section

private theorem bits_testBit : ∀ (u : Fin 4) (j : Fin 2),
    decide (bits u j = 1) = u.val.testBit j.val := by decide

private theorem digitKernel_flat (u v : Fin 4) :
    (pairEntry (bits u) (bits v) : ℂ) =
      BoxFin.flatWalsh (Finset.univ : Finset (Fin 2)) u v := by
  rw [FlatWalshKernel.bitPair, FlatWalshKernel.fullFlat]
  simp only [bits_testBit]

private theorem baseInputPos (s : Shape) (t : Fin (baseSize s)) (j : Fin 4) :
    ((laneEquiv s.pref 4 s.suff).symm (j, (laneEquiv s.pref 4 s.suff t).2)).val =
      (t.val/s.suff/4*4+j.val)*s.suff+t.val%s.suff := by
  have e := finProdFinEquiv.symm_apply_apply (t.divNat.divNat, t.modNat)
  have d : (finProdFinEquiv (t.divNat.divNat,t.modNat)).divNat = t.divNat.divNat := congrArg Prod.fst e
  have r : (finProdFinEquiv (t.divNat.divNat,t.modNat)).modNat = t.modNat := congrArg Prod.snd e
  simp only [laneEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, d, r]
  change t.val%s.suff + s.suff*(j.val + 4*(t.val/s.suff/4)) = _
  ring

/-- The four-point base is the flat normalized Walsh map on the precise
physical ordinal interval, with both spectator fields intact. -/
theorem baseIsometry_idealRow (A : ℕ) (s : Shape) (hl : s.level = 0) (x : IdealRow) :
    baseIsometry s (atWidth (baseSize s) x) =
      atWidth (baseSize s) (idealRow A s x) := by
  apply WithLp.ofLp_injective
  funext t
  change (fieldKernel s.pref s.suff *ᵥ (fun j => x j.val)) t = activeRow (grow A s.level) s.suff x t.val
  rw [fieldKernel_apply, show grow A s.level = 2 by simp [grow,hl]]
  unfold activeRow
  apply Finset.sum_congr rfl
  intro j _
  rw [digitKernel_flat, baseInputPos]
  rfl

/-- At depth zero the actual recursive node satisfies its range guard and
approximates the recursion's global ideal row on all of its stored cells. -/
theorem run_base_ideal_error {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (frac : ℕ)
    (s : Shape) (hl : s.level = 0) (x : Data s) (M : ℝ)
    (bounded : ‖atWidth (count (a+1) s) (meaningRow frac x)‖ ≤ M)
    (room : M * 2^frac < 2^s.w) :
    Good hW plan s x ∧
      ‖atWidth (count (a+1) s) (meaningRow frac (run hW plan s x)) -
        atWidth (count (a+1) s) (idealRow (a+1) s (meaningRow frac x))‖ ≤
      Real.sqrt (count (a+1) s) * (2/(2:ℝ)^frac) := by
  rw [count_base _ _ hl] at bounded ⊢
  have h := run_base_stable hW plan frac s hl x (baseValues frac s x) M bounded room
  refine ⟨h.1, ?_⟩
  rw [← baseIsometry_idealRow _ _ hl]
  simpa only [atWidth, meaningRow, baseValues, sub_self, norm_zero, add_zero] using h.2

end
end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
