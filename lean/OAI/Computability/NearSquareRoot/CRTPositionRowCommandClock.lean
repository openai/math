import OAI.Computability.NearSquareRoot.CRTPositionRowCommandRun

/-! # Charging the named grouped table program to its physical row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.RowCommand
open IntegerMultiplication Code Adic Strip Loom PositionProgram
noncomputable section

/-- The original P192 table clock on the canonical grouped record family
implies the exact fixed-row clock used by the physical scan. -/
theorem groupedRunsOfClock {c : Cmd} {ρ : ℝ} (positive : 0 ≤ ρ) (d : ℕ)
    (run : EffectiveTask.Runs c (fun z : Window.Row =>
      ⌈tableRate ρ z.1.mid ((RowCommandLow.wide z).count+(z.1.mid+1)^d)⌉₊)
      (together (fun z => send (Reflections.table z.1.perm.symm))
        (cloth (fun z => line 2 z.1.mid) RowCommandLow.wide RowCommandLow.data))
      (cloth (fun z => line 2 z.1.mid) RowCommandLow.wide (fun z a =>
        RowCommandLow.data z ((permuteNative z.1.perm.symm).symm a)))) : GroupedRuns c ρ := by
  have data : EffectiveTask.Runs c (fun z : Window.Row =>
      ⌈tableRate ρ z.1.mid ((RowCommandLow.wide z).count+(z.1.mid+1)^d)⌉₊)
      RowCommandLow.middleInput RowCommandLow.groupedOut := by
    simpa only [RowCommandLow.middleInput,RowCommandLow.groupedIn_eq,RowCommandLow.groupedOut_eq] using run
  refine ⟨d,fun select low => (data.on select).bound 1 (fun i => ?_)⟩
  let x := (select i).1
  let w := 2^x.lo*x.w
  have hw : (RowCommandLow.wide (select i)).count = w := by
    simp only [RowCommandLow.wide,Window.natural,Series.count_cart,lineSize,Series.count_natural,w,x]
  have mid : x.mid ≤ x.k := by unfold Window.mid; omega
  have slack : (x.mid+1)^d ≤ w :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ mid) d).trans
      ((payload_capacity d x.k x.w x.pos).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (low i))))
  have positiveRate : 0 ≤ positionRate ρ x.mid := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_positionRate positive _)
  have hr : 2 * positionRate ρ x.mid ≤ positionFactor ρ x.k := positionFactor_pays positive mid
  change ⌈tableRate ρ x.mid ((RowCommandLow.wide (select i)).count+(x.mid+1)^d)⌉₊+1 ≤
    1*(2^x.mid*w*positionFactor ρ x.k+1)
  rw [one_mul,hw]
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  rw [tableRate_eq]
  push_cast
  have ex : (((x.mid:ℝ)+1)^d) ≤ (w : ℝ) := by exact_mod_cast slack
  calc
    _ ≤ (2:ℝ)^x.mid * ((w:ℝ)+w) * positionRate ρ x.mid := by gcongr
    _ = (2:ℝ)^x.mid * w * (2*positionRate ρ x.mid) := by ring
    _ ≤ _ := by gcongr

end
end Controlled.PositionRows.RowCommand

end NearSquareRoot
end Computability
end OAI
