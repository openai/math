import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixRAM
import OAI.Optimization.LinearProgramming.Geometry.MarkedSegments
import OAI.Optimization.LinearProgramming.Geometry.OracleUnique

/-! Each physical query in the prefix inherits the batch's memory certificate. The
existing quantitative and mathematical proof is reused with marked control operations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM Contract OracleSegments

theorem markedRules (mark : QueryMark ℚ) (o : ScalarOracle ℚ) : TraceRules (fun b => MarkedRuns mark b o) where
  core x h := MarkedRuns.core x o h
  weaken x h := MarkedRuns.weaken x h
  seq x y := MarkedRuns.seq x y
  branchTrue cond x := MarkedRuns.branchTrue cond x
  branchFalse cond x := MarkedRuns.branchFalse cond x
  loopFalse cond body safe off := MarkedRuns.loopFalse cond body safe off
  loopTrue cond x y := MarkedRuns.loopTrue cond x y

/-- A mark witnesses the RAM-side ABI at each live query reached from a legal batch
input. Determinism identifies its entire output with the ordinary numerical proof. -/
def MarkedBatchInputs {r n : ℕ} (mark : QueryMark ℚ) (batch : Segment) (o : ScalarOracle ℚ) (base : Memory ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (B extra : ℕ) (Aux : Memory ℚ → Contract.History ℚ → Prop) : Prop :=
  ∀ (a : ℕ) (ha : a < r) (rows : Fin a → PivotRow n) (m : Memory ℚ) (hist : Contract.History ℚ) (H : ℕ),
    Stored base m rows price B → (D.submatrix (Fin.castLE (Nat.le_of_lt ha)) (fun j => (rows j).pivot)).det ≠ 0 →
    Aux m hist → RowRAM.Within H m → ∃ t final k, MarkedRuns mark batch o (RowRAM.Within (H+extra)) m hist k t final

theorem MarkedBatchInputs.annotation {r n B extra : ℕ} {mark : QueryMark ℚ} {batch : Segment} {o : ScalarOracle ℚ}
    {base : Memory ℚ} {D : Matrix (Fin r) (Fin n) ℚ} {price : Fin n → ℚ} {Aux : Memory ℚ → Contract.History ℚ → Prop}
    (marked : MarkedBatchInputs mark batch o base D price B extra Aux) :
    BatchAnnotation (fun b => MarkedRuns mark b o) batch o base D price B extra Aux := by
  intro a ha rows m hist H stored old aux safe t final k ordinary
  obtain ⟨w,hf,c,run⟩ := marked a ha rows m hist H stored old aux safe
  obtain ⟨rfl,rfl,rfl⟩ := Runs.unique ordinary run.forget
  exact run

/-- The returned cost and full transcript obey the prefix bounds while every real
scalar request additionally certifies its physical memory and query registers. -/
theorem run_marked {r n B L extra C H : ℕ} (mark : QueryMark ℚ) (batch : Segment) (o : ScalarOracle ℚ)
    (packet : PivotKey n → List ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ)
    (base : Memory ℚ) (hist₀ : Contract.History ℚ) (Aux : Memory ℚ → Contract.History ℚ → Prop)
    (layout : Layout base r n B) (hD : LinearIndependent ℚ D.row) (hb : RowRAM.Within H base)
    (stable : FrameStable base r n Aux) (aux₀ : Aux base hist₀) (ok : BatchSound batch o packet base D price B L extra C Aux)
    (marked : MarkedBatchInputs mark batch o base D price B extra Aux) :
    ∃ t final k, k ≤ r*stepCost n B C+6 ∧
      MarkedRuns mark (program batch) o (RowRAM.Within (H+r*stepWidth n L B extra)) base hist₀ k t final ∧
      Aux t final ∧ Outcome packet base D price B hist₀ t final :=
  run_with (markedRules mark o) batch o packet D price base hist₀ Aux layout hD hb stable aux₀ ok marked.annotation

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
