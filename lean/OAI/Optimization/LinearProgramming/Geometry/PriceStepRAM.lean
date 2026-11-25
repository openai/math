import OAI.Optimization.LinearProgramming.Geometry.PriceStep
import OAI.Optimization.LinearProgramming.Geometry.LabelResult

/-! The legal physical price trace is the deterministic price step, for every
initial caller scratch layout compatible with the geometric RAM interface. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open Contract RAM Matrix BorderBatch

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

theorem Result.priceStep_eq (S : Service D E) {before final : Contract.History ℚ} {m : Memory ℚ} {q : PriceGame.Query n}
    (done : Result (keyPacket D E) D q before m final) (legal : answersMatch S.oracle final) :
    S.priceStep before q=((if m.index 139=0 then some (decide (m.data 19=1)) else none),final) := by
  cases done with
  | completed xs rows requests history status answer =>
    let flag := fwLabel (1-computeGramProjector (roundedPivotMatrix rows q.prices (geoCutoff n))) q.index
    have tree : MinorQuery.Run (geometricMinorLabel D q.prices q.index) xs (.inr flag) := by
      unfold geometricMinorLabel
      rw [← List.append_nil xs]
      apply MinorQuery.Run.bind_answer requests
      exact .done flag
    have finalEq : final=MinorQuery.recorded (keyPacket D E) xs (.inr flag) before := history
    have label : m.data 19=if flag then 1 else 0 := by
      simpa only [flag,computeGramProjector_eq,show geoCutoff n=OracleSpec.MinorLog.threshold n by rfl] using answer
    rw [S.priceStep_of_run before q tree (finalEq ▸ legal),←finalEq,status]
    cases test : flag <;> simp [label,test]
  | restarted xs key requests history status =>
    have tree : MinorQuery.Run (geometricMinorLabel D q.prices q.index) xs (.inl key) := by
      unfold geometricMinorLabel
      exact MinorQuery.Run.bind_restart _ requests
    have finalEq : final=MinorQuery.recorded (keyPacket D E) xs (Sum.inl (β := Bool) key) before := history
    simpa [status,←finalEq] using S.priceStep_of_run before q tree (finalEq ▸ legal)

/-- Equality of the outer result and the exact minor transcript across two legal
geometric executions with the same old minor state and price input. -/
theorem Result.priceStep_unique (S : Service D E) {old f₁ f₂ : Contract.History ℚ} {m₁ m₂ : Memory ℚ} {q : PriceGame.Query n}
    (a : Result (keyPacket D E) D q old m₁ f₁) (b : Result (keyPacket D E) D q old m₂ f₂)
    (ha : answersMatch S.oracle f₁) (hb : answersMatch S.oracle f₂) :
    ((if m₁.index 139=0 then some (decide (m₁.data 19=1)) else none),f₁)=
      ((if m₂.index 139=0 then some (decide (m₂.data 19=1)) else none),f₂) :=
  (Result.priceStep_eq S a ha).symm.trans (Result.priceStep_eq S b hb)

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
