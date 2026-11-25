import OAI.Optimization.LinearProgramming.Geometry.PriceStep
import OAI.Optimization.LinearProgramming.Geometry.NamedRequests

/-! Charged, canonical minor calls of a single deterministic price step. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- The new scalar history and the outer price result are identified by one typed
trace. The bound counts the extra request that causes a possible early restart. -/
theorem priceStep_decompose (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n) :
    ∃ xs : List (PivotKey n × ℚ), ∃ out : Sum (PivotKey n) Bool,
      MinorQuery.Run (geometricMinorLabel D q.prices q.index) xs out ∧
      S.priceStep before q=(out.elim (fun _ => none) some,MinorQuery.recorded (keyPacket D E) xs out before) ∧
      xs.length+MinorQuery.restartCost out≤r*n ∧
      (∀ e∈xs, ∃ u, Canonical.checkedPrimalMinor D E e.1=some u) ∧
      MinorQuery.StopKey (fun k => ∃ u, Canonical.checkedPrimalMinor D E k=some u) out := by
  let z := S.priceTrace before q
  obtain ⟨requests,hist⟩ := S.priceTrace_spec before q
  have named : MinorQuery.AllKeys (fun k => ∃ u, Canonical.checkedPrimalMinor D E k=some u)
      (geometricMinorLabel D q.prices q.index) := by
    unfold geometricMinorLabel
    apply MinorQuery.AllKeys.bind (pivotPrefix_named D E q.prices r le_rfl)
    rintro (_|rows) <;> trivial
  exact ⟨z.answers,z.out,requests,Prod.ext rfl hist,geometricMinorLabel_run_length _ _ _ requests,requests.all_keys named⟩

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
