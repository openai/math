import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract
import OAI.Optimization.LinearProgramming.Geometry.PivotBasis
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe
import OAI.Optimization.LinearProgramming.Geometry.Projection
import OAI.Optimization.LinearProgramming.PriceGame.Model
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Typed output of a complete or interrupted geometric price calculation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open Matrix RAM
open scoped Matrix

variable {r n : ℕ}

/-- Return-tag zero carries the computed label in scalar register 19. Return-tag one
carries the precise answered prefix and the first request for which a restart was needed. -/
inductive Result (packet : PivotKey n → List ℚ) (D : Matrix (Fin r) (Fin n) ℚ)
    (q : PriceGame.Query n) (before : Contract.History ℚ) (t : Memory ℚ) (final : Contract.History ℚ) : Prop where
  | completed (xs : List (PivotKey n × ℚ)) (rows : Fin r → PivotRow n)
      (requests : MinorQuery.Run (pivotPrefix D q.prices r le_rfl) xs (.inr (some rows)))
      (history : final = PivotPrefixRAM.answeredHistory packet xs before) (status : t.index 139=0)
      (answer : t.data 19 = if fwLabel (1-rowGramProjector (roundedPivotMatrix rows q.prices (OracleSpec.MinorLog.threshold n)))
        q.index then 1 else 0) : Result packet D q before t final
  | restarted (xs : List (PivotKey n × ℚ)) (key : PivotKey n)
      (requests : MinorQuery.Run (pivotPrefix D q.prices r le_rfl) xs (.inl key))
      (history : final = (packet key,[1]) :: PivotPrefixRAM.answeredHistory packet xs before)
      (status : t.index 139=1) : Result packet D q before t final

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
