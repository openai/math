import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine

/-! Scalar encoding of the frozen index words and service reply tags. Kept independent
of determinant computation so replaying the persistent service requires only its contract. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open OracleSpec

def packet {r s n : ℕ} (u : MinorLog.RawIndex r s n) : List ℚ := (MinorLog.words u).map Nat.cast

def reply : Option ℚ → List ℚ
  | none => [1]
  | some q => [0,q]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
