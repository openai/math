import OAI.Hierarchy.ProtocolRAMFailureWords

namespace OAI
/-! # Public data layouts for the strip price table and aggregate test -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM

structure StripTest (digits : ℕ) where
  table : Bank
  radix : ℕ
  quoted : Fin digits→Expr
  live : Expr
  rows : ℕ
  population : ℕ
  base : ℕ
  rowBits : ℕ
  precision : ℕ
  tolerance : ℝ

namespace Calendar.GlobalTests

structure Layout where
  base : ℕ
  indexBits : ℕ
  stride : ℕ
  precision : ℕ

end Calendar.GlobalTests
end Hierarchy.ProtocolRAM

end OAI
