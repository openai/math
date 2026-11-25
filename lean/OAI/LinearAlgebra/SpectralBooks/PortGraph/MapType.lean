import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

/-! # Local types for the sum over rooted numbered maps -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

/-- Root flag and ordered list of port directions. Numbers start at zero and
`true` denotes the head port of an oriented edge. -/
structure MapType where
  degree : Fin 5
  root : Bool
  direction : Fin degree.val → Bool
  deriving DecidableEq, Fintype

end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
