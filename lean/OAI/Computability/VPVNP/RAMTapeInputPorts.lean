import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-! # Stack registers of the length-independent physical input reader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- Input, working counters, and the four extracted data fields. Each stack
contains individual bits in head-first order. -/
inductive InputPort where
  | input | tmp | count | prefix | address | header | incident | addressCount | incidentCount | size
  deriving DecidableEq

instance : Fintype InputPort := derive_fintype% _

end RAMTape

end VPVNP
end Computability
end OAI
