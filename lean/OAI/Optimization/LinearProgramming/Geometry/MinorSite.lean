import OAI.Optimization.LinearProgramming.RAM.Code

/-! Register contract at the instant the geometric tester issues a minor request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM

/-- The register roles, high packet buffer and restored scratch required by the
native minor-service inliner, at the exact moment the oracle instruction executes. -/
structure MinorSite (m : Memory ℚ) (src len dst count : ℕ) : Prop where
  sourceReg : src=80
  lengthReg : len=81
  destinationReg : dst=82
  countReg : count=83
  sourceHigh : 35 ≤ m.index src
  destinationHigh : 35 ≤ m.index dst
  sharedBuffer : m.index dst=m.index src
  zero2 : m.data 2=0
  zero29 : m.data 29=0

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
