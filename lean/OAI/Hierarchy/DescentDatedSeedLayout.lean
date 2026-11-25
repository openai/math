import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Fixed physical widths for the original dated initialization -/
namespace Hierarchy.DescentDatedSeedStartup
structure Layout where
  base : ℕ
  groupsPerNode : ℕ
  /-- Width of the original paid census counter. -/
  fieldBits : ℕ
  /-- Width of each retained argument field read by the first operand resolver. -/
  operandBits : ℕ
  /-- The exact first matcher pitch for signed, active, shape, and paid census words. -/
  packedLanes : ℕ
  /-- Independent pitch of the seven retained operand fields and the node metadata. -/
  operandLanes : ℕ
  wire : ℕ
  history : ℕ
  seedWidth : ℕ
end Hierarchy.DescentDatedSeedStartup

end OAI
