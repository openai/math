import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Measured terminal home format -/
namespace Hierarchy.DescentTerminalCompiledPrefix.Home

/-- These are public bounds of the local recipe format. The number of actual
owners and operands remains a measured input for each accepted branch. -/
structure Format where
  publicArity : ℕ
  roles : ℕ
  privateWords : ℕ
  nodes : ℕ
  addresses : ℕ
  piece : ℕ
  groups : ℕ

end Hierarchy.DescentTerminalCompiledPrefix.Home

end OAI
