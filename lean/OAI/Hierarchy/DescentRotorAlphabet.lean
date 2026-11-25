import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum

namespace OAI
/-! # The finite physical rotor dictionary used by the reset and its scalar labels -/

namespace Hierarchy.DescentSixParty
/-- The fixed reset geometry and scalar dictionary shared by all reached dates. -/
structure RotorSpec where
  n : ℕ
  arcs : Fin (2^n)→Fin (2^n)→ℕ
  C : ℕ
  w : ℕ
  stageDegree : ℕ
  regularity : ℕ
  rowExponent : ℕ
  reserveExponent : ℕ

end Hierarchy.DescentSixParty

namespace Hierarchy.DescentResetGates
/-- The only tags are a fixed-host permutation and row, a Boolean literal, a single-bit
comparison against a constant, or the common two-bit equality instruction. -/
abbrev CanonicalTag (Y : ℕ) := (Equiv.Perm (Fin Y) × Fin Y) ⊕ (Bool ⊕ (Bool ⊕ Unit))

end Hierarchy.DescentResetGates

end OAI
