import Mathlib.Data.Nat.Notation

namespace OAI
/-! # Common numerical operands of the installed grid evaluator -/

namespace Hierarchy.GridNativeImage

/-- Numerical operands common to every selector and external assignment. -/
structure Layout where
  dimension : ℕ
  sideMinusOne : ℕ
  bank : ℕ
  copies : ℕ
  pinWidth : ℕ
  selectorCap : ℕ
  receiverText : ℕ
  receiverPC : ℕ
  logRadix : ℕ
  degree : ℕ
  stageRate : ℕ
  rootRate : ℕ

end Hierarchy.GridNativeImage

end OAI
