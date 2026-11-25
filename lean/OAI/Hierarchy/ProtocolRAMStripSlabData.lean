import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Fixed public header end and private threshold exponent for a chronological slab -/
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
/-- The threshold bank occupies a power-of-two interval. Its exponent is the
instance exponent plus a fixed constant sufficient for the price padding. -/
structure Slab where
  headerEnd : ℕ
  thresholdExtra : ℕ

end Hierarchy.ProtocolRAM.Calendar.StripChart

end OAI
