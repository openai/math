import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.AbsoluteValue.Basic

namespace OAI
/-! # Maximum metric code for a purchased socket of radius M -/
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public

noncomputable def maxMetric (M : ℕ) := M + ⌈Real.sqrt 2 * (M : ℝ)⌉₊ + 1

end Hierarchy.ProtocolRAM.BoughtSockets.Public

end OAI
