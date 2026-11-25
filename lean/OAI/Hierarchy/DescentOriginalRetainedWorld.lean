import OAI.Hierarchy.DescentArchiveWorldShape

namespace OAI
/-! # A retained bit description with the shape of all its recipe fields -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentKernelHistory
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

structure Retained (p R : ℕ) (W : MarkedWorld F d P bits) where
  description : BitDescription W
  shape : WorldShape p R description

end Hierarchy.DescentBundleHistory

end OAI
