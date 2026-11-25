import OAI.Hierarchy.DescentExteriorHopLiteral

namespace OAI
/-! # The consecutive literal table allocation for an exterior ancestry replay -/
namespace Hierarchy.DescentExteriorReplay
open ProtocolRAM
noncomputable section

/-- All data defining these instructions are fixed before choosing the signed input. -/
structure Snapshots (k : ℕ) where
  hosts : ℕ → ℕ
  pitch : ℕ → ℕ
  shape : ℕ → Fin (2^k) → ℕ
  compact : ℕ → Option Bank

namespace Snapshots
variable {k : ℕ} (S : Snapshots k)
def start (S : Snapshots k) (base f : ℕ) : ℕ → ℕ
  | 0 => base
  | t+1 => S.start base f t + HopLiteral.words (S.hosts t) k f

theorem start_mono (base f : ℕ) : Monotone (S.start base f) :=
  monotone_nat_of_le_succ (fun _t => Nat.le_add_right _ _)

end Snapshots
end
end Hierarchy.DescentExteriorReplay

end OAI
