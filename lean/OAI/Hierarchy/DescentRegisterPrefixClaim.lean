import OAI.Hierarchy.DescentDatedBranchEvents
import OAI.Hierarchy.DescentRegisterTimelineCore

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}

namespace RegisterTimeline
/-- A property of a specific branch prefix, the genuine numerical register there and its memory. -/
abbrev PrefixClaim (t : RunTrace G q ε S k wire hist final bits d) (w : ℕ) :=
  ∀{W : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached W G q ε S k i z D wire hist},
    Path t.first r → Position → Memory w → Prop
end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
