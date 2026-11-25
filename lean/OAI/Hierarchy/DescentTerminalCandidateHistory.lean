import OAI.Hierarchy.DescentTerminalCandidateType

namespace OAI
/-! # The original history pins inside the complete terminal candidate -/
namespace Hierarchy.DescentTerminalFullPins
variable {K W q piece rows : ℕ}

def history {old:Type} : old→Candidate old K W q piece rows := fun v=>.inl (.inl v)

end Hierarchy.DescentTerminalFullPins

end OAI
