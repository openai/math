import OAI.Hierarchy.ProbeFixedWideRoleStart
import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.TaggedWireWideSocketDirectory
import OAI.Hierarchy.TaggedWireRoleTurnBoard

namespace OAI
/-! # The fixed native terminal board at the retained public socket charts -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard HistoryRoles RoleProgram
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "ownerBase" => v.wideRoleStart h width (v.fixedTerminalStock P h width) (v.widePaidSlices h width bits)

def wideTerminalBoard (workStart : ℕ) :=
  RoleRoom.turnBoard («R»:=R) v.sampler dir (edges:=(P).catalogue.rows) ownerBase workStart (P).catalogue.core (v.widePaidPorts h width ownerBase)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
