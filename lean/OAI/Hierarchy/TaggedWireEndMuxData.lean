import OAI.Hierarchy.TaggedWirePublicSlab
import OAI.Hierarchy.ProbeReportSockets

namespace OAI
/-! # Selecting the chronological, private or paid output of an original role -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open AdaptiveProbe ReportSockets TaggedShorterSupergroups

variable {h W k attempts H : ℕ} (S : PurchaseSampler)
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)

/-- Each original history role has a fixed source in the branch input.
The retained output is addressed by original public free/link ordinal and side,
or by permanent stage/group and socket (with the dynamic native tag handled
once in the controller and in the candidate bank). -/
def publicData (previous : Public S h W k attempts→ℕ→Bool)
    (privateBits : Free S h (2^W) k→Bool→ℕ→Bool)
    (positiveBits : Fin dir.groups×Fin H→ℕ→Bool) :
    Bool → Public S h W k attempts → ℕ→Bool
  | false,p=>previous p
  | true,.inl (.inl (f,side))=>privateBits f side
  | true,.inl (.inr x)=>positiveBits (packed dir x)
  | true,.inr _=>fun _=>false

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
end

end OAI
