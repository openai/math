import OAI.Hierarchy.DescentPhysicalResetStemEntry
import OAI.Hierarchy.DescentPhysicalTrunkHeader
import OAI.Hierarchy.DescentResetStemDateSignature

namespace OAI
/-! # The projected stem job used by the physical calendar front -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetStemDateSignature DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def job (v : CandidateFront) (s : v.StemInputs) : StemJob :=
  ⟨v.peer.oldDegree,v.stemField,v.metaBits,v.oldTicketCount,v.peer.oldHosts,v.newHosts,
   v.peer.groups,v.blocks,v.oldLanes,v.peer.lanes,v.signedQueries,s.parse,s.side,s.operands,s.ports⟩

theorem job_extent (v : CandidateFront) (base : ℕ) (s : v.StemInputs) :
    (v.job s).extent (v.parentEnd base) (v.parent base).base=v.mixed base :=
  v.stem_boundary s base

theorem job_output (v : CandidateFront) (base : ℕ) (s : v.StemInputs) :
    (v.job s).outputBase (v.parentEnd base) (v.parent base).base=v.stemOutput base := rfl

theorem received_job (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ}
    (space : v.SceneRoom base s w) (m : Memory w) :
    (v.received base s space).image m=
      (v.job s.stems).image (v.parentEnd base) (v.parent base).base (v.stemEntry base s space m) :=
  v.received_from_entry base s space m

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
