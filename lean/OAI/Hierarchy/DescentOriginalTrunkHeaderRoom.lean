import OAI.Hierarchy.DescentPhysicalTrunkHeader
import OAI.Hierarchy.DescentPhysicalResetSceneInputs

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open ProtocolRAM
noncomputable section

theorem original_scalar (v : CandidateFront) (base : ℕ) (old : v.Originals base) (flags count inv : Bank)
    {w : ℕ} (before : v.parentStart base<2^w) :
    ((v.fromOriginals base old flags count inv).rawHeader).Fits w (v.peer.endAddress (v.peers base)) :=
  v.physical_trunk_fits base ((Nat.le_add_right (v.peer.endAddress (v.peers base)) v.newHosts).trans_lt before)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
