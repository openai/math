import OAI.Hierarchy.DescentPhysicalResetTrunkScene

namespace OAI
/-! # The actual clock and text of the reset trunk date -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentSixParty.Chronology DescentStaticWordColumn
noncomputable section
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene) {w : ℕ} (room : v.SceneRoom floor s w)

theorem trunkScene_price :
    let n:=v.newHosts*chunks v.peer.groups v.peer.lanes
    let pages:=3*2^(DescentResetTrunkIssue.width v.metaBits v.peer.lanes)
    let earlier:=v.received floor s room
    let result:=v.trunkScene floor s room
    result.ticks≤earlier.ticks+(46+108*v.newHosts+124*n+10*pages) ∧
      names result.program≤names earlier.program+(15*(2*v.newHosts+4*n+4)+350+15*(pages+1)) ∧
      v.trunkEnd floor≤v.mixed floor+(4*v.newHosts+6*n+5)+pages:=by
  intro n pages earlier result
  let suffix:=DescentResetTrunkCompactProgram.phase w (v.mixed floor) v.newHosts v.peer.hosts
    v.peer.groups v.peer.lanes v.metaBits (v.trunkBanks floor s)
  have bound:=DescentResetTrunkCompactProgram.price w (v.mixed floor) v.newHosts v.peer.hosts
    v.peer.groups v.peer.lanes v.metaBits (v.trunkBanks floor s)
  refine ⟨Nat.add_le_add_left bound.1 earlier.ticks,?_,bound.2.2⟩
  change names (earlier.program.seq suffix.program)≤_
  rw [names_seq]
  exact Nat.add_le_add_left bound.2.1 _

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
