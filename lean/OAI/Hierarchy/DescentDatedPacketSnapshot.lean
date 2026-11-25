import OAI.Hierarchy.DescentPublicOperandDateRead
import OAI.Hierarchy.DescentOperandInputsBeforePair

namespace OAI
/-! # Original dated operand setup and post-packet read snapshots -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "recv" => (v).receiver
local notation "start" => (v).sheetsStart b
local notation "chart" => (v).setup
local notation "base" => (v).operandFloor b

/-- The actual control-register stage follows the two candidates, the true
rank book and the signed-field renderer. -/
def beforeSetupImage (ok : u.Ready) (atActors : Memory w) : Memory w :=
  let q:=u.sectors
  let rows:=DescentResetCandidatePair.memory start q.pageBits (recv).hosts (recv).groups (recv).lanes
    q.header q.original (u.sheetsEntry ok atActors)
  let ranks:=(v).linkedRankInputs q start
  let archived:=((v).rankBook ranks b).memory (((v).rankPortPhase b w).image rows)
  let rendered:=(v).renderMemory ((v).renderFromRanks ranks b) b u.degree archived
  ((v).controlPhase b u.bank w).image rendered

theorem before_setup_sources (ok : u.Ready) (atActors : Memory w) :
    u.beforePacketImage ok atActors=((chart).sources base w u.bank).image (u.beforeSetupImage ok atActors) :=rfl

/-- Both the live compact parent IDs and the word-aligned capacity of that
array precede their respective protected write windows. -/
theorem parent_room (ok : u.Ready) :
    let front:=(v).front
    let parent:=(front.parent ((v).actorEnd b)).base
    parent+front.newHosts≤(v).trunkEnd b ∧
    parent+DescentDyadicSpan.span front.newHosts≤(chart).placed base := by
  intro front parent
  have first:=front.front_order ((v).actorEnd b)
  have gather:=DescentResetTrunkCompactProgram.grow (front.mixed ((v).actorEnd b)) front.newHosts
    front.peer.groups front.peer.lanes
  have last : front.gathered ((v).actorEnd b)≤(v).trunkEnd b:=Nat.le_add_right ..
  have directory:=first.2.2.trans (first.2.1.trans (gather.trans last))
  obtain ⟨_,_,_,mass,joint,priv,masked,sheets,_⟩:=ok.ordered
  exact ⟨(Nat.add_le_add_left (DescentDyadicSpan.span_ge front.newHosts) parent).trans directory,
    directory.trans (mass.trans (joint.trans (priv.trans (masked.trans (sheets.trans (u.sheets_le_packet ok))))))⟩

theorem packet_result (ok : u.Ready) (atActors : Memory w) :
    (chart).packets.image ((chart).placed base) (u.beforePacketImage ok atActors)=
      (chart).packetMemory base u.bank (u.beforeSetupImage ok atActors) :=rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
