import OAI.Hierarchy.DescentRecordedVenueGeometry
import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentExteriorStaticHops

namespace OAI
/-! # The permanent date uses the precise shape, capacities, pitches and host order of its reached reset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentDatedAddressBook DescentExteriorReplay.HopTables
open DescentResetHostSize DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {old:Reached W G q ε S k i z D wire hist} (B:ClosedReset old ctl)
  (p drift degree payload e previous receiverM nextM packet:ℕ)(prior:ResetOutput.Prior)
local notation "v" => ResetOutput.fromBoard G S ctl.board k tail i p f g drift degree payload e previous receiverM nextM C packet prior
local notation "schedule" => capCalendar G.b S.rounds g S.height
local notation "H" => S.hostSize (i+1)
local notation "H₀" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "K" => B.reset.k-B.terminals.commonDepth
local notation "funded" => (v 0).venue.census
/-- The cap prefix is the original public cap calendar. The old reached header
provides its degree, block exponent and host envelope. -/
theorem named_venue (base:ℕ) (slots:prior.venue.degree=D)(blocks:prior.venue.k=k)
    (oldHosts:prior.venue.hosts=H₀)(cap:old.placement.cap=((schedule).take i).prod*256):
    (v base).venue=calibrated B funded H₀ H (2^e) (2^e) receiverM nextM prior.venue.paidBits:=by
  have shapes:(DescentDenseHostOrder.roster ctl.board k Ht).card=(DescentDenseHostOrder.roster B.reset.graph K Ht).card:=(reset_public B).1.symm
  change (⟨funded,
    ⟨(DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound prior.venue.degree n f g)).card,prior.venue.hosts,H,
      S.groupCount (i+1),2^k,prior.venue.paidBits,2^e,receiverM⟩,
    ⟨prior.venue.k,H,S.groupCount (i+1),3,2^g*(((schedule).take i).prod*256),prior.venue.paidBits,
      receiverM,receiverM,receiverM,nextM⟩,2^e⟩:ResetVenue)=_
  rw [slots,shapes,oldHosts,blocks,←cap,←B.next_capacity]
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentVenueQuantityPlanes
variable (v:ResetVenue)(B:Earlier)(base:ℕ)
theorem RunRoom.actual {w:ℕ}(room:(v).RunRoom B base 0 w)(N:ℕ)
    (slots:N≤B.ranks.inverse.size)(fits:N<2^w):(v).RunRoom B base N w:=
  ⟨{room.paid with inverseSize:=slots,usedFit:=fits},{room.actors with inverseSize:=slots,usedFit:=fits},
    room.roster,room.peerEnd,room.return_⟩
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI
