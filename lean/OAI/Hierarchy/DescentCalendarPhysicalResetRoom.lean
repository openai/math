import OAI.Hierarchy.DescentPhysicalVenuePredecessor
import OAI.Hierarchy.DescentNamedPriorVenueRoom
import OAI.Hierarchy.DescentNamedRoleRooms
import OAI.Hierarchy.DescentNamedResetAtlas

namespace OAI
/-! # Complete resource proof for the terminal stages of the public reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands) (floor : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "start_" => (a).stageStart floor
local notation "b" => (a).rebased start_
local notation "v" => (a).successor
local notation "old" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "fund" => (v).fundedEnd b
variable {w : ℕ}

/-- On the selected calendar all funding, role, birth and venue phases have native
room as soon as the incoming stage buffers fit and the dated address budget fits. -/
theorem named_final_room {u : (a).DateInputs start_ w} (z : u.FinalInputs)
    (shape : (a).RootShape) (ready : u.Ready)
    (hosts : venue.hosts=S.hostSize age) (blocks : venue.k=k)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within_ : age<S.length) (positive : 0<M)
    (root : u.roots.field=(v).middle.rootField)
    (atoms : ∀j,(z.earlier j).Fits w start_) (roles : ∀j,(z.previousRoles j).Fits w start_)
    (ceiling : (a).fullEnd floor<2^w) : z.Room:=by
  obtain ⟨selected,jobs,sites,waves,stockBlocks,joined,lanes⟩:=
    ResetOutput.venue_faces G S board k tail age p f g drift degree payload e previous M nextM C packet (old) b hosts blocks groups radix within_ positive
  obtain ⟨_,one,trunk,fail⟩:=
    ResetOutput.funded_shape G S board k tail age p f g drift degree payload e previous M nextM C packet (old) b
  obtain ⟨placed,birthLanes,birthBlocks⟩:=
    ResetOutput.birth_shape G S board k tail age p f g drift degree payload e previous M nextM C packet (old) b blocks positive
  obtain ⟨moveLanes,moveBlocks⟩:=
    ResetOutput.transfer_shape G S board k tail age p f g drift degree payload e previous M nextM C packet (old) b positive
  have endWord:(a).endAddress start_<2^w:=ceiling
  have move_:(v).fullEnd b≤(v).roleEnd b:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have class_:(v).roleEnd b≤(v).classEnd b:=by rw [ResetOutput.classEnd,(v).actorClass.translate];exact Nat.le_add_right ..
  have birth_:(v).classEnd b≤(v).birthEnd b:=by rw [ResetOutput.birthEnd,(v).birth.translate];exact Nat.le_add_right ..
  have used_:(v).birthEnd b≤(v).primitiveEnd b:=by rw [ResetOutput.primitiveEnd,(v).primitive.translate];exact Nat.le_add_right ..
  have total:(v).primitiveEnd b≤(a).endAddress start_:=by
    change _≤(v).metadata.endAddress ((v).primitiveEnd b)
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  have venueWord:(v).venue.endAddress fund<2^w:=by change (v).fullEnd b<_;omega
  have limit:=(v).venue.after fund
  have fromFund:fund<(2:ℕ)^w:=(limit.1.trans (limit.2.1.trans limit.2.2)).trans_lt venueWord
  obtain ⟨scene,dim,ranks,rendered⟩:=u.prior_venue_pages ready jobs sites waves fromFund
  have venueRoom:=u.venue_banks venue nextM selected stockBlocks joined lanes scene dim ranks rendered venueWord
  exact z.reached_room shape ready atoms roles venueRoom jobs one trunk (by rw [root];exact fail) placed birthLanes birthBlocks moveLanes moveBlocks endWord

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
