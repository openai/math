import OAI.Hierarchy.DescentPhysicalRecordedVenueRoom
import OAI.Hierarchy.DescentPhysicalFundedRoom

namespace OAI
/-! # Directory and signed output bounds at the genuine handoff to the successor venue -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {a:PhysicalReset}{floor w:ℕ}(u:a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "fund" => (v).fundedEnd b
local notation "F₀" => (v).front
local notation "actor" => (v).actor
local notation "atActor" => (v).middle.stop b
local notation "next" => (v).actorEnd b
local notation "ds" => (actor).directory atActor
local notation "Q" => (v).venue.census
local notation "src" => FinalInputs.predecessor u

private theorem peer_end (s : CandidateFront) (base : ℕ) :
    s.peer.endAddress (s.peers base)≤ s.trunkEnd base :=by
  have parent:s.peer.endAddress (s.peers base)≤ s.parentStart base:=Nat.le_add_right ..
  have aperture:s.parentStart base≤ s.parentEnd base:=by unfold CandidateFront.parentEnd;rw [DescentResetParentAperture.extent];omega
  have proj:s.parentEnd base≤ s.projected base:=by unfold CandidateFront.projected;rw [DescentResetStemProject.extent];omega
  have mixed:s.projected base≤ s.mixed base:=by unfold CandidateFront.mixed;rw [DescentResetStemPackedIssue.Mixed.affine];omega
  have done_:s.mixed base≤ s.trunkEnd base:=(DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  exact parent.trans (aperture.trans (proj.trans (mixed.trans done_)))

/-- The third peer row can address its full dyadic span, including at zero hosts.
The threshold and palette already reserve this slack after the raw rows. -/
private theorem peer_page (p : PeerAperture) (base : ℕ) (j : Fin 3):
    p.rawPeers base+j.val*p.hosts+2^Nat.clog 2 p.hosts≤p.endAddress base:=by
  have live:p.rawPeers base+3*p.hosts=p.three base:=rfl
  have three:p.three base≤p.threshold base:=by
    unfold PeerAperture.threshold PeerAperture.self
    rw [DescentResetSelfPortsRAM.extent]
    omega
  have row:=Nat.mul_le_mul_right p.hosts j.isLt.le
  have pad:2^Nat.clog 2 p.hosts=DescentDyadicSpan.span p.hosts:=rfl
  unfold PeerAperture.endAddress
  omega

/-- All physical predecessor pages, with the complete predecessor signed-row bound. -/
theorem DateInputs.prior_venue_pages_at (limit : ℕ) (after_ : (v).finalEnd b≤limit) (ready:u.Ready) (jobs:(Q).jobs=(actor).shapes)
    (sites:(Q).hosts=(actor).hosts) (waves:(Q).groups=(actor).groups) (space:limit<2^w):
    (src).actor.Fits w limit ∧
    (Q).jobs*(Q).hosts*chunks (Q).groups (actor).lanes≤(src).actor.size ∧
    DescentCompactVenuePeers.Room (src).ranks limit w ∧
    (v).receiver.rendered ((v).fieldsEnd b)≤limit:=by
  obtain ⟨_,_,ab,bc,cd,de,ef,fg,gh⟩:=ready.ordered
  have booked:(v).finalEnd b≤limit:=after_
  have paid:(v).trunkEnd b≤limit:=by omega
  have old:next≤limit:=ab.trans paid
  have enough {q:Bank} {n:ℕ} (f:q.Fits w n) (h:n≤limit):q.Fits w limit:=⟨f.1,f.2.1,f.2.2.trans h⟩
  have ranges:=(ds).fits (old.trans_lt space)
  have scratch:(ds).scratch≤(ds).endAddress:=by
    dsimp only [DescentResetNewActorDirectory.Layout.scratch,DescentResetNewActorDirectory.Layout.endAddress,
      DescentResetNewActorDirectory.Layout.size]
    omega
  refine ⟨enough (DateInputs.prior_actor_bank (a:=a) ready) old,?_,?_,?_⟩
  · rw [jobs,sites,waves,Nat.mul_assoc]
    exact (actor).extent_scene atActor
  · refine ⟨enough ranges.2.2.2.1 old,enough ranges.2.2.2.2 old,enough ranges.2.2.1 (scratch.trans old),?_⟩
    intro j
    let p:=(F₀).peer
    let base:=(F₀).peers next
    have end_:p.rawPeers base+j.val*p.hosts+2^Nat.clog 2 p.hosts≤limit:=
      (peer_page p base j).trans ((peer_end (F₀) next).trans paid)
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt space),end_⟩
  · have lim:=(v).receiver.occupied ((v).fieldsEnd b)
    have finish:(v).receiver.endAddress ((v).fieldsEnd b)≤(v).endAddress b:=by rw [(v).scalar_original_extent];omega
    exact lim.2.1.trans (lim.2.2.trans (finish.trans (((v).final_ge b).trans booked)))

theorem DateInputs.prior_venue_pages (ready:u.Ready) (jobs:(Q).jobs=(actor).shapes)
    (sites:(Q).hosts=(actor).hosts) (waves:(Q).groups=(actor).groups) (space:fund<2^w):
    (src).actor.Fits w fund ∧
    (Q).jobs*(Q).hosts*chunks (Q).groups (actor).lanes≤(src).actor.size ∧
    DescentCompactVenuePeers.Room (src).ranks fund w ∧
    (v).receiver.rendered ((v).fieldsEnd b)≤fund:=
  u.prior_venue_pages_at fund ((v).funded.room _) ready jobs sites waves space

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
