import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentDatePortHeaderRoom
import OAI.Hierarchy.DescentReachedOrdinaryVenueSpace
import OAI.Hierarchy.DescentResetPublicCuts
import OAI.Hierarchy.DescentResetVenueEnd

namespace OAI
/-! # Roster, hub and host count published by the two native successor programs -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDyadicSpan ProtocolRAM PhysicalOrdinary
noncomputable section

private theorem header_fit (b : Bank) {w roof : ℕ} (placed : b.base+b.size≤roof) (space : roof<2^w) :
    b.Fits w roof :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (placed.trans_lt space),placed⟩

theorem ordinary_header_room {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ)
    (space : v.returnedEnd floor<2^w) :
    (ordinary v floor).HeaderRoom w (v.returnedEnd floor) :=by
  have peersTop : v.peerTail floor≤v.rasterEnd floor:=by
    have old:v.signedEnd floor≤v.refsStart floor:=Nat.le_add_right ..
    have toBirth:v.refsStart floor≤v.birthStart floor:=Nat.le_add_right ..
    have born:v.birthStart floor≤v.vectorStart floor:=by rw [vectorStart,v.bornBook.affine];exact Nat.le_add_right ..
    have resolved:v.normalizedEnd floor≤v.endAddress floor:=by rw [endAddress,v.resolver.affine];exact Nat.le_add_right ..
    have raster:v.endAddress floor≤v.rasterEnd floor:=by
      rw [rasterEnd,StageVenueTail.OrdinaryRaster.translated];exact Nat.le_add_right ..
    have signedTop :=old.trans (toBirth.trans (born.trans ((v.vector_before floor).trans ((v.routed_le floor).trans (resolved.trans raster)))))
    exact (v.signed_stage_paid floor).2.2.trans signedTop
  let p:=v.materialEnd floor
  let H:=v.area.H
  let D:=v.area.D
  let R:=v.venue.hosts
  let E:=v.venue.degree
  let n:=DescentOrdinaryPeerRows.endAddress p H D R E
  have finish : v.rasterEnd floor≤v.returnedEnd floor:=by
    have start_:v.rasterEnd floor≤v.venueEnd floor:=by
      rw [PhysicalOrdinary.venueEnd,v.venue.translates];omega
    have «meta»:v.metaStart floor≤v.metaEnd floor:=by
      rw [PhysicalOrdinary.metaEnd,v.metadata.ordinary_translate];omega
    have op:v.metaEnd floor≤v.operandEnd floor:=by
      rw [PhysicalOrdinary.operandEnd,v.operandBook.affine];omega
    have tags : v.operandEnd floor≤v.primitiveEnd floor:=(v.primitive_spent _).2
    have end_ : v.primitiveEnd floor≤v.returnedEnd floor:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    exact start_.trans («meta».trans (op.trans (tags.trans end_)))
  have low : v.peerTail floor≤v.returnedEnd floor:=peersTop.trans finish
  have countEnd : (ordinary v floor).archive.count.base+(ordinary v floor).archive.count.size≤v.peerTail floor:=by
    change n+1≤(n+1+2*span R)+span R
    omega
  have peersEnd : (ordinary v floor).io.roster.base+(ordinary v floor).io.roster.size≤v.peerTail floor:=by
    change n≤(n+1+2*span R)+span R
    omega
  refine ⟨header_fit _ (countEnd.trans low) space,header_fit _ (peersEnd.trans low) space,?_,
    header_fit _ low space,?_⟩ <;> exact Nat.le_pow_clog (by decide) _

theorem reset_header_room {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (degree : a.successor.venue.next.degree=3)
    (hosts : a.successor.venue.next.hosts=a.successor.venue.dense.hosts)
    (space : a.endAddress floor<2^w) : (reset a floor u).HeaderRoom w (a.endAddress floor) :=by
  let v:=a.successor
  let b:=a.rebased floor
  let V:=v.venue
  let base:=v.fundedEnd b
  let H:=V.dense.hosts
  let ds:=v.actor.directory (v.middle.stop b)
  have cuts:=v.cuts b
  have actorBefore:v.actorEnd b≤a.endAddress floor:=cuts.trunk.trans (cuts.mass.trans
    (cuts.joint.trans (cuts.privateEnd.trans (cuts.meta.trans (cuts.originals.trans
      (cuts.candidates.trans (cuts.scalar.trans cuts.metadata)))))))
  have countEnd : ds.count.base+ds.count.size≤v.actorEnd b:=by
    change ds.first+2*ds.pitch+ds.sites+1≤ds.first+(4*ds.pitch+1+4*ds.sites)
    omega
  have venueBefore : V.venueStart base≤a.endAddress floor:=
    (V.after base).2.2.trans (v.venue_before_metadata b)
  have peerEnd : (reset a floor u).io.roster.base+(reset a floor u).io.roster.size≤V.venueStart base:=by
    change (DescentCompactVenuePeers.peers (V.peerStart base) V.rawHosts H).base+
      DescentCompactVenuePeers.span (3*H)≤_+DescentCompactVenuePeers.span H
    exact Nat.le_add_right ..
  have size (n:ℕ):n≤DescentCompactVenuePeers.span n:=
    (Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _)
  refine ⟨header_fit _ (countEnd.trans actorBefore) space,header_fit _ (peerEnd.trans venueBefore) space,?_,
    header_fit _ venueBefore space,?_⟩
  · change V.next.hosts*V.next.degree≤DescentCompactVenuePeers.span (3*H)
    change V.next.hosts=H at hosts
    change V.next.degree=3 at degree
    rw [degree,hosts,Nat.mul_comm H 3]
    exact size _
  · change V.next.hosts≤DescentCompactVenuePeers.span H
    exact hosts.le.trans (size H)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
