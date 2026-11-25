import OAI.Hierarchy.DescentDatedResetVenue
import OAI.Hierarchy.DescentVenueQuantityAny
import OAI.Hierarchy.DescentStageVenueAny

namespace OAI
/-! # A total reset return from the published sparse census to the next venue -/
namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

structure Earlier where
  actor : Bank
  ranks : DescentCompactVenuePeers.Inputs
  signed : ℕ→ℕ→Bank
  tag : ℕ→Bool

variable (v:ResetVenue)(B:Earlier)(base:ℕ)
def original:Bank:=⟨v.census.out base,Nat.clog 2 (v.census.jobs*v.census.rows)⟩
def paidLayout := DescentVenueQuantityPlanes.State.layout v.dense (v.denseStart base) (v.original base) B.ranks.count B.ranks.inverse
def actorLayout := DescentVenueQuantityPlanes.State.layout v.actorDims (v.actorStart base) B.actor B.ranks.count B.ranks.inverse

def sheet (p:DescentVenueQuantityPlanes.Dims)(l:DescentVenueQuantityPlanes.Layout)(b:ℕ):Bank:=
  ⟨l.out+b*(p.hosts*chunks p.groups p.lanes),Nat.clog 2 (p.hosts*chunks p.groups p.lanes)⟩

def sources:StageVenueTail.Sources:=
  ⟨DescentCompactVenuePeers.peers (v.peerStart base) v.rawHosts v.dense.hosts,
   DescentCompactVenuePeers.hubs (v.peerStart base) v.rawHosts v.dense.hosts,
   sheet v.actorDims (v.actorLayout B base),sheet v.dense (v.paidLayout B base),B.signed⟩

def phase (w:ℕ):NativePhase w:=
  (((DescentVenueQuantityPlanes.phase v.dense (v.paidLayout B base) w).seq
    (DescentVenueQuantityPlanes.phase v.actorDims (v.actorLayout B base) w)).seq
    (DescentCompactVenuePeers.phase B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag)).seq
    (v.next.phase (v.sources B base) (v.venueStart base) w)

structure RunRoom (used w:ℕ):Prop where
  paid:DescentVenueQuantityPlanes.Room v.dense (v.paidLayout B base) used w
  actors:DescentVenueQuantityPlanes.Room v.actorDims (v.actorLayout B base) used w
  roster:DescentCompactVenuePeers.Room B.ranks (v.peerStart base) w
  peerEnd:v.venueStart base<2^w
  return_:v.next.Space (v.sources B base) (v.venueStart base) w

theorem any {used w:ℕ}(m:Memory w)(fit:v.RunRoom B base used w):
    (v.phase B base w).Runs m ∧ ∀x,x<v.denseStart base ∨ v.endAddress base≤x→(v.phase B base w).image m x=m x:=by
  let pay:=DescentVenueQuantityPlanes.phase v.dense (v.paidLayout B base) w
  let actor:=DescentVenueQuantityPlanes.phase v.actorDims (v.actorLayout B base) w
  let chart:=DescentCompactVenuePeers.phase B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag
  let ret:=v.next.phase (v.sources B base) (v.venueStart base) w
  obtain ⟨rp,fp⟩:=DescentVenueQuantityPlanes.any v.dense (v.paidLayout B base) m fit.paid
  obtain ⟨ra,fa⟩:=DescentVenueQuantityPlanes.any v.actorDims (v.actorLayout B base) (pay.image m) fit.actors
  obtain ⟨rc,fc⟩:=DescentCompactVenuePeers.any B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag
    (actor.image (pay.image m)) fit.roster fit.peerEnd
  obtain ⟨rr,fr⟩:=v.next.any (v.sources B base) (v.venueStart base) (chart.image (actor.image (pay.image m))) fit.return_
  have parts:=v.steps base
  have after:=v.after base
  have fits₁:(v.paidLayout B base).out+DescentVenueQuantityPlanes.State.newRows v.dense≤v.actorStart base:=
    Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have fits₂:(v.actorLayout B base).out+DescentVenueQuantityPlanes.State.newRows v.actorDims≤v.peerStart base:=
    Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  refine ⟨((pay.seq actor).seq chart).seq_runs ret m (((pay.seq actor).seq_runs chart m (pay.seq_runs actor m rp ra) rc)) rr,?_⟩
  intro x away
  have densePeer := parts.1.trans parts.2.1
  have peerEnd := parts.2.2.trans after.2.2
  apply (fr x (away.imp_left (fun lo => lo.trans_le after.2.1))).trans
  apply (fc x (away.imp (fun lo => lo.trans_le densePeer) (fun hi => after.2.2.trans hi))).trans
  apply (fa x (away.imp (fun lo => lo.trans_le parts.1) (fun hi => fits₂.trans (peerEnd.trans hi)))).trans
  exact fp x (away.imp_right (fun hi => fits₁.trans (parts.2.1.trans (peerEnd.trans hi))))

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI
