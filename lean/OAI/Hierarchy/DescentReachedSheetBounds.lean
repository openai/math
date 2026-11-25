import OAI.Hierarchy.DescentDyadicSheetEnd
import OAI.Hierarchy.DescentDatedResetVenueRun

namespace OAI
/-! # All dyadically addressed original slabs end inside the actual next phase -/
namespace Hierarchy.DescentVenueQuantityPlanes.State
open DescentSIMDLookup ProtocolRAM

theorem sheet_end (d:Dims)(base:ℕ)(old count inv:ProtocolRAM.Bank){k:ℕ}
    (size:d.blocks=2^k)(x:Fin (2^k)):
    let sheet:=DescentDatedAddressBook.ResetVenue.sheet d (layout d base old count inv) x.val
    sheet.base+sheet.size≤roof d base:=by
  change (out d base+x.val*(d.hosts*chunks d.groups d.lanes))+2^Nat.clog 2 (d.hosts*chunks d.groups d.lanes)≤
    out d base+2^Nat.clog 2 (d.blocks*(d.hosts*chunks d.groups d.lanes))
  rw [size,Nat.add_assoc]
  exact Nat.add_le_add_left (DescentDyadicSpan.slice k _ x) _
end Hierarchy.DescentVenueQuantityPlanes.State

namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentVenueQuantityPlanes DescentSIMDLookup ProtocolRAM
variable (v:ResetVenue)(B:Earlier)(base:ℕ)
theorem earlier_sheets {k:ℕ}(blocks:v.dense.blocks=2^k)(x:Fin (2^k)):
    ((v.sources B base).paid x.val).base+((v.sources B base).paid x.val).size≤v.actorStart base ∧
    ((v.sources B base).alive x.val).base+((v.sources B base).alive x.val).size≤v.peerStart base:=
  ⟨State.sheet_end v.dense (v.denseStart base) (v.original base) B.ranks.count B.ranks.inverse blocks x,
   State.sheet_end v.actorDims (v.actorStart base) B.actor B.ranks.count B.ranks.inverse blocks x⟩

/-- Only the signed predecessor pages enter this safety proof from outside the paid
    and actor directory pipeline. All other rows are the genuinely allocated outputs. -/
theorem next_space {w:ℕ}(blocks:v.dense.blocks=2^v.next.k)(hosts:v.next.hosts=v.dense.hosts)
    (groups:v.next.groups=v.dense.groups)(degree:v.next.degree=3)
    (paid:v.next.paidLanes=v.dense.lanes)(alive:v.next.aliveLanes=v.dense.lanes)
    (signed:∀(x:Fin (2^v.next.k))(j:Fin (2*v.next.cap)),(B.signed x.val j.val).Fits w (v.venueStart base) ∧
      v.next.hosts*chunks v.next.groups v.next.signedLanes≤(B.signed x.val j.val).size)
    (roof:v.endAddress base<2^w):v.next.Space (v.sources B base) (v.venueStart base) w:=by
  let H:=v.dense.hosts
  let R:=v.rawHosts
  let entry:=v.peerStart base
  have steps:=v.steps base
  have ceiling: v.venueStart base<2^w:=(v.after base).2.2.trans_lt roof
  have bankFit (p:Bank)(done_:p.base+p.size≤v.venueStart base):p.Fits w (v.venueStart base):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (done_.trans_lt ceiling),done_⟩
  have peerFit:(DescentCompactVenuePeers.peers entry R H).Fits w (v.venueStart base):=
    bankFit _ (Nat.le_add_right ..)
  have hubFit:(DescentCompactVenuePeers.hubs entry R H).Fits w (v.venueStart base):=
    bankFit _ le_rfl
  refine ⟨peerFit,?_,hubFit,?_,signed,?_,?_,roof⟩
  · rw [hosts,degree,Nat.mul_comm v.dense.hosts 3]
    exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  · rw [hosts]
    exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  · intro x
    have found:=v.earlier_sheets B base blocks x
    refine ⟨bankFit _ (found.1.trans (steps.2.1.trans steps.2.2)),?_⟩
    rw [hosts,groups,paid]
    exact Nat.le_pow_clog (by decide) _
  · intro x
    have found:=v.earlier_sheets B base blocks x
    refine ⟨bankFit _ (found.2.trans steps.2.2),?_⟩
    rw [hosts,groups,alive]
    exact Nat.le_pow_clog (by decide) _

theorem run_room {w:ℕ}(blocks:v.dense.blocks=2^v.next.k)(hosts:v.next.hosts=v.dense.hosts)
    (groups:v.next.groups=v.dense.groups)(degree:v.next.degree=3)
    (paid:v.next.paidLanes=v.dense.lanes)(alive:v.next.aliveLanes=v.dense.lanes)
    (positive:0<v.dense.lanes)
    (original:v.dense.shapes*v.dense.oldHosts*chunks (v.dense.groups*v.dense.blocks) v.dense.oldLanes≤v.census.jobs*v.census.rows)
    (actor:B.actor.Fits w base)
    (actorRows:v.dense.shapes*v.dense.oldHosts*chunks (v.dense.groups*v.dense.blocks) v.actorLanes≤B.actor.size)
    (prior:DescentCompactVenuePeers.Room B.ranks base w)
    (signed:∀(x:Fin (2^v.next.k))(j:Fin (2*v.next.cap)),(B.signed x.val j.val).Fits w (v.venueStart base) ∧
      v.next.hosts*chunks v.next.groups v.next.signedLanes≤(B.signed x.val j.val).size)
    (roof:v.endAddress base<2^w):v.RunRoom B base 0 w:=by
  have next:=v.next_space B base blocks hosts groups degree paid alive signed roof
  have hostWord:v.dense.hosts≤2^w:=hosts ▸ (next.hubSize.trans next.hub.2.1.le)
  have order:=v.steps base
  have dense₀:base≤v.denseStart base:=(v.after base).1
  have actor₀:base≤v.actorStart base:=dense₀.trans order.1
  have roster₀:base≤v.peerStart base:=actor₀.trans order.2.1
  have ceiling: v.venueStart base<2^w:=(v.after base).2.2.trans_lt roof
  have actorRoom:=order.2.2.trans_lt ceiling
  have paidRoom:=order.2.1.trans_lt actorRoom
  have origEnd:(v.original base).base+(v.original base).size=v.denseStart base:=rfl
  have origFit:(v.original base).Fits w (v.denseStart base):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (origEnd.le.trans_lt (order.1.trans_lt paidRoom)),origEnd.le⟩
  have fitAt (p:Bank){a:ℕ}(hp:p.Fits w base)(ha:base≤a):p.Fits w a:=⟨hp.1,hp.2.1,hp.2.2.trans ha⟩
  have bp:0<v.dense.blocks:=by rw [blocks];exact Nat.two_pow_pos _
  refine ⟨?_,?_,⟨fitAt _ prior.count roster₀,fitAt _ prior.inverse roster₀,
    fitAt _ prior.forward roster₀,fun j=>fitAt _ (prior.neighbor j) roster₀⟩,ceiling,next⟩
  · exact State.room v.dense _ _ _ _ origFit (fitAt _ prior.count dense₀) (fitAt _ prior.inverse dense₀)
      (original.trans (Nat.le_pow_clog (by decide) _)) (Nat.zero_le _) (Nat.two_pow_pos _) hostWord positive bp paidRoom
  · exact State.room v.actorDims _ _ _ _ (fitAt _ actor actor₀) (fitAt _ prior.count actor₀)
      (fitAt _ prior.inverse actor₀) actorRows (Nat.zero_le _) (Nat.two_pow_pos _) hostWord positive bp actorRoom

end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI
