import OAI.Hierarchy.DescentDatedOrdinaryVenueModel
import OAI.Hierarchy.DescentDyadicSheetEnd

namespace OAI
/-! # The real peer, hub, actor, funded, and signed pages fit into their successor date -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSIMDLookup DescentDyadicSpan
noncomputable section
theorem complete_page (s:SignedExtent)(base:ℕ)(x:Fin s.blocks)(j:Fin (2*s.cap)):
    (s.page base x j).base+(s.page base x j).size ≤ s.roof base ∧
      s.hosts*chunks s.groups s.lanes≤(s.page base x j).size:=by
  let p:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
  let r:=DescentOrdinarySignedAll.Tail p s.blocks s.candidates s.fieldBits s.lanes s.hosts s.groups
  let n:=s.hosts*chunks s.groups s.lanes
  let begin_:=DescentNextSignedWindow.Native.All.outputBase (DescentResetWindowTail.next r s.fieldBits s.lanes)
    s.cap s.fieldBits s.lanes
  let q:=finProdFinEquiv (x,j)
  rw [←s.calibrated base]
  change begin_+q.val*span n+span n≤begin_+(s.blocks*(2*s.cap))*span n ∧ n ≤ span n
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact ⟨Nat.add_le_add_left (Nat.mul_le_mul_right _ q.isLt) _,span_ge n⟩
end
end Hierarchy.DescentDatedAddressBook.SignedExtent

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentDyadicSpan ProtocolRAM
open DescentOrdinaryRasterReturn DescentVenueQuantityPlanes
open StageVenueTail hiding span
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F](v:PhysicalOrdinary F P)(floor:ℕ)
local notation "area_" => v.area
local notation "d" => v.venue
local notation "p" => v.materialEnd floor
local notation "B" => v.reachedSources floor
local notation "dim" => OrdinaryRaster.dims (area_) d v.rasterLanes
local notation "raw" => OrdinaryRaster.sweep (area_) d v.rasterLanes (v.endAddress floor)

theorem reached_space {w:ℕ}(blocks:(d).k=v.k)(align:v.signed.blocks=2^v.k)(cap:v.signed.cap=(d).cap)
    (hosts:v.signed.hosts=(d).hosts)(groups:v.signed.groups=(d).groups)(pitch:v.signed.lanes=(d).signedLanes)
    (actor:(d).aliveLanes=(d).paidLanes)(space:v.venueEnd floor<2^w):
    (d).Space (B) (v.rasterEnd floor) w:=by
  have upper:v.rasterEnd floor≤v.venueEnd floor:=by
    rw [venueEnd,(d).translates];exact Nat.le_add_right ..
  have before:=upper.trans_lt space
  have old:v.signedEnd floor≤v.refsStart floor:=Nat.le_add_right ..
  have refs_before_birth:v.refsStart floor≤v.birthStart floor:=Nat.le_add_right ..
  have born:v.birthStart floor≤v.vectorStart floor:=by rw [vectorStart,v.bornBook.affine];exact Nat.le_add_right ..
  have resolved:v.normalizedEnd floor≤v.endAddress floor:=by rw [endAddress,v.resolver.affine];exact Nat.le_add_right ..
  have raster:v.endAddress floor≤v.rasterEnd floor:=by
    rw [rasterEnd,OrdinaryRaster.translated];exact Nat.le_add_right ..
  have signedTop :=old.trans (refs_before_birth.trans (born.trans ((v.vector_before floor).trans ((v.routed_le floor).trans (resolved.trans raster)))))
  have peersTop: v.peerTail floor≤v.rasterEnd floor:=(v.signed_stage_paid floor).2.2.trans signedTop
  have safe (b:Bank)(h:b.base+b.size≤v.rasterEnd floor):b.Fits w (v.rasterEnd floor):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (h.trans_lt before),h⟩
  have peer: (B).roster.base+(B).roster.size≤v.peerTail floor:=by
    change DescentOrdinaryPeerRows.endAddress p (area_).H (area_).D (d).hosts (d).degree≤v.peerTail floor
    change _≤(DescentOrdinaryPeerRows.endAddress p (area_).H (area_).D (d).hosts (d).degree+1+2*span (d).hosts)+span (d).hosts
    omega
  have paidAt:second dim raw≤v.rasterEnd floor:=by
    rw [v.reachedEnd]
    change second dim raw≤State.roof (DescentOrdinaryRasterReturn.actor dim) (second dim raw)
    rw [State.shift]
    exact Nat.le_add_right ..
  have slice (x:Fin (2^(d).k)):
      x.val*((d).hosts*chunks (d).groups (d).paidLanes)+span ((d).hosts*chunks (d).groups (d).paidLanes)≤
        span (2^v.k*((d).hosts*chunks (d).groups (d).paidLanes)):=
    DescentDyadicSpan.slice v.k _ (x.cast (congrArg (fun n=>2^n) blocks))
  refine ⟨safe _ (peer.trans peersTop),span_ge _,safe _ peersTop,span_ge _,?_,?_,?_,space⟩
  · intro x j
    let low:=x.cast ((congrArg (fun n=>2^n) blocks).trans align.symm)
    let slot:=j.cast (congrArg (2*·) cap.symm)
    change (v.reachedWire floor low.val slot.val).Fits w _ ∧ _≤(v.reachedWire floor low.val slot.val).size
    rw [v.reachedWire_at]
    obtain ⟨ends_,rows⟩:=v.signed.complete_page (v.markEnd floor) low slot
    exact ⟨safe _ (ends_.trans signedTop),by simpa only [hosts,groups,pitch] using rows⟩
  · intro x
    refine ⟨safe _ (LE.le.trans ?_ paidAt),span_ge _⟩
    change State.out dim (first dim raw)+x.val*((d).hosts*chunks (d).groups (d).paidLanes)+span _≤
      State.out dim (first dim raw)+span (2^v.k*((d).hosts*chunks (d).groups (d).paidLanes))
    rw [Nat.add_assoc];exact Nat.add_le_add_left (slice x) _
  · intro x
    refine ⟨safe _ ?_,?_⟩
    · change State.out (DescentOrdinaryRasterReturn.actor dim) (second dim raw)+x.val*((d).hosts*chunks (d).groups (d).paidLanes)+span _≤
        State.out (DescentOrdinaryRasterReturn.actor dim) (second dim raw)+span (2^v.k*((d).hosts*chunks (d).groups (d).paidLanes))
      rw [Nat.add_assoc];exact Nat.add_le_add_left (slice x) _
    · rw [actor];exact span_ge _

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
