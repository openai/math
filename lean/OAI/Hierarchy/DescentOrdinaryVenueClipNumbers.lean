import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentPackedActorMask
import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # Per-lane table widths and group-aligned pitch of the original ordinary receiver -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs
variable (s : Shape)
def bits := totalBits s+1*s.blocks
end Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs

namespace Hierarchy.DescentScalarVenueMask.Receiver
open DescentSharedCableNames
def unit (raw low n : ℕ) :=max (1+Packed.bits raw) (Packed.bits low*n+Packed.bits low)
end Hierarchy.DescentScalarVenueMask.Receiver

namespace Hierarchy.DescentOrdinaryVenueIngress
open DescentHaloWalkRAM DescentSIMDLookup DescentScalarVenueMask DescentRawCablePanel DescentSharedCableNames
noncomputable section

structure Chart where
  socket : DepotRAM.Shape
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  k : ℕ
  profile : ℕ
  gain : ℕ
  slots : ℕ
  names : ℕ

namespace Chart
variable (v : Chart)
def raw:=2^(v.k+1)*v.slots
def paths:=breadth v.socket.degree
end Chart

structure Clip where
  venue : Chart
  payload : ℕ
  panelPitch : ℕ
  actorPitch : ℕ
  consumerUnit : ℕ

namespace Clip
variable (c : Clip)
def actorCount:=DescentPackedActorMask.actors (c.venue.paths*c.venue.socket.blocks) c.venue.socket.cap
def fieldWidth:=Packed.bits c.venue.names*c.actorCount
/-- The complete per-row register, return query, raw path key, and full assembled actor mask each have a real LUT. -/
def localUnit:=max 2 (max (DepotRAM.ActorInputs.bits c.venue.socket) (max (Packed.bits c.venue.paths+1)
  (max (Packed.bits c.venue.raw) (Receiver.unit c.venue.raw c.venue.names c.actorCount))))
def unit:=max c.localUnit c.consumerUnit
def radix:=2^c.venue.k
/-- The native gather changes the previous `postPitch * radix` lanes into `postPitch` lanes. -/
def postPitch:=min (c.panelPitch/c.radix) (min (c.actorPitch/c.radix) (lanes c.payload ((2*c.unit)*c.radix)))
def working:=c.postPitch*c.radix

theorem working_fields : c.working≤c.panelPitch ∧ c.working≤c.actorPitch ∧
    c.working*c.unit≤c.payload/4 :=by
  have p : c.postPitch≤c.panelPitch/c.radix := Nat.min_le_left ..
  have a : c.postPitch≤c.actorPitch/c.radix := (Nat.min_le_right ..).trans (Nat.min_le_left ..)
  have q : c.postPitch≤lanes c.payload ((2*c.unit)*c.radix) := (Nat.min_le_right ..).trans (Nat.min_le_right ..)
  have cap:= (Nat.mul_le_mul_right ((2*c.unit)*c.radix) q).trans (lanes_fit c.payload ((2*c.unit)*c.radix))
  have eqn : c.postPitch*((2*c.unit)*c.radix)=2*(c.working*c.unit):=by unfold working;ring
  rw [eqn] at cap
  exact ⟨(Nat.mul_le_mul_right _ p).trans (Nat.div_mul_le_self ..),
    (Nat.mul_le_mul_right _ a).trans (Nat.div_mul_le_self ..),by omega⟩
end Clip
end
end Hierarchy.DescentOrdinaryVenueIngress

end OAI
