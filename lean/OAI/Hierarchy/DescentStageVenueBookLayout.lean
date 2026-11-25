import OAI.Hierarchy.DescentStageVenueDate
import OAI.Hierarchy.DescentPackedColumnSum
import OAI.Hierarchy.DescentScalarHaloPortROM
import OAI.Hierarchy.DescentVenueShape
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # Addresses of the three real packed successor banks and the halo directory -/
namespace Hierarchy.DescentActorRaster.Venue
noncomputable section

def outBase (base k M : ℕ) :=DescentPackedColumnSum.finish base (2^k) 1 M

end
end Hierarchy.DescentActorRaster.Venue

namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentActorRaster DescentSIMDLookup
noncomputable section

def span (n:ℕ) :=2^(Nat.clog 2 n)
def area (base k H G M:ℕ) :=Venue.outBase base k M+span (H*chunks G M)
def endAddress (base k H G M D:ℕ) :=DescentScalarHaloPortROM.stop H G M D (area base k H G M)

namespace Date
variable (d : Date)
local notation "r" => 2^d.k
local notation "p" => 2*d.cap
local notation "H" => d.hosts
local notation "G" => d.groups
local notation "M" => d.lanes

def signedShape : DescentVenueSlabs.Shape :=
  ⟨r*p,H,G,d.signedLanes,M,DescentSignedCableCodec.width d.degree d.cap⟩
def paidShape : DescentVenueSlabs.Shape:=⟨r,H,G,d.paidLanes,M,d.paidBits⟩
def aliveShape : DescentVenueSlabs.Shape:=⟨r,H,G,d.aliveLanes,M,1⟩
def firstEnd (base:ℕ):=DescentVenueSlabs.endAddress d.signedShape base
def secondEnd (base:ℕ):=DescentVenueSlabs.endAddress d.paidShape (d.firstEnd base)
def thirdEnd (base:ℕ):=DescentVenueSlabs.endAddress d.aliveShape (d.secondEnd base)
def endAddress (base:ℕ):=StageVenueTail.endAddress (d.thirdEnd base) d.k H G M d.degree

end Date
end
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
