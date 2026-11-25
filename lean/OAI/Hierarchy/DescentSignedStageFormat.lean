import OAI.Hierarchy.DescentSignedFeedWidths
import OAI.Hierarchy.DescentPublicDegreeNumbers

namespace OAI
/-! # The signed format at a real ordinary transition -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup DescentHaloWalkRAM DescentHostDegree
noncomputable section

/-- The actual old and new schedule coordinates used by the local and returned fields. -/
structure SignedStage where
  k : ℕ
  oldDegree : ℕ
  oldCap : ℕ
  newDegree : ℕ
  newCap : ℕ
  oldHosts : ℕ
  newHosts : ℕ
  groups : ℕ
  radix : ℕ
  colors : ℕ
  padding : ℕ
  deriving DecidableEq
namespace SignedStage
variable (q : SignedStage)

def localSlots := 2^packExponent 20 q.oldDegree+2
def hostPitch := (2^(q.k+1)-1)*q.localSlots
def lowSites := 2^(q.k+1)*q.localSlots
def residentSlots := 2^q.k*q.oldCap*11
def tickets := (breadth q.oldDegree+1)*q.residentSlots
def donorUnits := max (q.oldCap*q.radix) (q.colors+1+q.padding)

/-- The eleven original fields include a missing-path rank and one-based ticket codes. -/
def rawAlphabet :=
  let P:=breadth q.oldDegree
  P+1+q.lowSites+P*P*q.lowSites+q.tickets+(q.newCap+1)+2

def fieldBits :=
  Nat.clog 2 (q.rawAlphabet+(q.newDegree+2)+(2*q.newCap+2)+(q.donorUnits+1))

def template : SignedExtent :=
  ⟨2^q.k,q.oldHosts,q.newHosts,q.groups,0,q.oldDegree,q.residentSlots,q.lowSites,q.tickets,q.newCap,q.fieldBits⟩

/-- The material projector reads the entire old block vector before publishing one digit. -/
def unit := max q.template.feedUnit (q.fieldBits*2^q.k+q.fieldBits)

def format (payload : ℕ) : SignedExtent :=
  {q.template with lanes:=lanes payload q.unit}

theorem field_room :
    q.rawAlphabet≤2^q.fieldBits ∧ max (q.newDegree+1) (q.newCap+1)<2^q.fieldBits ∧
    breadth q.oldDegree*breadth q.oldDegree*q.lowSites≤2^q.fieldBits ∧
    q.tickets≤2^q.fieldBits ∧ q.donorUnits<2^q.fieldBits := by
  have fits:=Nat.le_pow_clog (by decide : 1<2) (q.rawAlphabet+(q.newDegree+2)+(2*q.newCap+2)+(q.donorUnits+1))
  change _≤2^q.fieldBits at fits
  have raw : breadth q.oldDegree*breadth q.oldDegree*q.lowSites≤q.rawAlphabet:=by
    dsimp only [rawAlphabet];omega
  exact ⟨by omega,max_lt (by omega) (by omega),by omega,by dsimp only [rawAlphabet] at *;omega,by omega⟩

theorem width (payload : ℕ) : (q.format payload).feedUnit≤q.unit :=
  le_max_left ..

theorem material_width (payload : ℕ) :
    ((q.format payload).fieldBits*(q.format payload).blocks+(q.format payload).fieldBits)*(q.format payload).lanes≤payload/2 := by
  have chip:=lanes_fit payload q.unit
  have part:=Nat.mul_le_mul_right (lanes payload q.unit)
    (le_max_right q.template.feedUnit (q.fieldBits*2^q.k+q.fieldBits))
  exact part.trans (show q.unit*lanes payload q.unit≤payload/2 by rw [Nat.mul_comm];exact chip)

theorem lanes_eq (payload : ℕ) : (q.format payload).lanes=lanes payload q.unit := rfl

theorem positive : 0<q.unit := by
  have l := show 32*(1+q.template.fieldBits+
      DescentSharedCableNames.Packed.bits q.template.oldKey+DescentSharedCableNames.Packed.bits q.template.shortPeerKinds+
      DescentSharedCableNames.Packed.bits q.template.reach+DescentSharedCableNames.Packed.bits q.template.lowSites+
      DescentSharedCableNames.Packed.bits (q.template.reach*q.template.lowSites))≤q.template.feedUnit from le_max_right ..
  have u : q.template.feedUnit≤q.unit := le_max_left ..
  omega

end SignedStage
end
end Hierarchy.DescentDatedAddressBook

end OAI
