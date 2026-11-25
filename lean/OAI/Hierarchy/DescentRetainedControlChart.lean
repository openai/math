import OAI.Hierarchy.DescentRotorWindowSize
import OAI.Hierarchy.DescentRetainedOverlapSize

namespace OAI
/-! # Address chart for the sorted donor selector and the fixed-width retile -/
namespace Hierarchy.DescentRetainedControl
open DescentSIMDLookup
noncomputable section
structure Layout where
  hosts : ℕ
  groups : ℕ
  targets : ℕ
  donors : ℕ
  degree : ℕ
  cap : ℕ
  field : ℕ
  bits : ℕ
  oldLanes : ℕ
  lanes : ℕ
namespace Layout
variable (s : Layout)
def rootWidth:=s.field*DescentRotorWindowArchive.count s.degree s.donors s.cap
def selectorBits:=Nat.clog 2 (s.donors+1)*s.donors
def stripBits:=s.bits*s.donors
def rows:=s.hosts*chunks s.groups s.oldLanes
def installed (base : ℕ) :=base+s.targets*(2*2^(s.rootWidth*s.oldLanes))
def temporary (base : ℕ) :=s.installed base+s.targets*s.rows+2^Nat.clog 2 s.rows
def temp (base : ℕ) (target : Fin s.targets) : ProtocolRAM.Bank :=
  ⟨s.installed base+target.val*s.rows,Nat.clog 2 s.rows⟩
def received (base : ℕ) :=s.temporary base+s.targets*DescentResetRetainedSetup.Layout.counts s.hosts s.groups s.oldLanes s.lanes s.selectorBits
def aperture:=max s.bits s.stripBits+s.selectorBits
def endAddress (base : ℕ) :=s.received base+(2*s.targets)*(2*2^(s.aperture*s.lanes))
theorem translate (base : ℕ) : s.endAddress base=base+s.endAddress 0:=by
  simp only [endAddress,received,temporary,installed,Nat.zero_add,Nat.add_assoc]

end Layout
end
end Hierarchy.DescentRetainedControl

end OAI
