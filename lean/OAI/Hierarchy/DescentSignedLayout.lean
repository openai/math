import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentSignedTableDimensions
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Public extent of the cross-indexed signed parent rank and renderer pages. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentHaloWalkRAM DescentSIMDLookup DescentDyadicSpan
open DescentParallelBase.ParentFilter
open Filter
open scoped Classical
noncomputable section

structure SignedExtent where
  blocks : ℕ
  priorHosts : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  degree : ℕ
  residentSlots : ℕ
  lowSites : ℕ
  tickets : ℕ
  cap : ℕ
  fieldBits : ℕ

namespace SignedExtent

def reach (s:SignedExtent):=breadth s.degree
def candidates (s:SignedExtent):=s.reach*s.residentSlots
def slab (s:SignedExtent):=s.hosts*chunks s.groups s.lanes
def directoryWords (s:SignedExtent):=3*span (s.priorHosts*(s.reach*s.reach))
def compareWidth (s:SignedExtent):=Fused.TablesROM.unit s.degree s.lowSites s.tickets s.cap s.fieldBits*s.lanes
def digitArea (s:SignedExtent):=s.fieldBits*s.lanes

def peerWords (s:SignedExtent):=2*2^(2*s.digitArea)
def converterWords (s:SignedExtent):=26*2^s.compareWidth+2*2^(11*s.digitArea)
def rankWords (s:SignedExtent):=4*2^(10*s.digitArea)+(s.blocks*3*s.candidates)*span s.slab
def formatterWords (s:SignedExtent):=32*2^(8*s.digitArea)
def outputWords (s:SignedExtent):=(8+2*s.cap)*2*2^(9*s.digitArea)+(s.blocks*(2*s.cap))*span s.slab
def signedBound (s:SignedExtent):=s.peerWords+s.converterWords+s.rankWords+s.formatterWords+s.outputWords

def coreRoof (s:SignedExtent) (base:ℕ):=base+s.directoryWords+s.signedBound
def oldRows (s:SignedExtent):=s.priorHosts*chunks s.groups s.lanes
def oldKey (s:SignedExtent):=s.reach*(s.lowSites*s.reach)
def routeTotal (s:SignedExtent):=s.reach*(s.lowSites*s.reach)
def peerKinds (s:SignedExtent):=(s.reach*s.reach)*s.lowSites
def jobsLocal (s:SignedExtent):=s.blocks*s.candidates
def jobsCompare (s:SignedExtent):=(s.blocks*3)*(s.candidates*(s.candidates+1))
def lookupArea (s:SignedExtent):=s.digitArea+s.fieldBits
def remoteArea (s:SignedExtent):=(DescentSharedCableNames.Packed.bits s.oldKey+s.fieldBits)*s.lanes
def flagArea (s:SignedExtent):=(s.fieldBits*11+1)*s.lanes
def shapeArea (s:SignedExtent):=(4+s.fieldBits*2)*s.lanes
def gateArea (s:SignedExtent):=(4+s.fieldBits)*s.lanes
def indexWords (s:SignedExtent):=
  span (s.hosts*(s.reach*s.reach))+s.lowSites*span s.oldRows+span s.slab+span s.slab+span s.priorHosts
def reverseArea (s:SignedExtent):=DescentSharedCableNames.Packed.bits s.reach*s.lanes
def reverseWords (s:SignedExtent):=
  let a:=DescentSharedCableNames.Packed.bits s.reach
  DescentPackedChildNeighbor.SIMD.ROM.cells s.reach a a s.lanes s.priorHosts s.groups+(span s.oldRows-s.oldRows)
def forwardArea (s:SignedExtent):=(DescentSharedCableNames.Packed.bits s.reach+DescentSharedCableNames.Packed.bits s.lowSites)*s.lanes
def backArea (s:SignedExtent):=(DescentSharedCableNames.Packed.bits (s.reach*s.lowSites)+DescentSharedCableNames.Packed.bits s.reach)*s.lanes
def shortPeerKinds (s:SignedExtent):=(s.reach*s.reach)*s.lowSites
def peerSelectionArea (s:SignedExtent):=DescentSharedCableNames.Packed.bits s.shortPeerKinds*s.lanes
def peerSelectionWords (s:SignedExtent):=
  2^(s.fieldBits*11*s.lanes)+DescentPackedChildNeighbor.SIMD.ROM.cells s.shortPeerKinds (DescentSharedCableNames.Packed.bits s.shortPeerKinds) s.fieldBits s.lanes s.hosts s.groups+(span s.slab-s.slab)
def peerDirectoryWords (s:SignedExtent):=
  let rows:=s.hosts*s.shortPeerKinds
  (5*rows+s.priorHosts+span (rows+1)+span (s.priorHosts+1))+span rows
def preparation (s:SignedExtent):=
  3*span (s.hosts*(s.reach*s.reach))
    +2*2^(2*s.digitArea)
    +DescentPackedChildNeighbor.SIMD.ROM.cells (s.reach*s.reach) s.fieldBits s.fieldBits s.lanes s.hosts s.groups
    +(s.jobsLocal*5)*span s.slab
    +(s.jobsLocal*11)*span s.slab
    +((s.jobsLocal*11)*s.lowSites)*span s.oldRows
    +(s.oldKey*2)*2^s.remoteArea
    +(s.jobsCompare*11)*span s.oldRows
    +26*2^s.compareWidth
    +4*2^s.flagArea
    +4*2^s.shapeArea
    +2*2^s.gateArea
    +s.indexWords+2*2^s.forwardArea+2*2^s.backArea+(span s.slab-s.slab)+s.reverseWords+s.peerSelectionWords+s.peerDirectoryWords
/-- Word immediately following every physical ordinary signed publication. -/
def roof (s:SignedExtent) (base:ℕ):=s.coreRoof base+s.preparation
theorem shift (s:SignedExtent) (base:ℕ):s.roof base=base+s.roof 0:=by simp [roof,coreRoof,Nat.add_assoc]
theorem room (s:SignedExtent) (base:ℕ):base ≤ s.roof base:=by unfold roof coreRoof;omega

variable {ι:ℕ→Type*}
structure ScalarRoom (s:∀h,ι h→SignedExtent):Prop where
  blocks:Bounded (fun h i=>(s h i).blocks)
  oldHosts:Bounded (fun h i=>(s h i).priorHosts)
  reach:Bounded (fun h i=>(s h i).reach)
  slots:Bounded (fun h i=>(s h i).residentSlots)
  rows:Bounded (fun h i=>(s h i).slab)
  cap:Bounded (fun h i=>(s h i).cap)
  comparison:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).compareWidth≤C*h
  packed:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).digitArea≤C*h
  hosts:Bounded (fun h i=>(s h i).hosts)
  oldRows:Bounded (fun h i=>(s h i).oldRows)
  lows:Bounded (fun h i=>(s h i).lowSites)
  digit:∀h i,0<(s h i).fieldBits
  batch:∀h i,0<(s h i).lanes
  routeQueries:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,max (s h i).forwardArea (s h i).backArea≤C*h
  route:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).remoteArea≤C*h

end SignedExtent
end
end Hierarchy.DescentDatedAddressBook

end OAI
