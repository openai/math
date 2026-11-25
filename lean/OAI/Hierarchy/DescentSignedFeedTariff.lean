import OAI.Hierarchy.DescentSignedFeedPrefix
import OAI.Hierarchy.DescentDatedSignedLimits

namespace OAI
/-! # Local instruction coefficients and the cost of a packed row on two host populations -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSIMDLookup

def prefixFactor (s : SignedExtent) (K : ℕ) :=
  20*(s.prepLimit K+1)*(21+(s.rankDirectoryFactor+s.peerInstallFactor+s.preparationFactor))

def rankColumns (s : SignedExtent) := s.blocks*3*s.candidates
def outputColumns (s : SignedExtent) := s.blocks*(2*s.cap)
def rankExpr (s : SignedExtent) (K : ℕ) := 1+s.candidates*(2*(13+11*(gatedLimit K+11))+12)
def outputExpr (s : SignedExtent) (K : ℕ) := 1+(2*s.candidates)*(14+8*((s.headerLimit K+18)+11))

/-- Each lookup-table word and packed row counts once in the corresponding pass. -/
def feedClockFactor (s : SignedExtent) (K : ℕ) :=
  s.prefixFactor K+
  ((8+10*28)+((4+10*4)+(4+s.rankColumns*(4+(2*s.rankExpr K+4))))+
  ((4+10*32)+((4+10*((8+2*s.cap)*2))+(4+s.outputColumns*(4+(2*s.outputExpr K+4))))))

def feedTextFactor (s : SignedExtent) (K : ℕ) :=
  s.prefixFactor K+
  (15*(28+2)+(15*(4+1)+15+s.rankColumns*(11+4*s.rankExpr K))+
  (15*(32+1)+(15*((8+2*s.cap)*2+1)+15+s.outputColumns*(11+4*s.outputExpr K))))

def feedFactor (s : SignedExtent) (K : ℕ) := s.feedClockFactor K+7*s.feedTextFactor K

def feedVolume (s : SignedExtent) (h unit : ℕ) :=
  (1+2^(h/2)+2*(s.priorHosts+s.hosts))*h + 4*(s.priorHosts+s.hosts)*s.groups*unit

theorem feed_rows_volume (s : SignedExtent) (h unit : ℕ) (pos : 0<unit)
    (wide : 2*unit≤h) (parallelism : s.lanes=DescentSIMDLookup.lanes h unit) :
    s.feedRows h*h≤ s.feedVolume h unit := by
  have prior := DescentSIMDLookup.volume s.priorHosts s.groups h unit pos wide
  have next := DescentSIMDLookup.volume s.hosts s.groups h unit pos wide
  rw [←parallelism] at prior next
  unfold feedRows feedVolume
  change (1+2^(h/2)+s.priorHosts+s.hosts+(s.priorHosts*chunks s.groups s.lanes)+
    s.hosts*chunks s.groups s.lanes)*h≤_
  nlinarith only [prior,next]


end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
