import OAI.Hierarchy.DescentSignedLayout

namespace OAI
/-! Public scalar envelopes of the signed renderer. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
variable (s:SignedExtent) (K:ℕ)
def rankCost:=(1+s.reach*s.reach*(2*K+47))
def donorCost:=2*(K+16)+11
def queryCost:=2*K+23+s.reach*(K+36)
def routeCost:=1+s.routeTotal*(s.queryCost K+57)
def directoryCost:=15+36*(s.reach*s.reach)+K*(30+36*(s.reach*s.reach))
def prepLimit:=128+s.rankCost K+donorCost K+s.routeCost K+s.directoryCost K
def gatedLimit:=512+K
def headerLimit:=1024+2*K+s.peerKinds*512

def converterLiterals := 26*2^s.compareWidth+2*2^(s.fieldBits*11*s.lanes)
def rankLiterals := 4*2^((s.fieldBits*5+s.fieldBits*5)*s.lanes)
def metaLiterals := 32*2^((s.fieldBits*7+s.fieldBits)*s.lanes)
def signedLiterals := (8+2*s.cap)*2*2^((s.fieldBits*8+s.fieldBits)*s.lanes)
local notation "dhead"=>s.converterLiterals
local notation "rhead"=>s.rankLiterals
local notation "mhead"=>s.metaLiterals
local notation "shead"=>s.signedLiterals
local notation "nr"=>(s.blocks*3)*s.candidates
local notation "ns"=>s.blocks*(2*s.cap)
local notation "N"=>s.slab
local notation "wr"=>1+s.candidates*(2*(13+11*(gatedLimit K+11))+12)
local notation "ws"=>1+(2*s.candidates)*(14+8*((s.headerLimit K+18)+11))

def fixedTime:=20*(s.prepLimit K+1)*(21+s.roof 0)+
  ((8+10*dhead)+((4+10*rhead)+(4+nr*(4+N*(2*wr+4))))+
    ((4+10*mhead)+((4+10*shead)+(4+ns*(4+N*(2*ws+4))))))
def fixedNames:=20*(s.prepLimit K+1)*(21+s.roof 0)+
  (15*(dhead+2)+(15*(rhead+1)+15+nr*(11+4*wr))+
    (15*(mhead+1)+(15*(shead+1)+15+ns*(11+4*ws))))

end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
