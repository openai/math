import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Native numerical extents and rates for the old material archive -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM
def opLimit (D:ℕ):=128+20*(D+10)^4+64*(breadth D+breadth D*breadth D)
end Hierarchy.DescentDatedAddressBook.PriorHeader

namespace Hierarchy.DescentOrdinaryMarkProject.Shape
def shared (h : ℕ) := (h+2)^2*2^(h/2)
end Hierarchy.DescentOrdinaryMarkProject.Shape

namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentSIMDLookup DescentHaloWalkRAM

/-- Every term is a native scan axis or one half-word lookup table. -/
def scanVolume (H H' G G' L M blocks payload : ℕ) :=
  1+2^(payload/2)+payload+H+H'+H*chunks G L+H*chunks G' M+H'*chunks G' M+
    H*chunks G (M*blocks)

def strideFactor (D : ℕ) := 2*(1+1+breadth D*breadth D+1)+1
def priorFactor (D : ℕ) :=
  let P:=breadth D
  let paid:=(P+13)*strideFactor D
  (4+10*paid+7*(8+(P*P)*(2*PriorHeader.opLimit D+4))+4)+
    7*(15*(paid+1)+7*(15+(11+4*PriorHeader.opLimit D))+15)

def chartFactor (D : ℕ) :=
  let P:=breadth D
  4+10*(1+(1+P*(2*(P+1))))+7*(15*(1+(1+P*(2*(P+1)))+1))

def joinFactor (D : ℕ) :=
  let work:=32+40*breadth D
  4+10*2+7*(15*(2+1))+(4+(2*work+4))+7*(11+4*work)

def mapFactor (blocks P : ℕ) :=
  let wr:=fun c=>4+10*c+7*(15*(c+1))
  wr ((2*blocks)*2)+wr 1+wr (P+1)

def sheetFactor (n : ℕ) :=
  (4+10*(n*(1+(2*1+1))))+(4+n*(4+44))+7*(15*(n*(1+(2*1+1))+1)+(15+n*(11+4*20)))

def materialFactor (D blocks fields oldUnit : ℕ) :=
  priorFactor D+chartFactor D+joinFactor D+sheetFactor fields+mapFactor blocks (breadth D)+
    2048*((4*oldUnit*blocks+3)+fields+fields+1)

end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
