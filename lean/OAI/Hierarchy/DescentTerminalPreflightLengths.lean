import OAI.Hierarchy.DescentTerminalPreflightSpace

namespace OAI
/-! # Exact address increments and translation along the full purchased terminal preflight -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalPrimitiveArena DescentTerminalLocalPortBook DescentTerminalGrainProfiles
open DescentTerminalRowArena ProtocolRAM DescentSIMDLookup
noncomputable section
variable (x:Spec) (base:ℕ)
local notation "H" => x.scalar.shops
local notation "B" => x.scalar.blocks
local notation "N" => x.scalar.rows
local notation "room" => x.headerRows
local notation "n" => x.paidRows
def incomingWords := DescentTerminalFrozenRoster.ROM.size x.frozenBits x.cohortBits+
  3*pad x.cohorts+2*pad H+4*x.cohorts+2*H+2
def oldMenus := 2^x.externalBits+chunks x.groups x.paidLanes*2^(x.paidBits*x.paidLanes)+
  B*chunks x.groups x.actorLanes*2^x.actorLanes
def oldWords := 2*pad H+x.oldMenus+2*N+x.scalar.guard+pad H
def primitiveWords := (x.scalar.columns+6)*N+5*pad N+4*pad H+
  2*fee x.scalar.columns x.scalar.pointerBits+fee 3 x.scalar.countBits
def bookWords := Book.WeightShelf.words x.vertices x.arguments+
  6*(x.strips*H+pad H+fee x.strips x.printBits+pad H)
def controlBytes := Book.Bytes 4 x.vertices (x.vertices*x.arguments) x.arguments (Book.tokenBits (x.vertices*x.arguments))
def controlShape : DescentTerminalControlROM.Shape:=⟨x.vertices,x.binSize,x.pageBits⟩
def controlWords := pad x.controlBytes+2*pad H+1+4*pad x.controlShape.limit
def tickets:=H*x.degree
def widthColumns:=Counter.columns B x.cap x.groups x.signedLanes
def cableCap:=x.groups*(B*x.cap)*x.grainsPerCable
def cableWords:=6*pad x.tickets+x.widthColumns*x.tickets+fee x.widthColumns x.cableCellBits+
  2*pad (x.cableCap+1)+pad room+1+2*x.tickets
def publicWords:=pad (2^x.cohortBits+1)+2*pad H+2*pad (2^x.cohortBits*x.publicGrains+1)+pad room+1+2*H
def eventWords:=4*DescentTerminalHeaderDraft.span n+22*ProtocolRAMPurchaseSampler.span (2*H+n+0+1)+3*pad n

theorem incoming : x.cohortEnd base=base+x.incomingWords := by
  change base+DescentTerminalFrozenRoster.ROM.size x.frozenBits x.cohortBits+pad x.cohorts+pad H+H+1+
    pad x.cohorts+pad H+pad x.cohorts+4*x.cohorts+H+1=_
  unfold incomingWords;ring
theorem prior_size : x.primitive base=x.cohortEnd base+x.oldWords := by
  unfold primitive DescentTerminalPriorArena.start DescentTerminalPriorArena.actor DescentTerminalPriorArena.actStart
    DescentTerminalPriorArena.pop oldWords oldMenus
  change x.cohortEnd base+(pad H+2^x.externalBits+chunks x.groups x.paidLanes*2^(x.paidBits*x.paidLanes))+
    N+x.scalar.guard+(pad H+B*chunks x.groups x.actorLanes*2^(1*x.actorLanes))+N+pad H=_
  rw [one_mul];ring
theorem primitive_size : x.weights base=x.primitive base+x.primitiveWords := by
  simpa only [weights, primitiveWords, Nat.add_assoc] using x.scalar.exact_end (x.primitive base)
theorem book_size : x.bookEnd base=x.weights base+x.bookWords := by
  change x.weights base+Book.WeightShelf.words x.vertices x.arguments+
    6*(x.strips*H+pad H+fee x.strips x.printBits+pad H)=_
  unfold bookWords;omega
theorem controls_size : (x.controls base).finish=x.bookEnd base+x.controlWords := by
  change x.bookEnd base+pad x.controlBytes+pad H+pad H+(1+4*pad x.controlShape.limit)=_
  unfold controlWords;omega
theorem cable_size : x.cableEnd base=(x.controls base).finish+x.cableWords := by
  change (x.controls base).finish+3*pad x.tickets+x.widthColumns*x.tickets+pad x.tickets+
    fee x.widthColumns x.cableCellBits+pad x.tickets+2*pad (x.cableCap+1)+pad x.tickets+
    pad room+1+x.tickets+x.tickets=_
  unfold cableWords;omega
theorem public_size : x.literalBase base=x.cableEnd base+x.publicWords := by
  change x.cableEnd base+pad (2^x.cohortBits+1)+pad H+2*pad (2^x.cohortBits*x.publicGrains+1)+pad H+
    pad room+1+H+H=_
  unfold publicWords;omega
theorem draft_size : x.maskBase base=x.literalBase base+x.eventWords := by
  change x.literalBase base+4*DescentTerminalHeaderDraft.span n+22*ProtocolRAMPurchaseSampler.span (2*H+n+0+1)+3*pad n=_
  unfold eventWords;omega

def words := x.incomingWords+x.oldWords+x.primitiveWords+x.bookWords+x.controlWords+x.cableWords+x.publicWords+x.eventWords
theorem section_end : x.maskBase base=base+x.words := by
  rw [draft_size,public_size,cable_size,controls_size,book_size,primitive_size,prior_size,incoming]
  unfold words;omega
theorem translate : x.maskBase base=base+x.maskBase 0 := by simp only [section_end,Nat.zero_add]

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
