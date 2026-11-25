import OAI.Hierarchy.DescentResetPeerRootPages

namespace OAI
/-! # The public address of a reset root depends on the catalogue dimensions -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedColony DescentResetHostSize DescentResetGates
open DescentSixParty.Chronology ProtocolRAM
noncomputable section

/-- Ordinary census and signed rows can give different dependent Receiver types at
the same date. These are precisely the numerals used for an actual private root address. -/
def rootAddress (base H c M r n D : ℕ) (s : Bool) (j : PrivateTicket r n) : Bank :=
  ⟨(RootTemplates.arena base H (2^c) M r n D).output
    (rootIndex r (2^n) (privatePage s j)).val,Nat.clog 2 (H*chunks (2^c) M)⟩

theorem rootAddress_congr {x x' H H' c c' M M' r r' n n' D D' : ℕ}
    (base : x=x') (hosts : H=H') (groups : c=c') (lanes : M=M') (blocks : r=r') (dims : n=n') (arms : D=D')
    (side : Bool) (j : PrivateTicket r n) :
    rootAddress x H c M r n D side j=
      rootAddress x' H' c' M' r' n' D' side (cast (congrArg₂ PrivateTicket blocks dims) j) :=by
  subst x'; subst H'; subst c'; subst M'; subst r'; subst n'; subst D'
  rfl

variable {D cap N n r c H G K R M h₀ l t field Ht w D' cap' N' n' r' c' H' G' K' R' M' h₀' l' t' field' Ht' w' : ℕ}

theorem catalogue_address (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w)
    (b : RootBook n r D (2^r) cap field)
    (a' : Receiver D' cap' N' n' r' c' H' G' K' R' M' h₀' l' t' field' Ht' w')
    (b' : RootBook n' r' D' (2^r') cap' field')
    (base : a.headerEnd b = a'.headerEnd b')
    (hosts : H=H') (groups : c=c') (lanes : M=M') (blocks : r=r') (dims : n=n') (arms : D=D')
    (side : Bool) (j : PrivateTicket r n) :
    a.privatePageBank b side j=
      a'.privatePageBank b' side (cast (congrArg₂ PrivateTicket blocks dims) j) :=
  rootAddress_congr base hosts groups lanes blocks dims arms side j

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
