import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentOrdinaryStaticCore

namespace OAI
/-! # The ordinary register books at the purchased working and return pitches -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentOrdinaryVenueIngress DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentDatedPriorOperand ProtocolRAM
noncomputable section
namespace OrdinaryBooks

/-- These are the literal two pitches used by the reference table, the newborn
table and the rebased resolver. Metadata is written with the resolver pitch. -/
def clipped (b : OrdinaryBooks) (a : Dated.Ordinary) (c : Clip) : OrdinaryBooks :=
  let r : Layout := {b.resolver with
    blocks:=c.radix,operands:=b.vector.operands,hosts:=b.vector.hosts*b.vector.lows,
    groups:=b.vector.groups,lanes:=c.postPitch}
  { b with
    reference:={b.reference with lanes:=c.working,degree:=a.D,k:=a.k}
    bornBook:={b.bornBook with lanes:=c.working,blocks:=2^a.k,cap:=b.reference.capacity,args:=b.vector.operands}
    vector:={b.vector with lanes:=c.postPitch,radix:=c.radix}
    resolver:=r
    metadata:={b.metadata with chart:=⟨r.blocks,r.nodes,r.hosts,r.groups,b.metadata.chart.bits,r.lanes⟩}
    origin:=⟨b.origin.preparationWords⟩
    operandBook:=⟨r,b.metadata.chart.bits,b.metadata.chart.bits⟩ }

/-- Register the two relative sizes of the native input publishers. -/
def reserved (b : OrdinaryBooks) (early routed : ℕ) : OrdinaryBooks :=
  {b with ingressWords:=early,origin:=⟨routed⟩}

end OrdinaryBooks

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def books : OrdinaryBooks :=
  ⟨v.reference,v.bornBook,v.ingressWords,v.vector,v.resolver,v.origin,v.palette,v.metadata,v.operandBook⟩

theorem clip_books (extra : ℕ) :
    (v.withFundedClip extra).books=v.books.clipped v.area (v.fundedClip extra) :=rfl

theorem registered_books (prior : DatePorts) (floor : ℕ) :
    let c:=v.fundedClip (v.argumentUnitFrom prior floor)
    let A:=v.registeredEntry prior floor
    let W:=v.registeredFrom prior floor
    W.books=(v.books.clipped v.area c).reserved (A.words W)
      (W.originControlWords+W.originMouthWords+W.rootSourceSize) :=rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
