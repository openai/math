import OAI.Hierarchy.DescentRegisteredOrdinaryBooks

namespace OAI
/-! The sixteen local argument widths and the five source searches at the first chosen pitch. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentOrdinaryVenueIngress
open DescentHaloWalkRAM DescentPackedActorMask DescentRawCablePanel DescentSIMDLookup
open DescentSharedCableNames DescentOrdinaryOriginMask
noncomputable section
namespace OrdinaryBooks
variable {F:Type} [Field F] (G:PoweredGadget F) (b:OrdinaryBooks)

def sourceWidths (old:DescentDatedPriorOperand.Layout) (c:Clip) : Fin 16→ℕ :=
  let refs:=b.reference
  let candidates:=nodes (breadth refs.degree*2^refs.k) refs.oldNodes refs.capacity
  let origin:Return:=⟨refs.degree,refs.k,refs.oldNodes,refs.capacity,b.resolver.nodes,Nat.clog 2 (candidates+1),
      b.vector.hosts,b.vector.lows,b.vector.groups,b.vector.radix,b.vector.lanes⟩
  let printed:=DescentPrimitivePalette.printedBits G b.palette.seedWidth b.palette.grainLimit b.palette.rotor
  let donors:=c.venue.paths*old.blocks
  PhysicalOrdinary.widthTable (DescentOrdinaryPriorRetile.digits old) (printed*refs.oldNodes)
    (refs.countBits*donors+refs.countBits) (DepotRAM.totalBits c.venue.socket)
    refs b.bornBook b.vector b.resolver origin b.operandBook printed b.metadata.chart.bits b.metadata.paidBits

def sourceGeometry (s:PhysicalOrdinary.StaticCore) : Geometry :=
  let l:=b.resolver
  let fmt:=s.format
  let P:=breadth fmt.degree
  let digit:=max (max s.material.fieldBits (l.size+2)) (max b.bornBook.bits (Packed.bits P))
  ⟨l.hosts,l.groups,l.lanes,l.jobs,P,fmt.blocks,fmt.degree,fmt.cap,digit,l.size+2⟩

def purchaseAt (core:PhysicalOrdinary.StaticCore) (ports:DatePorts) (c:Clip) : ℕ :=
  let b₀:=b.clipped core.area c
  let old:=ports.argumentLayout (2^core.area.k)
  max (Finset.univ.sup (b₀.sourceWidths G old c)) (purchase (b₀.sourceGeometry core))

def argumentCost (core:PhysicalOrdinary.StaticCore) (ports:DatePorts) (paidBits:ℕ) : ℕ :=
  b.purchaseAt G core ports (PhysicalOrdinary.fundedClipAt core.area core.format core.donor.amount paidBits 0)

end OrdinaryBooks

namespace PhysicalOrdinary
variable {F Pin:Type} [Field F] (v:PhysicalOrdinary F Pin) (ports:DatePorts) (floor:ℕ)

theorem argument_purchase :
    v.argumentUnitFrom ports floor=v.books.purchaseAt v.gadget (v.staticCore floor) ports (v.fundedClip 0) :=rfl

theorem argument_purchase_named
    (short:v.short=max (v.k+3) (Nat.clog 2 (v.area.D+1)))
    (profile:v.profile=DescentTerminalEpochBits.width v.gadget.C) :
    v.argumentUnitFrom ports floor=v.books.argumentCost v.gadget (v.staticCore floor) ports v.venue.paidBits :=by
  rw [argument_purchase,OrdinaryBooks.argumentCost,v.fundedClip_named 0 short profile]
  have socket:v.ticket.depotShape v.short=v.ticket.donorDate.format:=by rw [short]; rfl
  change v.books.purchaseAt v.gadget _ ports
      (fundedClipAt v.area v.ticket.donorDate.format v.ticket.donorDate.amount v.venue.paidBits 0)=
    v.books.purchaseAt v.gadget _ ports
      (fundedClipAt v.area (v.ticket.depotShape v.short) v.ticket.donorDate.amount v.venue.paidBits 0)
  rw [socket]

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
