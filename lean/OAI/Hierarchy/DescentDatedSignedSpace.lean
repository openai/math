import OAI.Hierarchy.DescentDatedSignedAny

namespace OAI
/-! The malformed-input proof uses a single numerical guard above the actual public address book. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentDyadicSpan
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)
local notation "s"=>v.signed
local notation "fmt"=>v.ticket.depotShape v.short
local notation "e"=>v.material

def signedGuard (floor:ℕ):=v.signedEnd floor+max (s).slab (s).oldSlab+
  (s).priorHosts*((s).reach*(s).reach)+(s).priorHosts*v.materialPitch+(s).lowSites+(s).hosts+(s).priorHosts+(s).reach*(s).reach+1

theorem signed_room (floor w:ℕ) (prior:(s).priorHosts=v.area.H) (next_:(s).hosts=v.venue.hosts)
    (lanes:0<(s).lanes) (blocks:0<(fmt).blocks) (groups:(e).oldGroups=(s).groups*(fmt).blocks)
    (growth:v.area.H≤ (s).hosts) (envelope:v.signedGuard floor<2^w):v.SignedRoom floor w:=by
  let first:=v.materialStart floor
  let last:=v.materialEnd floor
  let book:=DescentOrdinaryPeerCount.roof last v.area.H v.area.D v.venue.hosts v.venue.degree
  let start:=v.markEnd floor
  have material:first≤last:=by
    dsimp only [first,last,materialEnd]
    rw [(e).translated]
    exact Nat.le_add_right ..
  have addr:last≤v.peerTail floor:=by
    change last≤DescentOrdinaryVenueReturn.roof last _ _ _ _
    rw [DescentOrdinaryVenueReturn.expanded]
    omega
  have order:v.peerTail floor≤ start:=v.markShape.low _
  have early:last≤ start:=addr.trans order
  have lower:start≤v.signedEnd floor:=(s).room start
  have guard:=envelope
  dsimp only [signedGuard] at guard
  have endWord:v.signedEnd floor<2^w:=by omega
  have fit:book≤v.peerTail floor:=by
    change book≤book+2*DescentDyadicSpan.span v.venue.hosts+DescentDyadicSpan.span v.venue.hosts
    omega
  have near:= (DescentOrdinaryPeerCount.output_fit last v.area.H v.area.D v.venue.hosts v.venue.degree
    ((fit.trans (order.trans lower)).trans_lt endWord)).1
  have nw : 0<w :=by
    by_contra h
    have hz : w=0 :=by omega
    rw [hz, pow_zero] at guard
    omega
  have endEq : (s).roof (v.markEnd floor) = v.signedEnd floor := rfl
  exact ⟨prior,next_,lanes,blocks,groups,growth,material.trans early,early,
    ((material.trans early).trans lower).trans_lt endWord,by omega,by omega,by omega,by omega,by omega,
    ⟨near.1,near.2.1,near.2.2.trans (fit.trans order)⟩,nw,by rw [endEq];omega⟩

theorem guard_rate {ι:ℕ→Type*} (v:∀h,ι h→PhysicalOrdinary F P) (floor:∀h,ι h→ℕ)
    (end₀:Bounded fun h i=>(v h i).signedEnd (floor h i))
    (area:SignedExtent.ScalarRoom (fun h i=>(v h i).signed))
    (pitch:Bounded fun h i=>(v h i).materialPitch):
    Bounded (fun h i=>(v h i).signedGuard (floor h i)):=by
  have sheets:Bounded fun h i=>max (v h i).signed.slab (v h i).signed.oldSlab:=
    (area.rows.add area.oldRows).of_le fun h i=>max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
  have square:=area.reach.mul area.reach
  have total := ((((((end₀.add sheets).add (area.oldHosts.mul square)).add
    (area.oldHosts.mul pitch)).add area.lows).add area.hosts).add area.oldHosts)
  exact (total.add square).add (Bounded.const 1)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
