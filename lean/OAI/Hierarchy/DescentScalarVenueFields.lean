import OAI.Hierarchy.DescentScalarVenueMask
import OAI.Hierarchy.DescentPackedActorMask

namespace OAI
/-! # The full receiving column of old and matched six-party venue fields -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPackedColony DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P r cap raw low k gain slots H G M w : ℕ}
local notation "A"=>DescentPackedActorMask.actors (P*r) cap
local notation "K"=>1+cap*6

def fields (walks : Fin H→Fin P→Option (Fin H)) (ticket : Fin r→Fin K→Fin H→Fin G→Ticket P raw) (hubs : Fin H→Fin G→Cell 1)
    (k gain slots low : ℕ) (h : Fin H) (g : Fin G) (j : Fin A) :=
  let z:Fin (P*r)×Fin K:=finProdFinEquiv.symm j;let loc:Fin P×Fin r:=finProdFinEquiv.symm z.1
  let t:=(DescentSortedRoster.indexed walks h loc.1).bind fun v=>ticket loc.2 z.2 v g
  returned k gain slots raw low walks loc.1 h (hubs h g) t

/-- Paths and local heap/slot words can be bound to old owner outputs
before the receive pass. The two fields at a donor refer to the same
selected old or born site, including its activity bit. -/
structure Donors (P r cap : ℕ) where
  route : Fin r→Fin (1+cap*6)→Bank
  localKey : Fin r→Fin (1+cap*6)→Bank
  ports : Ports P
  head : Fin P→Hardware P
  masks : Fin (DescentPackedActorMask.actors (P*r) cap)→Tables
  hub : Expr

def Donors.one (C : Donors P r cap) (H : ℕ) (j : Fin A) : Expr:=
  let z:Fin (P*r)×Fin K:=finProdFinEquiv.symm j;let loc:Fin P×Fin r:=finProdFinEquiv.symm z.1
  expr (C.head loc.1) (peerExpr C.ports (C.route loc.2 z.2) H loc.1) (peerExpr C.ports (C.localKey loc.2 z.2) H loc.1) C.hub

def Donors.all (C : Donors P r cap) (H : ℕ) :=Gather.assembly C.masks (C.one H)

structure MountedDonors (C : Donors P r cap) (walks : Fin H→Fin P→Option (Fin H)) (t : Fin r→Fin K→Fin H→Fin G→Ticket P raw)
    (hubs : Fin H→Fin G→Cell 1) (k gain slots low M base : ℕ) (m : Memory w) : Prop where
  roster : Mounted C.ports (DescentSortedRoster.indexed walks) m G M
  path : ∀b j,Reads (C.route b j) (fun h g=>pathCode (t b j h g)) M m
  lowKey : ∀b j,Reads (C.localKey b j) (fun h g=>localCode (t b j h g)) M m
  pathRoom : ∀b j,Accessible C.ports (C.route b j) H G M w base
  lowRoom : ∀b j,Accessible C.ports (C.localKey b j) H G M w base
  hub : Source C.hub hubs M m
  search : ∀s b j,DescentPackedChildNeighbor.SIMD.Room (C.head s).host (peerExpr C.ports (C.route b j) H s) H G (Packed.bits P) 1 M w base
  reaches : ∀s,DescentPackedChildNeighbor.SIMD.Stored (C.head s).host H G (Packed.bits P) 1 M (checks walks s) m
  prior : ∀s b j,let q:=DescentPackedChildNeighbor.SIMD.body (C.head s).host (peerExpr C.ports (C.route b j) H s) (List.finRange P)
                 DescentPackedZip.Fits (C.head s).prior q (peerExpr C.ports (C.localKey b j) H s) 1 (Packed.bits raw) M base w
  last : ∀s b j,let q:=DescentPackedChildNeighbor.SIMD.body (C.head s).host (peerExpr C.ports (C.route b j) H s) (List.finRange P)
                DescentPackedZip.Fits (C.head s).trim C.hub ((C.head s).prior.read q (peerExpr C.ports (C.localKey b j) H s)) 1 (Packed.bits raw) M base w
  hold : ∀s,Static (C.head s).prior (keepRaw (raw:=raw)) M m
  trim : ∀s,Static (C.head s).trim (trimmed k gain slots raw low) M m
  collectFits : Gather.Bounds (d:=Packed.bits low) (w:=w) (M:=M) C.masks (C.one H) base
  collectROM : ∀j,Static (C.masks j) (Gather.setField (d:=Packed.bits low) j) M m

theorem issued (C : Donors P r cap) (walks : Fin H→Fin P→Option (Fin H)) (t : Fin r→Fin K→Fin H→Fin G→Ticket P raw)
    (hubs : Fin H→Fin G→Cell 1) (base : ℕ) (m : Memory w) (ready : MountedDonors C walks t hubs k gain slots low M base m) :
    Source (C.all H) (fun h g=>encode (Packed.bits low) A (fields walks t hubs k gain slots low h g)) M m :=by
  have each (j : Fin A):Source (C.one H j) (fun h g=>fields walks t hubs k gain slots low h g j) M m:=by
    let z:Fin (P*r)×Fin K:=finProdFinEquiv.symm j;let x:Fin P×Fin r:=finProdFinEquiv.symm z.1
    let ticket:=fun h g=>(DescentSortedRoster.indexed walks h x.1).bind fun v=>t x.2 z.2 v g
    have pathAt : Source (peerExpr C.ports (C.route x.2 z.2) H x.1) (fun h g=>pathCode (ticket h g)) M m:=by
      have same (h g) : pathCode (ticket h g)=(DescentSortedRoster.indexed walks h x.1).elim 0 (fun u=>pathCode (t x.2 z.2 u g)):=by
        unfold ticket;cases DescentSortedRoster.indexed walks h x.1 <;> rfl
      simp_rw [same]
      exact peerSource C.ports (C.route x.2 z.2) base (ready.pathRoom x.2 z.2)
        (DescentSortedRoster.indexed walks) m ready.roster (fun h g => pathCode (t x.2 z.2 h g))
        (ready.path x.2 z.2) x.1
    have keyAt : Source (peerExpr C.ports (C.localKey x.2 z.2) H x.1) (fun h g=>localCode (ticket h g)) M m:=by
      have same (h g) : localCode (ticket h g)=(DescentSortedRoster.indexed walks h x.1).elim 0 (fun u=>localCode (t x.2 z.2 u g)):=by
        unfold ticket;cases DescentSortedRoster.indexed walks h x.1 <;> rfl
      simp_rw [same]
      exact peerSource C.ports (C.localKey x.2 z.2) base (ready.lowRoom x.2 z.2)
        (DescentSortedRoster.indexed walks) m ready.roster (fun h g => localCode (t x.2 z.2 h g))
        (ready.lowKey x.2 z.2) x.1
    exact from_chips (C.head x.1) _ _ _ base m walks x.1 ticket hubs pathAt keyAt ready.hub
      (ready.search x.1 x.2 z.2) (ready.reaches x.1) (ready.prior x.1 x.2 z.2)
      (ready.last x.1 x.2 z.2) (ready.hold x.1) (ready.trim x.1)
  simpa only [Donors.all,Gather.assembly,List.mem_finRange,ite_true] using
    Gather.collected C.masks (C.one H) base ready.collectFits m ready.collectROM
      (fields walks t hubs k gain slots low) each (List.finRange A)

end
end Hierarchy.DescentScalarVenueMask

end OAI
