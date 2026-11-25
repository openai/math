import OAI.Hierarchy.TaggedWideSpillPooledGeometry
import OAI.Hierarchy.TaggedWideSpillPooledRoles
import OAI.Hierarchy.TaggedWideSpillPooledFields

namespace OAI
/-! # Signed role and absolute address on a physical live row of the dated spill RAM -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillPosition
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard WireTelescope HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM ProtocolRAM.Calendar CoreRoute ProtocolRAMTurnOrder ProtocolRAMTurnChart ProtocolRAMTurnItinerary
open ProtocolRAMTurnReplayed ProtocolRAMDateSpillRank ProtocolRAM.DateSpill.Turns
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxHeartbeats 1800000
variable {h W k w attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (b : RoleProgram.Board)
    (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) b.edges) (pad : Chord (siteLast h (2^W) k+1))
    (o : Orders h (2^W) k) (lo base : ℕ) (spill : Bank) (original m : Memory w)
    (reader : RankRead B o lo spill original m)
local notation "Good" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Full" => SettledMatrix.Source b.edges Good (Columns h (2^W)×Fin k)
local notation "Sub" => SettledMatrix.Source b.edges Good Empty
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder b.edges h (2^W) k).symm
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "D" => B.datedLayout inj pad
local notation "size" => b.edges+coreCount o
local notation "ranked" => (D).nativeOrder (spillEnum B o)
local notation "vals" => ProtocolRAMTurnSnapshot.values (b.itinerary (key lo size) (rank lo size b.edges)) m
local notation "stock" => fun g=>RouteSettlement.actual spill original (PurchaseInventory.slot g)
local notation "bits" => (D).bits stock
local notation "order" => positionOrder S π B pad
local notation "sp" => fun i=>sparseSpine S π B pad ((D).num i)
local notation "P" => Public S h W k attempts
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))
local notation "num" => Fintype.card (TurnShelf.Positions (D).routes)

def originalSpillCodes (pay : Fin b.edges→Bool→P) (i : Fin (b.edges+PurchaseInventory.footprint h (Stages h (2^W)) k)) (s : Bool) :=
  ProtocolRAMTurnOperands.printed S false (publicRoleFor S π pay (source ((D).num i))) s false

include reader in
/-- A real rank word is read for each adjacent hop, with the corresponding
authenticated paid row on positive stock. Only original directed board words,
the two chronological prefix expressions and their numeric room enter here. -/
theorem live_fields (markDepth : ℕ) (marks : ReportSockets.Marks h W k attempts) (unique : ReportSockets.Exclusive marks)
    (oldWidth : Fin b.old→ℕ) (total : Fin b.edges→ℕ) (oldPorts : ∀i,0<oldWidth i→Bool→P)
    (paidPorts : ∀e,0<total e→Bool→P) (auth : b.LiveReads S oldWidth total oldPorts paidPorts m)
    (id : {e:Fin b.edges // 0<total e}→Catalogue S π markDepth marks)
    (aligned : ∀e,filledChord B.actual pad e.val=sorted S π markDepth marks (.inl (id e)))
    (ports : ∀e on s,paidPorts e on s=.inl (paid S π markDepth marks unique (id ⟨e,on⟩,s)))
    (pay : Fin b.edges→Bool→P) (data : ProtocolRAMTurnChart.Data) (oldBase newBase : ℕ→ℕ)
    (charged : ∀e,routeLoad B.ordinary stock e≤total e) (fits : ∀e,total e≤2^w)
    (words : 4*size≤2^w) (edgeRoom : b.edges≤2^w) (siteRoom : siteLast h (2^W) k+1≤2^w)
    (newFit : ∀e on s,ProtocolRAMTurnOperands.printed S true (paidPorts e on) s false<2^w)
    (krow : Fin num) (on : 0<bits (order krow).1)
    (g : Good) (row : (D).num (order krow).1=.inr (.inl g)) (a : Fin b.old)
    (ordinal : a.val=(ProtocolRAMTurnGeometry.sourceOrder b.edges h (2^W) k (.inr (.inl g))).val)
    (old : let p:=publicRoleFor S π pay (.inr (.inl g))
      rev (captured data m) a.val=ProtocolRAMTurnStepOrder.reverse B inj pad (.inr (.inl g)) ∧
      (vals).oldSource a.val=ProtocolRAMTurnOperands.printed S false p false false ∧
      (vals).oldTarget a.val=ProtocolRAMTurnOperands.printed S false p true false)
    (left : oldBase a.val=datedBase (D).family bits (order krow).1)
    (right : ∀e,0<routeLoad B.ordinary stock e→newBase e.val=datedBase (D).edge (routeLoad B.ordinary stock) e)
    (s : Bool) :
    let t:=record (ProtocolRAMTurnGeometry.header o base names) (captured data m) visit (chartReal S π B pad krow)
    let p:=order krow
    let ref:=TurnShelf.refAt (D).family (D).edge (D).routes sp p s
    fieldWords t vals oldBase newBase (if s then 1 else 0)=refRole (D).routes
       (originalSpillCodes S π b B pad pay) (ProtocolRAMTurnStepOrder.liveCode S true total paidPorts) p.1 ref ∧
    fieldWords t vals oldBase newBase (if s then 3 else 2)=datedStart (D).family (D).edge (D).routes bits ranked p.1 ref := by
  intro t p ref
  have decode : source (C:=Columns h (2^W)×Fin k) ((D).num p.1)=.inr (.inl g):=congrArg _ row
  have observed : rev (captured data m) (ProtocolRAMTurnGeometry.sourceOrder b.edges h (2^W) k (source ((D).num p.1))).val=
      ProtocolRAMTurnStepOrder.reverse B inj pad (source ((D).num p.1)) := by
    rw [decode,←ordinal]
    exact old.1
  obtain ⟨item,origin,length,direction,position,site⟩:=
    registered_fields S π B pad o base (captured data m) krow observed
  change t.item=_ at item
  rw [decode,←ordinal] at item
  rw [decode] at origin length direction
  have routeEq: (D).routes p.1=(D).data.steps (.inr (.inl g)):=congrArg _ row
  let hop (q : Fin ((D).routes p.1).length):=q.cast (congrArg List.length routeEq)
  let akey (q : Fin ((D).routes p.1).length):=b.edges+(goodIndex B inj pad o g (hop q)).val
  let jc:=p.2.cast (congrArg (fun l=>l.length+1) routeEq)
  have both:=neighbor_addresses S π B pad o g t jc origin length direction position
  have plen : t.length=((D).routes p.1).length:=by
    rw [routeEq];exact length.trans (ProtocolRAMTurnEdges.canonical_length B inj pad (.inr (.inl g))).symm
  apply ProtocolRAMDateSpillTurns.field_references (D).family (D).edge (D).routes bits ranked sp p.1 p.2
    (originalSpillCodes S π b B pad pay) (ProtocolRAMTurnStepOrder.liveCode S true total paidPorts)
    t vals oldBase newBase plen position site akey (fun _=>false)
  · intro q eqn;exact (both (hop q)).1 (Fin.ext (show q.val+1=p.2.val from congrArg Fin.val eqn))
  · intro q eqn;exact (both (hop q)).2 (Fin.ext (show q.val=p.2.val from congrArg Fin.val eqn))
  · simpa only [item,originalSpillCodes,decode] using old.2.1
  · simpa only [item,originalSpillCodes,decode] using old.2.2
  · simpa only [item] using left
  · intro q
    let e:=((D).routes p.1).get q
    have edgeRead:=RankRead.snapshot_good b B inj pad o reader p.1 g row q words edgeRoom on (fun e=>(charged e).trans (fits e))
    have live:=NativeSlot.start_room (D).routes bits ranked p.1 q on
    rw [(D).measured] at live
    have active : 0<routeLoad B.ordinary stock e:=on.trans_le (by exact (Nat.le_add_left ..).trans live)
    have data:=DateSpill.paid_hop_roles S π b B pad markDepth marks unique (key lo size) (rank lo size b.edges)
      m oldWidth total oldPorts paidPorts auth id aligned ports e (active.trans_le (charged e)) siteRoom (newFit e _)
    change (vals).edge (akey q)=e.val ∧ (vals).starts (akey q)=_ at edgeRead
    dsimp only
    rw [edgeRead.1]
    exact ⟨data.1,data.2.1,data.2.2,by rw [funext ((D).measured stock)];exact right e active,edgeRead.2⟩

end Hierarchy.ProtocolRAMDateSpillPosition
end

end OAI
