import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentMaterialSocketRoom
import OAI.Hierarchy.DescentDatedOperandMux

namespace OAI
/-! # Gather the operand pages from the measured previous donor into the successor group -/
namespace Hierarchy.DescentDatedOperandPages
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM DescentRawCablePanel
open DescentSixParty.Chronology DescentRawCablePanel.DepotRAM.Material
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G K M r L b w profile : ℕ} (f : DepotRAM.Shape)
local notation "l" => Layout.mk H (G*r) L (M*r) b profile
local notation "P" => breadth f.degree
local notation "port" => (0:Route.Port)

def socket (H G K M r b : ℕ) (base : ℕ) (rank : DescentOrdinaryDonorRankDirectory.Banks)
    (ports : Ports P) (source : Bank) (p : Fin P) (x : Fin r) : Expr :=
  Route.projected rank ports source (Route.bank K G M (Route.Projection.mapBase b r M base))
    (Route.stampBank K G M (Route.Projection.markBase b r M K G base) port p) H G M p
    (Route.Projection.table b r M base port x)

theorem issued_socket (floor address out : ℕ) (R : Fin H → Fin f.degree → Option (Fin H))
    (rank : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P) (v : Fin H → Fin (G*r) → DepotRAM.Parts f)
    (original later : Memory w) (pitch : ℕ) (j : Fin (count f)) (p : Fin P) (x : Fin r)
    (range : Route.Projection.roof b r M K G P floor≤out) (room : out<2^w) (hm : 0<M) (hr : 0<r)
    (stable : ∀i,i<Route.Projection.roof b r M K G P floor →
      later i=(Route.Projection.stage H K G M P b r pitch floor w).image original i)
    (old : Reads (resultBank f l address j) (fun h g=>law f profile b j.val (DepotRAM.combine f (v h g))) (M*r) later)
    (access : Accessible (Route.keepPorts rank ports) (resultBank f l address j) H G M w out)
    (roster : Mounted ports (Gather.reaching R) later G M) (rankRead : DescentOrdinaryDonorRankDirectory.Reads R rank later)
    (safe : H*chunks G M<2^w) :
    Source (H:=K) (socket f H G K M r b floor rank ports (resultBank f l address j) p x)
      (Route.value R pitch p port x (fun h g=>law f profile b j.val (DepotRAM.combine f (v h g)))) M later :=
  Route.Projection.source_later floor out range room R rank ports (resultBank f l address j) port p x _ pitch original later
    hm hr stable old access roster rankRead safe

theorem live_socket (R : Fin H → Fin f.degree → Option (Fin H)) (v : Fin H → Fin (G*r) → DepotRAM.Parts f)
    (pitch : ℕ) (j : Fin (count f)) (p : Fin P) (x : Fin r) (h : Fin K) (g : Fin G) (recv donor : Fin H)
    (high : Route.receiver H pitch h=some recv) (issued : Gather.select (Gather.reaching R) recv p=some donor) :
    Route.value R pitch p port x (fun z t=>law f profile b j.val (DepotRAM.combine f (v z t))) h g=
      law f profile b j.val (DepotRAM.combine f (v donor (finProdFinEquiv (g,x)))) := by
  simp [Route.value,Route.selected,high,issued,Route.gated]

theorem missing_socket (R : Fin H → Fin f.degree → Option (Fin H)) (v : Fin H → Fin (G*r) → DepotRAM.Parts f)
    (pitch : ℕ) (j : Fin (count f)) (p : Fin P) (x : Fin r) (h : Fin K) (g : Fin G)
    (hole : Route.selected R pitch p h=none) :
    Route.value R pitch p port x (fun z t=>law f profile b j.val (DepotRAM.combine f (v z t))) h g=0 := by
  simp [Route.value,hole]

end
end Hierarchy.DescentDatedOperandPages

end OAI
