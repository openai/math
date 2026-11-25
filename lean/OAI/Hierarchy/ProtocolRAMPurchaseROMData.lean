import OAI.Hierarchy.ProtocolRAMPurchaseSourceLayout
import OAI.Hierarchy.ProtocolRAMPurchaseGateColumns

namespace OAI
/-! # The fixed sampler, path and gate words installed in a purchase-stage input -/

namespace Hierarchy.ProtocolRAMPurchaseAllocation.Layout
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

def gates (L : Layout) := ProtocolRAMPurchaseGateColumns.shapeDirectory L.source L.candidates (L.height+1)

def work (L : Layout) := ProtocolRAMPurchaseGateColumns.markBase L.source L.candidates (L.height+1)

def data {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) :=
  let sampler := ProtocolRAMPurchaseSampler.install L.start L.groups next back mem
  let digits := PurchaseDirectory.install L.directory L.rows L.degree L.height sampler
  GateColumns.mount L.gates (ProtocolRAMPurchaseGateColumns.spec (R:=L.candidates) (H:=L.height+1)
    (L.rows+1) L.work L.first) digits

end Hierarchy.ProtocolRAMPurchaseAllocation.Layout

end OAI
