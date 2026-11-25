import OAI.Hierarchy.TaggedWireRoutes
import OAI.Hierarchy.ProtocolRAMRouteSettlement

namespace OAI
/-! # The two terminal discharges on the very same width reported by the RAM -/

noncomputable section
namespace Hierarchy.ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Fin.CommRing

theorem reported_restricts {F : Type*} [Field F] {W r edges S : ℕ} [Nonempty (Fin S)]
    {I C : Type} [Fintype I] [Fintype C]
    {core : I → List (Fin edges)} {center : C → List (Fin edges)}
    (b : Banks) (src : ℕ) (m : Memory W) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (geo : Fin 7 → Expr)
    (fit : edges≤b.width.size) (bound : edges≤2^W) (space : b.width.base+edges≤ src)
    (room : ∀ e : Fin edges,(m (b.width.base+e.val)).val +
      (routeLoad core (fun i=>actual b.stock m (ci i)) e+
       routeLoad center (fun j=>actual b.reserved m (cj j)-actual b.used m (cj j)) e)<2^W)
    (G : PortGraph (Fin S) (Fin edges)) (ordinary : PortGraph (Fin S) I) (catalysts : PortGraph (Fin S) C)
    (walks : ∀ i, Traverses G (ordinary.tail i) (core i) (ordinary.head i))
    (near : ∀ j, Traverses G (catalysts.tail j) (center j) (catalysts.head j)) :
    (raw F (G.chordWidths (fun e=>(m (b.width.base+e.val)).val) +
      ordinary.chordWidths (fun i=>actual b.stock m (ci i)) +
      catalysts.chordWidths (fun j=>actual b.reserved m (cj j)-actual b.used m (cj j)))).Restricts
      (raw F (G.chordWidths (fun e=>(reportedRows [] (fields b geo) (output b src m enum ci cj) e).width))) :=
  settled_restricts F G ordinary catalysts core center _ _ _ _ _ walks near
    (fun e=>reported_width b src m enum ci cj geo e fit bound space (room e))

end Hierarchy.ProtocolRAM.RouteSettlement

end
end OAI
