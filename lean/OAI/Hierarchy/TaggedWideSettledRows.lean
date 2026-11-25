import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProbeFinalRoutes

namespace OAI
/-! # The native reporter's own edge widths satisfy the settled ledger -/

noncomputable section
namespace Hierarchy.ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Fin.CommRing

/-- The capacity term and the emitted width have the same unique physical
edge index. Counters for stock and catalyst returns are actual RAM reads. -/
theorem report_termBudget {W r edges : ℕ} {I C : Type*} [Fintype I] [Fintype C]
    {core : I → List (Fin edges)} {center : C → List (Fin edges)}
    (b : Banks) (src : ℕ) (m : Memory W) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (geo : Fin 7 → Expr)
    (fit : edges≤b.width.size) (bound : edges≤2^W) (space : b.width.base+edges ≤ src)
    (room : ∀ e : Fin edges,(m (b.width.base+e.val)).val +
      (routeLoad core (fun i=>actual b.stock m (ci i)) e+
        routeLoad center (fun j=>actual b.reserved m (cj j)-actual b.used m (cj j)) e)<2^W)
    (p q Q Λ : ℝ) (n w M : ℕ) (hn : 0<n) (hw : 0<w)
    (t len : Fin edges → ℝ) (cash : ℝ) (box : I→ℝ)
    (within : ∀ j,actual b.used m (cj j)≤actual b.reserved m (cj j))
    (ordinary : ∀ i,((core i).map len).sum≤box i)
    (central : ∀ j,((center j).map len).sum≤2*M)
    (prepaid : (∑ e : Fin edges, (len e*(((m (b.width.base+e.val)).val:ℝ)/w)+
      Λ*AdaptiveProbe.capacity p q Q (t e) (len e)))≤cash+2*M*(∑ j, (actual b.used m (cj j):ℝ))/w)
    (paid : cash+pairing (fun i=>(actual b.stock m (ci i):ℝ)/w) box≤6*n) :
    TermBudget p q Q Λ n w M (∑ j,actual b.reserved m (cj j)) t len (fun e : Fin edges =>
      ((reportedRows [] (fields b geo) (output b src m enum ci cj) e).width:ℝ)/w) := by
  have bill := settle_installed_routes p q Q Λ n w M hn hw t len
    (fun e => (m (b.width.base+e.val)).val) cash box core (fun i=>actual b.stock m (ci i))
    center (fun j=>actual b.reserved m (cj j)) (fun j=>actual b.used m (cj j))
    within ordinary central prepaid paid
  have width (e : Fin edges) := reported_width b src m enum ci cj geo e fit bound space (room e)
  simpa only [width] using bill

end Hierarchy.ProtocolRAM.RouteSettlement

end
end OAI
