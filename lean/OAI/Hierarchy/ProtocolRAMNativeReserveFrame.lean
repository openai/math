import OAI.Hierarchy.ProtocolRAMNativeReserveSink

namespace OAI
/-! # Preserving the original decision word through the native route reporter -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe
open scoped Fin.CommRing Classical
noncomputable section
variable {w r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

omit [Fintype I] [Fintype J] in
theorem Sink.frame (f : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (x : ℕ) (stock : x<f.banks.width.base) (table : x<f.table)
    (dest : x<f.destination) (size : f.banks.width.base+edges≤f.source) :
    f.output m e ci cj x=m x := by
  have later : x<f.destination+3*edges := by omega
  have last : x<f.destination+6*edges := by omega
  simp only [output,finalMemory,ProtocolRAMEmit.emitted,fillSegment,not_le.mpr dest,not_le.mpr later,
    not_le.mpr last,false_and,ite_false,result,report,Pass.apply,image,not_le.mpr table]
  exact RouteSettlement.output_below f.banks f.source m e ci cj x stock size

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
