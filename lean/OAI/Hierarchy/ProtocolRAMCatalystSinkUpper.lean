import OAI.Hierarchy.ProtocolRAMCalendarSettlement

namespace OAI
/-! # The physical terminal sink retains every higher private word -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w n r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

omit [Fintype I] [Fintype J] in
theorem RouteSettlement.output_above (b : RouteSettlement.Banks) (src : ℕ) (m : Memory w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (x : ℕ)
    (stock : b.width.base+edges≤x) (tape : src+2*r≤x) :
    RouteSettlement.output b src m enum ci cj x=m x := by
  unfold RouteSettlement.output
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by
    intro i
    have bound:=((enum i).edge).isLt
    unfold RouteSettlement.address
    omega)]
  exact ProtocolRAMGeneratedWrite.frame_image src (2*r) (RouteSettlement.words b) m x (Or.inr tape)

theorem emit_above (destination : ℕ) (rows : Fin n→ProtocolRAMEmit.Row) (m : Memory w) (x : ℕ)
    (endAt : destination+9*n≤x) : ProtocolRAMEmit.emitted destination rows m x=m x := by
  have a : ¬(destination≤x ∧ x<destination+3*n):=by omega
  have b : ¬(destination+3*n≤x ∧ x<destination+3*n+3*n):=by omega
  have c : ¬(destination+6*n≤x ∧ x<destination+6*n+3*n):=by omega
  simp only [ProtocolRAMEmit.emitted,fillSegment,ite_eq_right a,ite_eq_right b,ite_eq_right c]

omit [Fintype I] [Fintype J] in
/-- A slot above the written bank, route tape, packed 8-word rows, and
9-word terminal report is invariant through the full actual sink execution. -/
theorem Calendar.Sink.above (s : Calendar.Sink r edges) (m : Memory w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (x : ℕ)
    (bank : s.banks.width.base+edges≤x) (tape : s.source+2*r≤x)
    (packedRows : s.table+8*edges≤x) (emitted : s.destination+9*edges≤x) :
    s.output m enum ci cj x=m x := by
  let settled:=RouteSettlement.output s.banks s.source m enum ci cj
  let fields:=RouteSettlement.fields s.banks s.geometry
  change ProtocolRAMEmit.emitted s.destination (reportedRows [] fields settled)
    ((report s.table edges s.owners fields).apply settled) x=m x
  rw [emit_above _ _ _ _ emitted]
  exact (ProtocolRAMGeneratedWrite.frame_image s.table (8*edges) (packed s.owners fields) settled x (Or.inr packedRows)).trans
    (RouteSettlement.output_above s.banks s.source m enum ci cj x bank tape)

end Hierarchy.ProtocolRAM
end

end OAI
