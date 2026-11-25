import OAI.Computability.BorderVNP.DiagonalNativeReportReconstruction
import OAI.Computability.BorderVNP.DiagonalSourceOwnedVisit

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The three chronological local calls on a reconstructed source report -/

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (S : SourceReports ar owners) (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (B : F.Builders fixed id owners)

set_option maxHeartbeats 800000
set_option maxRecDepth 6500


/-- The physical source inverse reconstructs its local preparation by
passing each chosen report to its own physical assignment on the same pinned packet. -/
theorem PreparationFrame.sourceEquiv_return_reports (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let a : Matching ar owners decl raw.val := ⟨q.val.val,q.val.property,rfl⟩
    let checked : Subtype (B raw).pins := ⟨a,(agree.pins raw a).mpr q.property⟩
    let pin : PinnedDeclared ar owners decl (fun raw => (B raw).pins) := ⟨q.val,checked.property⟩
    let input := (F.returnEquiv fixed id owners B).symm ⟨pin,fun t =>
      (agree.cells raw checked t).equiv.symm (reports t)⟩
    full=input := by
  intro full raw a checked pin input
  apply congrArg (F.returnEquiv fixed id owners B).symm
  rfl

/-- The remainder of the native computation at the exact state of the
shared router replay. Both cuts use this same dependent family. -/
abbrev PreparationFrame.RoutedInputs (raw : SharedWords ar decl) :=
  let z := F.replay fixed raw
  (u : Fin (R+1)) → Returns (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s))
    (pub z.1 u) (mac z.1 u) (z.2 u).val.2.1 (z.2 u).val.2.2

/-- All reports on one physically compatible assignment of the shared words. -/
abbrev PreparationFrame.LocalSelections (raw : SharedWords ar decl) :=
  Σ c : Subtype (B raw).pins, (u : Fin (R+1)) → ReportAssignments ((B raw).localRows c u).cells

/-- The joint equivalence at the routing cut, before the per-team scalar
constants, owned scans, report traversals and typed argument calls. -/
noncomputable def PreparationFrame.preparedRawEquiv :
    (Σ x : HeaderExterior L header, (u : Fin (R+1)) → Returns
      (prepareExpansion epochPlacement (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h))
        (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s)))
      (pub x u) (mac x u) (reg x u) (mem x u)) ≃
    Σ raw : SharedWords ar decl, F.RoutedInputs (id:=id) fixed raw :=
  exteriorPreparedEquiv G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement F.guess F.rows decl fixed header
    F.length id pub mac reg mem F.schedule F.empty F.initialized F.copies F.emitted F.fitted F.records F.count
    F.dataCount F.room F.frame

/-- The remaining joint input returns after the physical router replay. -/
noncomputable def PreparationFrame.reportInputEquiv (raw : SharedWords ar decl) :
    F.RoutedInputs (id:=id) fixed raw ≃ F.LocalSelections fixed B raw :=
  let z := F.replay fixed raw
  nativeOwnedReportEquiv ar owners decl raw.val id (pub z.1) (mac z.1) (fun u => (z.2 u).val.2.1)
    (fun u => (z.2 u).val.2.2) (B raw).constants (B raw).owned (B raw).pins (B raw).controlsAt
    (B raw).paths (B raw).localRows

/-- Separate the routing, local report and global indexing equivalences
before using any concrete RAM return as their argument. -/
theorem PreparationFrame.returnEquiv_decomposition :
    let pins := fun raw => (B raw).pins
    let rows := jointRowReportsEquiv ar owners decl pins (fun raw q u => ((B raw).localRows q u).layout)
      (fun raw q u => ((B raw).localRows q u).cells)
    F.returnEquiv fixed id owners B = (F.preparedRawEquiv (id:=id) fixed).trans
      ((Equiv.sigmaCongrRight (fun raw => F.reportInputEquiv fixed B raw)).trans rows) := by
  unfold PreparationFrame.returnEquiv nativePreparedReportEquiv PreparationFrame.preparedRawEquiv
    PreparationFrame.reportInputEquiv
  rfl

/-- The simulator's original schedule and routed return are concatenated
with precisely the selected post-routing continuation on each team. -/
theorem PreparationFrame.preparedRawEquiv_rebuilt (raw : SharedWords ar decl)
    (inputs : let z := F.replay fixed raw
      (u : Fin (R+1)) → Returns (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s))
        (pub z.1 u) (mac z.1 u) (z.2 u).val.2.1 (z.2 u).val.2.2) :
    let z := F.replay fixed raw
    (F.preparedRawEquiv (id:=id) fixed).symm ⟨raw,inputs⟩ =
      ⟨z.1,fun u => (fixedScheduleEquiv id (F.schedule z.1 u) (F.empty z.1 u)) ⟨z.2 u,inputs u⟩⟩ := by
  unfold PreparationFrame.preparedRawEquiv exteriorPreparedEquiv
  rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
