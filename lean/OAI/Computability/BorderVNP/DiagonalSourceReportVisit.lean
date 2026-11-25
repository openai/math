import OAI.Computability.BorderVNP.DiagonalReturnedVisitTail
import OAI.Computability.BorderVNP.DiagonalSourceChosenReturn

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The three chronological local calls on a reconstructed source report -/

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
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

set_option maxHeartbeats 420000
set_option maxRecDepth 6500

/-- For arbitrary report guesses the actual source equivalence returns that
same report on the previously reconstructed control state and then runs the
typed argument program on its particular output. No equality of field values
or validity test of the private cells is used. -/
theorem PreparationFrame.sourceEquiv_report_visits (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) (u : Fin (R+1)) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let a : Matching ar owners decl raw.val := ⟨q.val.val,q.val.property,rfl⟩
    let checked : Subtype (B raw).pins := ⟨a,(agree.pins raw a).mpr q.property⟩
    let ctl := (((B raw).paths a).returns.mpr checked.property).some u
    let data := (B raw).localRows checked u
    let bits := ((agree.cells raw checked u).equiv).symm (reports u)
    let report := assignedReportReturnEquiv (data.seed ctl) (mac full.1 u) ctl.val.2.1 bits
    let args := (arguments_returns (data.argumentsFit ctl bits)).some
    let v := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    (v.controls.val,v.reports.val,v.arguments.val)=(ctl.val,report.val,args.val) := by
  intro full raw a checked ctl data bits report args v
  let physical := (B raw).owned.symm a
  let z := F.replay fixed raw
  let rs := fun t => (agree.cells raw checked t).equiv.symm (reports t)
  let inputs := (F.reportInputEquiv fixed B raw).symm ⟨checked,rs⟩
  have fullEq := F.sourceEquiv_chosen_return fixed S B agree q reports
  have last := nativeOwnedReportEquiv_rebuilt ar owners decl raw.val id (pub z.1) (mac z.1)
    (fun t => (z.2 t).val.2.1) (fun t => (z.2 t).val.2.2) (B raw).constants (B raw).owned (B raw).pins
    (B raw).controlsAt (B raw).paths (B raw).localRows checked rs u
  let tail := (fittedReportTailEquiv ctl (data.seed ctl) (data.argumentsFit ctl)).symm bits
  have localInput : inputs u=(inputCut id (pub z.1 u) (mac z.1 u) ((B raw).constants u)).symm
      ⟨physical u,tail⟩ := last
  with_reducible_and_instances
    have assembled := returned_report_visits id pub mac reg mem z.1 (F.schedule z.1) (F.empty z.1)
      z.2 inputs full fullEq u ((B raw).constants u) (physical u) ctl data bits localInput
  dsimp only [v,report,args]
  with_reducible_and_instances exact assembled

end TeamContraction

end BorderVNP
end Computability
end OAI
