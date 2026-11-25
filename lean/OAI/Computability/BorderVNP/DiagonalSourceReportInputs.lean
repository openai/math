import OAI.Computability.BorderVNP.DiagonalSourceReportVisit
import OAI.Computability.BorderVNP.DiagonalSourceReturnedInputs

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The fitted source tape and sparse inputs on a decoded preparation -/

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

set_option maxHeartbeats 170000
set_option maxRecDepth 6500

/-- At the inverse of the actual source equivalence the scanner on the
source rows chooses exactly the supplied tape. The fitted argument launcher
starts at this same native report return. -/
theorem PreparationFrame.sourceEquiv_report_cut (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) (u : Fin (R+1)) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let a : Matching ar owners decl raw.val := ⟨q.val.val,q.val.property,rfl⟩
    let checked : Subtype (B raw).pins := ⟨a,(agree.pins raw a).mpr q.property⟩
    let data := (B raw).localRows checked u
    let v := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    Nonempty (ReportArgumentCut v.reports (reports u) data.cursor data.description) := by
  intro full raw a checked data v
  let ctl := (((B raw).paths a).returns.mpr checked.property).some u
  have h := F.sourceEquiv_report_visits fixed S B agree q reports u
  exact ⟨data.observedCut ctl (agree.cells raw checked u) (reports u) v.reports
    (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2.1) h)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
