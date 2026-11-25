import OAI.Computability.BorderVNP.DiagonalSourceReportFrame

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Chronological rows of the physical source inverse -/

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


private theorem orderedInverse {I X Y : Type*} {V W : I → Type*} (all : X ≃ Y) (start : X ≃ Sigma V)
    (localEquiv : ∀ i, V i ≃ W i) (sort : Sigma W ≃ Y)
    (decomposed : all=start.trans ((Equiv.sigmaCongrRight localEquiv).trans sort)) (y : Y) (i : I) (w : W i)
    (picked : sort.symm y=⟨i,w⟩) :
    all.symm y=start.symm ⟨i,(localEquiv i).symm w⟩ := by
  subst all
  exact congrArg (fun pair => start.symm ((Equiv.sigmaCongrRight localEquiv).symm pair)) picked

local notation3 (prettyPrint := false) "reportPins" => fun raw : SharedWords ar decl => (B raw).pins
local notation3 (prettyPrint := false) "assignedCharts" => fun (raw : SharedWords ar decl) (c : Subtype (B raw).pins)
  (u : Fin (R+1)) => ((B raw).localRows c u).layout
local notation3 (prettyPrint := false) "assignedCells" => fun (raw : SharedWords ar decl) (c : Subtype (B raw).pins)
  (u : Fin (R+1)) => ((B raw).localRows c u).cells
local notation3 (prettyPrint := false) "allSorted" => jointRowReportsEquiv ar owners decl reportPins assignedCharts assignedCells
local notation3 (prettyPrint := false) "inputsOf(" p ")" => (pinnedMatchingEquiv ar owners decl reportPins).symm p

/-- Taking the inverse at the declared row cut recovers the unique native
word table together with its selected owned and local returns. -/
theorem PreparationFrame.returnEquiv_input (pn : PinnedDeclared ar owners decl (fun raw => (B raw).pins))
    (rs : let x := (pinnedMatchingEquiv ar owners decl (fun raw => (B raw).pins)).symm pn
      (u : Fin (R+1)) → ReportAssignments ((B x.1).localRows x.2 u).cells) :
    let x := (pinnedMatchingEquiv ar owners decl (fun raw => (B raw).pins)).symm pn
    (F.returnEquiv fixed id owners B).symm ⟨pn,rs⟩ =
      (F.preparedRawEquiv (id:=id) fixed).symm ⟨x.1,(F.reportInputEquiv fixed B x.1).symm ⟨x.2,rs⟩⟩ := by
  have shapeProof := F.returnEquiv_decomposition fixed B
  have sorted := jointRowReportsEquiv_rebuilt ar owners decl reportPins assignedCharts assignedCells pn rs
  with_reducible_and_instances
    have actual := orderedInverse (V:=F.RoutedInputs (id:=id) fixed) (W:=F.LocalSelections fixed B)
      (F.returnEquiv fixed id owners B) (F.preparedRawEquiv (id:=id) fixed) (fun raw => F.reportInputEquiv fixed B raw)
      allSorted shapeProof ⟨pn,rs⟩ (inputsOf(pn)).1 ⟨(inputsOf(pn)).2,rs⟩ sorted
  dsimp only at actual ⊢
  with_reducible_and_instances exact actual

end TeamContraction

end BorderVNP
end Computability
end OAI
