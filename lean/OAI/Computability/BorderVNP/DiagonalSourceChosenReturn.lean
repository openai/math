import OAI.Computability.BorderVNP.DiagonalSourceReportReconstruction

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The routed physical return selected by a particular joint report proposal -/

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

set_option maxHeartbeats 550000
set_option maxRecDepth 6500

local notation3 (prettyPrint := false) "chosenAt(" packet "," ok ")" =>
  (pinnedMatchingEquiv ar owners decl (fun word => (B word).pins)).symm ⟨(packet).val,ok⟩

private theorem changeInputIndex {I X : Type*} {V W : I → Type*} (start : X ≃ Sigma V)
    (localEquiv : ∀ i, V i ≃ W i) (i j : I) (a : W i) (b : W j) (h : Sigma.mk i a=Sigma.mk j b) :
    start.symm ⟨i,(localEquiv i).symm a⟩=start.symm ⟨j,(localEquiv j).symm b⟩ :=
  congrArg (fun packet : Sigma W => start.symm ⟨packet.1,(localEquiv packet.1).symm packet.2⟩) h

/-- A declared proposal reconstructs the particular shipped router and the
matching owned/local input continuation for every team. The equality retains
the whole source run, including its registers and memory. -/
theorem PreparationFrame.sourceEquiv_chosen_return (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) :
    let raw := declaredWords ar owners decl q.val
    let a : Matching ar owners decl raw.val := ⟨q.val.val,q.val.property,rfl⟩
    let checked : Subtype (B raw).pins := ⟨a,(agree.pins raw a).mpr q.property⟩
    let rs := fun t => (agree.cells raw checked t).equiv.symm (reports t)
    let z := F.replay fixed raw
    let inputs := (F.reportInputEquiv fixed B raw).symm ⟨checked,rs⟩
    (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩ =
      ⟨z.1,fun t => (fixedScheduleEquiv id (F.schedule z.1 t) (F.empty z.1 t)) ⟨z.2 t,inputs t⟩⟩ := by
  intro raw a checked rs z inputs
  let pn : PinnedDeclared ar owners decl (fun raw => (B raw).pins) := ⟨q.val,checked.property⟩
  have s0 := F.sourceEquiv_return_reports fixed S B agree q reports
  have s1 := F.returnEquiv_input fixed B pn rs
  have s2 := F.preparedRawEquiv_rebuilt (id:=id) fixed raw inputs
  dsimp only [pn,rs,inputs,raw,a,checked] at s0 s1 s2
  with_reducible_and_instances have firstTwo := s0.trans s1
  let named := (pinnedMatchingEquiv ar owners decl (fun word => (B word).pins)).symm pn
  let original : Σ word, F.LocalSelections fixed B word := ⟨named.1,named.2,rs⟩
  let current : Σ word, F.LocalSelections fixed B word := ⟨raw,checked,rs⟩
  have name_eq : original=current := by rfl
  let leftData : F.LocalSelections fixed B (chosenAt(q,checked.property)).1 := ⟨(chosenAt(q,checked.property)).2,rs⟩
  have state_eq := changeInputIndex (V:=fun word => F.RoutedInputs (id:=id) fixed word)
      (W:=fun word => F.LocalSelections fixed B word) (F.preparedRawEquiv (id:=id) fixed)
      (fun word => F.reportInputEquiv fixed B word) (chosenAt(q,checked.property)).1 raw leftData ⟨checked,rs⟩ name_eq
  dsimp only [leftData,pn,rs,raw,a,checked] at state_eq
  with_reducible_and_instances have currentState := firstTwo.trans state_eq
  with_reducible_and_instances have fullEq := currentState.trans s2
  dsimp only [z,inputs,rs,checked,a,raw]
  with_reducible_and_instances exact fullEq

end TeamContraction

end BorderVNP
end Computability
end OAI
