import OAI.Computability.BorderVNP.DiagonalCalendarOwnerAdmission
import OAI.Computability.BorderVNP.DiagonalOriginalAdmittedObservation
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership

/-! # The writer history and the physical owner return of an original calendar field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube

open Lean Meta
open private argument atHead argumentsOf applyNamed preparedFamilies
  from OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000


set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

/-- Read the route and subtotal from the calendar's actual field. The two component
proofs use its selected preparation and its own checked owner census. -/
private def checkedHistory : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected selected calendar routes"
  forallTelescope shape.value fun parameters selected => do
    let roster ← atHead selected ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
    let native := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let (whole, routes, reports) ← preparedFamilies roster
    let physical ← argumentsOf roster
    let some mv ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the calibrated input matrices"
    withLocalDeclD `f whole fun f => do
      let pin := mkProj ``Sigma 0 f
      let historyAndEntries := mkProj ``Sigma 1 f
      let history := mkProj ``Sigma 0 historyAndEntries
      let entries := mkProj ``Sigma 1 historyAndEntries
      let route := mkProj ``Sigma 0 entries
      let proposal := mkProj ``Sigma 1 entries
      let subtotal := mkProj ``Prod 0 proposal
      let rows := mkProj ``Prod 1 proposal
      let checked := mkAppN parameters.back! #[pin,history,subtotal]
      let frames := mkProj ``CheckedRouteInputs 0 checked
      let passes := mkProj ``CheckedRouteInputs 1 checked
      let common ← argumentsOf (← atHead (← inferType frames) ``AdmittedPinnedFrames)
      let honest := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRouteAllowedForOwner)
        ((parameters.extract 0 (mv+1)).push history)
      let seen ← applyNamed ``AdmittedPinnedFrames.originalObservation
        (#[ (`count,← argument common `entries), (`candidates,frames), (`checked,passes), (`honest,honest), (`q,route), (`reports,rows) ] ++ common)
      let same ← applyNamed ``BootedPinStart.routedBareTuple_owner_observation
        (#[ (`gen,mkConst ``SparseExterior.driver), (`ar,← argument common `ar), (`Route,routes),
            (`Report,reports), (`routed,native), (`f,f) ] ++ physical)
      let atVisit := mkProj ``And 1 same
      let full := mkAppN (mkConst ``And.intro) #[← inferType seen,← inferType atVisit,seen,atVisit]
      mkLambdaFVars (parameters.push f) full

local elab "observedRegisteredWriter%" : term => do inferType (← checkedHistory)

/-- The actual selected writer history and owner scan at any validated source-entry family. -/
abbrev SignedCalendarAt.OriginalWriterHistoryStatement : Prop := observedRegisteredWriter%

/-- Retain the full shared transmission and the original native return for each decoded field. -/
theorem SignedCalendarAt.frozenObservedWriterOnEntries : SignedCalendarAt.OriginalWriterHistoryStatement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← checkedHistory)
    Lean.Elab.Tactic.replaceMainGoal []


/-- Specialize only the source-entry coordinate. All other inputs and the original
field remain those of the actual routed calendar. -/
private def selectedWriterOnEntries : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected calendar's issuing routes"
  forallTelescope shape.value fun parameters _ => do
    let some matrices ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the calendar's matrices"
    let some entries ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `entries)
      | throwError "expected a source-entry family"
    let before := parameters.extract 0 entries
    let counts := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenFrameEntries)
      (parameters.extract 0 (matrices+1))
    let general ← mkConstWithLevelParams ``SignedCalendarAt.frozenObservedWriterOnEntries
    mkLambdaFVars before (mkAppN general (before.push counts))

local elab "observedAtOriginalEntries%" : term => do inferType (← selectedWriterOnEntries)

/-- The writer history and the native owner scan at the calendar's actual entry counts. -/
abbrev SignedCalendarAt.OriginalWriterAtFrameEntries : Prop := observedAtOriginalEntries%

/-- Recover the table, row map, complete writer history, and pin substitution on
the original registered frame, together with the equality to its native owner scan. -/
theorem SignedCalendarAt.frozenObservedWriterOnOriginal : SignedCalendarAt.OriginalWriterAtFrameEntries := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← selectedWriterOnEntries)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
