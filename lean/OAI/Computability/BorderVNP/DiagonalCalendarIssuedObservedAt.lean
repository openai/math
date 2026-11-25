import OAI.Computability.BorderVNP.DiagonalIssuedObservedFields
import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes

/-! # The observed header of every issued calendar field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (privateSize : TeamScales.width n (1/2) ≤ burst)

open Crossing Packing.Inherited Packing.BottomReports Cube.Physical Cube.Physical.NativeAssignments
open DiagonalTallyCellReports RoutingISA.CompactMachine
variable {D nativeGroups : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Hist → Network D P bits} {count : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) axes nativeGroups (count h) box lanes selectors R)

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
    (roster : SourceRoster core d symbols) (taskBase : ℕ)

variable (routed : decoder.RosterRoutes limit burst privateSize core roster taskBase)

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- At every exterior block the roster inverse observes the header of its own issued
field, including its original declaration and proposed subtotals. -/
def PreparedHistoryDecoder.ObservedAtRoutes : Prop :=
  ∀ (f : _) (cut : Block (R+1)),
    JointHeader.observed L (routedBareTuple routed f).1.val cut = (issuedHeader routed f).bits

/-- The original header observation on this native roster. -/
theorem PreparedHistoryDecoder.observedAtRoster :
    decoder.ObservedAtRoutes limit burst privateSize core roster taskBase routed :=
  fun f cut => routedBareTuple.observed routed f cut

end TeamContraction.ProcessorSlots.BootedPinStart

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

private def observationOnSelectedRoutes : MetaM Expr := do
  let .defnInfo declaration ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calibrated family of issuing routes"
  forallTelescope declaration.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the selected source roster"
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let observation ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.observedAtRoster
    mkLambdaFVars parameters (mkAppN observation (roster.getAppArgs.push routed))

local elab "selectedHeaderObservationType%" : term => do
  inferType (← observationOnSelectedRoutes)

/-- The header assertion on all original inputs of the calibrated routing family. -/
abbrev SignedCalendarAt.FrozenObservedHeaders : Prop := selectedHeaderObservationType%

/-- The selected exterior sees the issued header at every cut on every prepared field. -/
theorem SignedCalendarAt.issuedObservedAtOfCandidates : SignedCalendarAt.FrozenObservedHeaders := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← observationOnSelectedRoutes)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
