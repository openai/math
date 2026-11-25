import OAI.Computability.BorderVNP.DiagonalIssuedObservedFields
import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes

/-! # The original bare tuple of every issued calendar field -/

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

private abbrev selectedFunctionType {X : Type*} (_ : X) := X

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- The complete bare exterior and joint native prefix returned by this particular
roster, as a function of an issued field. -/
noncomputable def PreparedHistoryDecoder.OriginalBareAtRoutes : Type _ :=
  selectedFunctionType (routedBareTuple routed)

/-- Read the original bare tuple using the exact routed inverse. -/
noncomputable abbrev PreparedHistoryDecoder.bareAtRoutes :
    decoder.OriginalBareAtRoutes limit burst privateSize core roster taskBase routed :=
  routedBareTuple routed

end TeamContraction.ProcessorSlots.BootedPinStart

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

private def bareOnSelectedRoutes : MetaM Expr := do
  let .defnInfo declaration ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calibrated family of issuing routes"
  forallTelescope declaration.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the selected source roster"
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let native ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.bareAtRoutes
    mkLambdaFVars parameters (mkAppN native (roster.getAppArgs.push routed))

local elab "selectedBareTupleType%" : term => do inferType (← bareOnSelectedRoutes)

/-- The selected roster's physical bare-tuple family on the original calendar. -/
noncomputable abbrev SignedCalendarAt.FrozenOriginalBareTuples : Type _ := selectedBareTupleType%

/-- Return the selected positive exterior and every team's original native preparation
at the issued field. -/
noncomputable abbrev SignedCalendarAt.issuedBareTupleAtOfCandidates : SignedCalendarAt.FrozenOriginalBareTuples := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← bareOnSelectedRoutes)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
