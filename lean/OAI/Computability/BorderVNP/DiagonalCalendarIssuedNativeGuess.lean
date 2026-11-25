import OAI.Computability.BorderVNP.DiagonalCalendarIssuedBareAt

/-! # The original native guess at each issued tuple and team -/

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
set_option maxHeartbeats 800000 in
/-- The exposed local guess is the decoding of the original full pin on this team. -/
def PreparedHistoryDecoder.OriginalNativeGuesses : Prop :=
  ∀ (f : _) (u : Fin (R+1)),
    (((decoder.bareAtRoutes limit burst privateSize core roster taskBase routed f).2 u).1) =
      (G.jointGuess (fun i => (args i).ibase) (fun i => (args i).hbase) (fun i => (args i).starbase)).symm f.1 u

/-- Every team initially reads its own part of the source pin. This holds before applying a private report or accepted predicate. -/
theorem PreparedHistoryDecoder.guessAtRoster :
    decoder.OriginalNativeGuesses limit burst privateSize core roster taskBase routed := by
  intro f u
  rfl

end TeamContraction.ProcessorSlots.BootedPinStart

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

private def originalGuessSelection : MetaM Expr := do
  let .defnInfo issuing ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calibrated issuing routes"
  forallTelescope issuing.value fun inputs family => do
    let some source ← whnfUntil family ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the actual field and report roster"
    let route := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) inputs
    let read ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.guessAtRoster
    mkLambdaFVars inputs (mkAppN read (source.getAppArgs.push route))

local elab "selectedGuessStatement%" : term => do inferType (← originalGuessSelection)

/-- The original field's restored native digits, at all actual calibration parameters. -/
abbrev SignedCalendarAt.FrozenOriginalGuesses : Prop := selectedGuessStatement%

/-- Each team's guess in the original issued preparation is the corresponding
part of the full pin in that same issued field. -/
theorem SignedCalendarAt.issuedOriginalGuessOfCandidates : SignedCalendarAt.FrozenOriginalGuesses := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalGuessSelection)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
