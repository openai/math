import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationAtNativeNext
import OAI.Computability.BorderVNP.DiagonalProducedRoster

/-! # The roster requested by an original calendar registration

The argument visitor returns its private-call input after traversing the
original team's report prefix. The roster uses that input, the published
argument readings, and the control rows of the same team. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator
open Cube.Physical.NativeLedger CellMacro.Generator CompactMachine
open Packing.RoutingOutputs

/-- A produced roster for the actual visit preceding the private calls. -/
def OriginalPrefixRoster {n w : ℕ} (arena : SignedTaskArena.Layout) (t : Fin arena.cube.teams)
    (team : PositiveTeam arena.id SparseExterior.driver n w) (prefixRun : team.Prefix)
    (origin cables cells entries ports : ℕ) : Prop :=
  let visited := prefixVisits team prefixRun
  let stages := (ScheduleClock.argumentVisitsEquiv team.pub (install SparseExterior.driver n team.routines)
    visited.reports.val.2.1 visited.reports.val.2.2).symm visited.arguments
  let table := bases origin cables cells entries
  let control := controlsBase origin cables cells entries ports
  ∃ (Orig : Type) (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ)
    (extras : ℕ → List CellSparse.Record)
    (source : ScheduleClock.SparseCallInput team.pub stages.2.1.val.2.2),
    ScheduleClock.ProducedRoster arena
      (arena.controlRows t.val (team.pub 0).val table.ends control table.livePairs ports)
      (readings stages.1.val.2.2) patch locations extras source

private def nativeRoster (result : Expr) : MetaM Expr := do
  let some native ← whnfUntil result ``OriginalPrefixRun | throwError "expected an original prefix run"
  let mut type := (← getConstInfo ``OriginalPrefixRun).type
  let mut args : NameMap Expr := {}
  for arg in native.getAppArgs do
    args := args.insert type.bindingName! arg
    type := type.bindingBody!
  let arg := fun name => args.find? name |>.getDM (throwError "missing original prefix parameter {name}")
  let some control ← whnfUntil (← arg `control) ``controlsBase
    | throwError "expected the original published control layout"
  let prefixArgs ← #[`n, `w, `sa, `t, `u, `pr].mapM arg
  return mkAppN (mkConst ``OriginalPrefixRoster) (prefixArgs ++ control.getAppArgs)

local elab "originalRegisteredRoster%" : term => do
  let op ← mkConstWithLevelParams ``SignedCalendarAt.frozenRegistrationAtNativeNext
  forallTelescopeReducing (← inferType op) fun parameters _ => do
    let registrar := mkAppN op parameters
    let registrations := mkProj ``TeamContraction.ProcessorSlots.BootedPinStart.OriginalReportRule 0 registrar
    forallBoundedTelescope registrations (some 3) (whnfType := true) fun coordinates goal => do
      let some registered ← whnfUntil goal ``TeamContraction.RegisteredOriginalPrefix
        | throwError "expected the registration of an original report, subtotal, and team"
      let request ← nativeRoster registered.getAppArgs.back!
      mkLambdaFVars parameters (← mkForallFVars coordinates request)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
/-- At the given original route, every report proposal, subtotal and team
requires a roster from the private argument stage at its reached prefix. -/
noncomputable def SignedCalendarAt.rostersAtRegisteredSource := originalRegisteredRoster%

end Diagonal

end BorderVNP
end Computability
end OAI
