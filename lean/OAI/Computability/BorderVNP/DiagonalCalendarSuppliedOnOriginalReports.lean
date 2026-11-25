import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedAtRoutes

/-! # Native sources for the original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

private def issuerOnOriginalReports (build : Expr → MetaM Expr) : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun _ calibrated => do
    let issuer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSuppliedAtRoutes) calibrated
    build issuer

local elab "originalReportIssuerType%" : term => do inferType (← issuerOnOriginalReports pure)

/-- The calibrated packet assembler and both source maps for the given original reports. -/
noncomputable abbrev SignedCalendarAt.OriginalReportPacketIssuer : Type _ := originalReportIssuerType%

/-- Assemble both the observed native source and its retained owner/placement
evidence using the same pre-call fields of the route certified by the original reports. -/
noncomputable def SignedCalendarAt.suppliedOnOriginalReports : SignedCalendarAt.OriginalReportPacketIssuer := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← issuerOnOriginalReports pure)
    Lean.Elab.Tactic.replaceMainGoal []

private def sourceOfPacket : MetaM Expr :=
  issuerOnOriginalReports fun issuer => do
    forallBoundedTelescope (← inferType issuer) (some 1) fun packets _ => do
      let acquired := mkProj ``Prod 0 (mkAppN issuer packets)
      forallBoundedTelescope (← inferType acquired) (some 1) fun fields _ => do
        let original := mkAppN packets[0]! fields
        let sources := mkProj ``Sigma 0 (mkAppN acquired fields)
        forallBoundedTelescope (← inferType sources) (some 1) fun teams _ => do
          let fromHistory := mkAppN sources teams
          let fromSite := mkProj ``Sigma 0 (mkAppN original teams)
          let equality ← mkEq fromHistory fromSite
          let kernelProof := mkApp2 (mkConst ``id [.zero]) equality (← mkEqRefl fromHistory)
          mkLambdaFVars (packets ++ fields ++ teams) kernelProof

local elab "originalReportSourceEq%" : term => do inferType (← sourceOfPacket)

/-- The identity between the acquired source and the per-team native packet on the same original field. -/
abbrev SignedCalendarAt.OriginalReportNativeIdentity : Prop := originalReportSourceEq%

/-- On each original field and team, the source used by the calibrated acquisition
is definitionally the native source in the very same physical packet. -/
theorem SignedCalendarAt.suppliedOnOriginalReports_native : SignedCalendarAt.OriginalReportNativeIdentity := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← sourceOfPacket)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
