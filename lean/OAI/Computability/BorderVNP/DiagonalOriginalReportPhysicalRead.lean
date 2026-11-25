import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalOriginalOwnersAtEmission
import OAI.Computability.BorderVNP.DiagonalRegisteredDeclaredOwnerRead
import OAI.Computability.BorderVNP.DiagonalRegisteredFundedRead

/-! # Funding a cell report with its returned allocation and owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyCellReports

private theorem reportedOwnerRows {a : CubeArena.Layout} {R : ℕ}
    {packetOwner residentOwner : (Packet a.n a.header.d a.header.blocks → Cube.Selector a.n a.K a.h) →
      Fin a.header.d → Fin (R+1)}
    {packetLabel residentLabel : Fin a.cells → Label (a.n+1) a.header.d}
    {packet : Routed (b:=a.b) (s:=a.s) packetOwner}
    {resident : Routed (b:=a.b) (s:=a.s) residentOwner} {read : Fin a.cells → ℕ}
    (words : routedOwnerWord a packetOwner packetLabel packet = routedOwnerWord a residentOwner residentLabel resident)
    (returned : ∀ c, read c = (residentOwner resident.1 (residentLabel c (chosen a.b a.s resident.1))).val) :
    ∀ c, read c = (packetOwner packet.1 (packetLabel c (chosen a.b a.s packet.1))).val := by
  intro c
  apply (returned c).trans
  simpa only [routedOwnerWord, dite_eq_left c.isLt] using (congrFun words c.val).symm

/-- The physical seed and allocation of precisely the cells reported by this return. -/
def attainedOriginalReportOperands (prepared : Expr) : TermElabM (Expr × Expr) := withoutErrToSorry do
  let checked := mkProj ``And 0 prepared
  let agreement ← exprToSyntax (mkProj ``And 1 prepared)
  let source ← exprToSyntax (mkProj ``And 0 checked)
  let bank ← exprToSyntax (mkProj ``And 1 checked)
  let seed ← elabTerm (← `(SameReportCells.source_seed $agreement $source)) none
  let allocation ← elabTerm (← `(SameReportCells.source_allocation $agreement $bank)) none
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars seed, ← instantiateMVars allocation)

private def recordedArgument (app : Expr) (key : Name) : MetaM Expr := do
  let ci ← getConstInfo app.getAppFn.constName!
  forallBoundedTelescope ci.type (some app.getAppNumArgs) fun formals _ => do
    let some i ← formals.findIdxM? (fun x => return (← x.fvarId!.getUserName) == key)
      | throwError "missing original return field {key}"
    return app.getAppArgs[i]!

private def bankEquality (op : Expr) (key : Name) : MetaM Expr := do
  let next ← whnf (← inferType op)
  unless next.isForall && next.bindingName! == key do throwError "missing original bank field {key}"
  let some eq ← whnfUntil next.bindingDomain! ``Eq | throwError "expected original bank address equality"
  return mkApp op (← mkEqRefl eq.getAppArgs[1]!)

/-- Apply the previously funded reader through its original seed, cell allocation,
signed owner word, first address and stride. The remaining arguments start at
the physical cable rows for this particular sparse emission. -/
def physicalReadOnOriginalReport (funded field team actual attended selected ownerWord seed allocation
    marker fit cells emission : Expr) : TermElabM Expr := withoutErrToSorry do
  let f ← exprToSyntax field
  let u ← exprToSyntax team
  let src ← exprToSyntax seed
  let alloc ← exprToSyntax allocation
  let marked ← exprToSyntax marker
  let paid ← exprToSyntax funded
  let earned ← elabTerm (← `(registeredFundedRead% $paid $f $u $alloc $marked)) none
  let some stamp ← whnfUntil (← inferType attended) ``Eq | throwError "expected the actual original routed owner visit"
  let some visits ← whnfUntil stamp.getAppArgs[1]! ``PinStart.ownedVisits | throwError "missing original owned visit"
  let id ← exprToSyntax (← recordedArgument visits `id)
  let starts ← exprToSyntax (← recordedArgument visits `S)
  let active ← exprToSyntax (← recordedArgument visits `p)
  let run ← elabTerm (← `(PinStart.visits $id $starts (u:=$u) ($active $u))) none
  synthesizeSyntheticMVarsNoPostponing
  let run ← instantiateMVars run
  let controls ← exprToSyntax (← mkProjection run `controls)
  let reports ← exprToSyntax (← mkProjection run `reports)
  let some same ← whnfUntil (← inferType ownerWord) ``Eq | throwError "expected the two original owner words"
  let some written ← whnfUntil same.getAppArgs.back! ``routedOwnerWord | throwError "missing the returned owner"
  let native ← exprToSyntax written.getAppArgs.back!
  let C ← exprToSyntax actual
  let chosen ← exprToSyntax selected
  let declared ← exprToSyntax (← mkProjection actual `declared)
  let numbers ← elabTerm (← `(registeredOwnerWords% $chosen on $native matching $declared)) none
  synthesizeSyntheticMVarsNoPostponing
  let numbers ← exprToSyntax (← instantiateMVars numbers)
  let e ← exprToSyntax emission
  let returned ← elabTerm (← `(originalOwnersAtEmission% $C $numbers $u $controls $reports $src $alloc $e)) none
  synthesizeSyntheticMVarsNoPostponing
  let read ← mkAppM ``reportedOwnerRows #[ownerWord, ← instantiateMVars returned]
  let original := mkAppN (← instantiateMVars earned) #[seed, allocation, fit, ← mkEqSymm cells, emission, read]
  bankEquality (← bankEquality original `bankStart) `stride

end Diagonal

end BorderVNP
end Computability
end OAI
