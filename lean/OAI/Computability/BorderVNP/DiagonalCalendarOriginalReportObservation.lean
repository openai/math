import OAI.Computability.BorderVNP.DiagonalSelectedAdmittedFrameObservation
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHistory
import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame

/-! # The original report cut on the admitted calendar route

The checked calendar routing map fixes the history, private source and table
indices. We instantiate the admitted-frame cut with that map's literal
arguments. In particular each recovered report and each row-range check comes
from the same routed input. Keeping the shared arguments also avoids expanding
the entire frozen decoder at each application of the observer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term
open TeamContraction TeamContraction.ProcessorSlots PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

/-- Pair each argument of the admitted route with its original binder. The
route is applied to two extra arguments, its selected frames and row checks. -/
private def actualArgs (c : Expr) : MetaM (Array (Name × Expr)) := do
  let some n := c.getAppFn.constName? | throwError "expected a calibration declaration"
  let mut t := (← getConstInfo n).type
  let mut xs := #[]
  for x in c.getAppArgs do
    if !t.isForall then break
    xs := xs.push (t.bindingName!,x)
    t := t.bindingBody!.instantiate1 x
  return xs

private def param (args : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let some a := args.toList.lookup key | throwError "missing {key}"
  return a

private def calApp (p : Expr) (n : Name) : MetaM Expr := do
  let some a ← whnfUntil p n | throwError "expected {n}"
  return a

private def cutoff (args : Array (Name × Expr)) (key : Name) : MetaM (Array Expr) := do
  let some ix := args.findIdx? (fun a => a.1 == key) | throwError "missing endpoint {key}"
  return (args.extract 0 (ix+1)).map Prod.snd

/-- Both the startup frame and the physical output origin are constant on
the physical team index. -/
private def constantBody (fn : Expr) : MetaM Expr := do
  lambdaTelescope (← instantiateMVars fn) fun _ body => pure body

/-- Recover the numerical model from the existing admitted implementation.
The final input binders of the calendar route are the raw pin, history and
subtotal. The observed theorem also takes the route, proposal and team. -/
private def buildFrozenCut : TermElabM Expr := do
  let route ← mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs
  forallTelescope (← inferType route) fun xs _ => do
    let calWidth ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
    let some ix := calWidth | throwError "missing matrices"
    let external := xs.extract (xs.size-3) xs.size
    let original := xs.extract 0 (xs.size-3)
    let cargs := xs.extract 0 ix
    let applied ← calApp (mkAppN route xs) ``signedAdmittedRouting
    let args ← actualArgs applied
    let point := applied.getAppArgs
    -- These are the actual arguments of the returned admitted preparation.
    let frames := point[point.size-2]!
    let passed := point.back!
    let fArgs ← actualArgs (← calApp (← inferType frames) ``AdmittedPinnedFrames)
    let align := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites_frames) cargs
    let frameBase ← constantBody (← inferType align).getAppArgs.back!
    let outputBase ← constantBody (← param args `origin)
    let get := param args
    let lam := mkLambdaFVars external
    let decoder := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedHistoryDecoder)
      ((xs.extract 0 (ix+1)).push (← get `readerPin))
    let sites := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites) cargs
    let limit ← mkAppM ``Fin.val #[← mkAppM ``SiteData.limit #[sites]]
    let burst ← mkAppM ``Fin.val #[← mkAppM ``SiteData.burst #[sites]]
    let room := mkApp (mkConst ``Nat.le_refl) burst
    -- The honest broadcast lemma takes the history just after its lower
    -- bound hypothesis. All remaining static arguments agree with the route.
    let mut hs := (← cutoff args `hp).push external[1]!
    let bound ← cutoff args `profileBits
    let hp ← cutoff args `hp
    hs := hs ++ bound.extract hp.size bound.size
    let honest := mkAppN (← mkConstWithLevelParams ``signedBroadcastAllowed_honest) (hs.push (← get `admitted))
    let mid ← #[`clockWidth,`tallyWidth,`pub,`reg,`args,`readerPin,`layout,`fixed,`hw,`agreeWidth,`base,`hdr,`room,`enc,`B₀].mapM (fun k => liftM (get k))
    -- Reuse the actual frames and their survived checks at every original
    -- pin, decoded history and subtotal before supplying the measured clock.
    let inputs := bound ++ #[frameBase,outputBase,← get `frame] ++ mid ++
      #[← lam (← param fArgs `allowed),← lam (← get `template),← lam (← get `entries),
        ← lam frames,← lam passed,← lam honest,decoder,limit,burst,room]
    let partialRead := mkAppN (← mkConstWithLevelParams ``signedAdmittedCutAtOriginalFrame) inputs
    forallBoundedTelescope (← inferType partialRead) (some 1) fun next _ => do
      let reader := mkAppN partialRead (next.push align)
      forallTelescope (← inferType reader) fun point' _ => do
        let read := mkAppN reader point'
        let ty ← inferType read
        let down := mkApp2 (mkConst ``PLift.down [Level.zero]) ty.getAppArgs.back! read
        mkLambdaFVars (original ++ next ++ point') down

open Lean.Elab.Command in
run_cmd liftTermElabM do
  let proof ← buildFrozenCut
  let type ← inferType proof
  -- Give the complete quantified statement a name. This keeps the theorem
  -- signature small while its proposition unfolds to the original cut.
  let claim := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.OriginalReportObservation
  addDecl (.defnDecl {
    name := claim
    levelParams := []
    type := mkSort .zero
    value := type
    hints := .abbrev
    safety := .safe })
  addDocStringCore claim "The original admitted route has a physical scanner cut at every calendar input, private report, subtotal and team."
  let n := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.frozenOriginalReportObservation
  addDecl (.thmDecl { name:=n, levelParams:=[], type:=mkConst claim, value:=proof })
  addDocStringCore n "The original team report scanner has a physical cursor, descriptor, and argument cut for each admitted calendar route and proposed source assignment."

end Diagonal

end BorderVNP
end Computability
end OAI
